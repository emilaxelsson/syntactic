{-# LANGUAGE UndecidableInstances #-}

-- | Basic optimization of expressions
module Language.Syntactic.Features.Binding.Optimize where



import Control.Monad.Writer
import Data.Set as Set

import Data.Proxy

import Language.Syntactic
import Language.Syntactic.Features.Symbol
import Language.Syntactic.Features.Literal
import Language.Syntactic.Features.Condition
import Language.Syntactic.Features.Tuple
import Language.Syntactic.Features.Binding



-- | Constant folder
--
-- Given an expression and the statically known value of that expression,
-- returns a (possibly) new expression with the same meaning as the original.
-- Typically, the result will be a 'Literal', if the relevant type constraints
-- are satisfied.
type ConstFolder dom = forall a . ASTF dom a -> a -> ASTF dom a

-- | Basic optimization of a feature
class EvalBind dom => Optimize feature ctx dom
  where
    -- | Bottom-up optimization of a feature. The optimization performed is
    -- up to each instance, but the intention is to provide a sensible set of
    -- \"always-appropriate\" optimizations. The default implementation
    -- 'optimizeFeatDefault' does only constant folding. This constant folding
    -- uses the set of free variables to know when it's static evaluation is
    -- possible. Thus it is possible to help constant folding of other features
    -- by pruning away parts of the syntax tree that are known not to be needed.
    -- For example, by replacing (using ordinary Haskell as an example)
    --
    -- > if True then a else b
    --
    -- with @a@, we don't need to report the free variables in @b@. This, in
    -- turn, can lead to more constant folding higher up in the syntax tree.
    optimizeFeat
        :: Proxy ctx
        -> ConstFolder dom
        -> feature a
        -> HList (AST dom) a
        -> Writer (Set VarId) (ASTF dom (EvalResult a))

  -- The reason for having @dom@ as a class parameter is that many instances
  -- require the constraint @(feature :<: dom)@. If @dom@ was forall-quantified
  -- in 'optimizeFeat', this constraint would not be allowed. On the other hand,
  -- it is not possible to add the constraint @(feature :<: dom)@ to
  -- 'optimizeFeat', because the instance for '(:+:)' doesn't satisfy it.

instance (Optimize sub1 ctx dom, Optimize sub2 ctx dom) =>
    Optimize (sub1 :+: sub2) ctx dom
  where
    optimizeFeat ctx constFold (InjectL a) = optimizeFeat ctx constFold a
    optimizeFeat ctx constFold (InjectR a) = optimizeFeat ctx constFold a

optimizeM :: Optimize dom ctx dom
    => Proxy ctx
    -> ConstFolder dom
    -> ASTF dom a
    -> Writer (Set VarId) (ASTF dom a)
optimizeM ctx constFold = transformNode (optimizeFeat ctx constFold)

-- | Optimize an expression
optimize :: Optimize dom ctx dom =>
    Proxy ctx -> ConstFolder dom -> ASTF dom a -> ASTF dom a
optimize ctx constFold = fst . runWriter . optimizeM ctx constFold

-- | Convenient default implementation of 'optimizeFeat' (uses 'evalBind' to
-- partially evaluate)
optimizeFeatDefault
    :: ( feature :<: dom
       , WitnessCons feature
       , Optimize dom ctx dom
       )
    => Proxy ctx
    -> ConstFolder dom
    -> feature a
    -> HList (AST dom) a
    -> Writer (Set VarId) (ASTF dom (EvalResult a))
optimizeFeatDefault ctx constFold feat@(witnessCons -> ConsWit) args = do
    (args',vars) <- listen $ mapHListM (optimizeM ctx constFold) args
    let result = appHList (Symbol $ inject feat) args'
        value  = evalBind result
    if Set.null vars
      then return $ constFold result value
      else return result

instance (Sym ctx'      :<: dom, Optimize dom ctx dom) => Optimize (Sym ctx')      ctx dom where optimizeFeat = optimizeFeatDefault
instance (Literal ctx'  :<: dom, Optimize dom ctx dom) => Optimize (Literal ctx')  ctx dom where optimizeFeat = optimizeFeatDefault
instance (Tuple ctx'    :<: dom, Optimize dom ctx dom) => Optimize (Tuple ctx')    ctx dom where optimizeFeat = optimizeFeatDefault
instance (Select ctx'   :<: dom, Optimize dom ctx dom) => Optimize (Select ctx')   ctx dom where optimizeFeat = optimizeFeatDefault
instance (Let ctxa ctxb :<: dom, Optimize dom ctx dom) => Optimize (Let ctxa ctxb) ctx dom where optimizeFeat = optimizeFeatDefault

instance
    ( Condition ctx' :<: dom
    , Lambda ctx :<: dom
    , Variable ctx :<: dom
    , ExprEq dom
    , Optimize dom ctx dom
    ) =>
      Optimize (Condition ctx') ctx dom
  where
    optimizeFeat ctx constFold cond@Condition args@(c :*: t :*: e :*: Nil)
        | Set.null cVars  = optimizeM ctx constFold t_or_e
        | alphaEq ctx t e = optimizeM ctx constFold t
        | otherwise       = optimizeFeatDefault ctx constFold cond args
      where
        (c',cVars) = runWriter $ optimizeM ctx constFold c
        t_or_e     = if evalBind c' then t else e

instance (Variable ctx :<: dom, Optimize dom ctx dom) =>
    Optimize (Variable ctx) ctx dom
  where
    optimizeFeat _ _ var@(Variable v) Nil = do
        tell (singleton v)
        return (inject var)

instance (Lambda ctx :<: dom, Optimize dom ctx dom) =>
    Optimize (Lambda ctx) ctx dom
  where
    optimizeFeat ctx constFold lam@(Lambda v) (body :*: Nil) = do
        body' <- censor (delete v) $ optimizeM ctx constFold body
        return $ inject lam :$: body'

