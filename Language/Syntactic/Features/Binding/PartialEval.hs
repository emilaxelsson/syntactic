{-# LANGUAGE UndecidableInstances #-}

-- | Partial evaluation

module Language.Syntactic.Features.Binding.PartialEval where



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
type ConstFolder ctx dom = forall a
    .  ASTF (Lambda ctx :+: Variable ctx :+: dom) a
    -> a
    -> ASTF (Lambda ctx :+: Variable ctx :+: dom) a

-- | Partial evaluation
class Eval dom => PartialEval feature ctx dom
  where
    -- | Partial evaluation of a feature. The @(`Set` `VarId`)@ returned is the
    -- set of free variables of the expression. However, free variables are
    -- counted in a \"lazy\" sense: free variables from sub-expressions that are
    -- never evaluated may not be counted. (The instance for 'Conditional' will
    -- throw away the free variables of the pruned branch when the condition is
    -- statically known. This is one reason why partial evaluation and free
    -- variable calculation have to be done simultaneously.)
    partEvalFeat
        :: Proxy ctx
        -> ConstFolder ctx dom
        -> feature a
        -> HList (AST (Lambda ctx :+: Variable ctx :+: dom)) a
        -> Writer
            (Set VarId)
            (ASTF (Lambda ctx :+: Variable ctx :+: dom) (EvalResult a))

instance (PartialEval sub1 ctx dom, PartialEval sub2 ctx dom) =>
    PartialEval (sub1 :+: sub2) ctx dom
  where
    partEvalFeat ctx constFold (InjectL a) = partEvalFeat ctx constFold a
    partEvalFeat ctx constFold (InjectR a) = partEvalFeat ctx constFold a

partialEvalM :: PartialEval dom ctx dom
    => Proxy ctx
    -> ConstFolder ctx dom
    -> ASTF (Lambda ctx :+: Variable ctx :+: dom) a
    -> Writer (Set VarId) (ASTF (Lambda ctx :+: Variable ctx :+: dom) a)
partialEvalM ctx constFold = transformNodeC (partEvalFeat ctx constFold)

-- | Partially evaluate an expression
partialEval :: PartialEval dom ctx dom
    => Proxy ctx
    -> ConstFolder ctx dom
    -> ASTF (Lambda ctx :+: Variable ctx :+: dom) a
    -> ASTF (Lambda ctx :+: Variable ctx :+: dom) a
partialEval ctx constFold = fst . runWriter . partialEvalM ctx constFold



-- | Convenient default implementation of 'partEvalFeat' (uses 'evalLambda' to
-- evaluate)
partEvalFeatDefault
    :: ( feature :<: dom
       , WitnessCons feature
       , PartialEval dom ctx dom
       )
    => Proxy ctx
    -> ConstFolder ctx dom
    -> feature a
    -> HList (AST (Lambda ctx :+: Variable ctx :+: dom)) a
    -> Writer
        (Set VarId)
        (ASTF (Lambda ctx :+: Variable ctx :+: dom) (EvalResult a))
partEvalFeatDefault ctx constFold feat@(witnessCons -> ConsWit) args = do
    (args',vars) <- listen $ mapHListM (partialEvalM ctx constFold) args
    let result = appHList (Symbol $ InjectR $ InjectR $ inject feat) args'
        value  = evalLambda result
    if Set.null vars
      then return $ constFold result value
      else return result

instance (Sym ctx' :<: dom, PartialEval dom ctx dom) =>
    PartialEval (Sym ctx') ctx dom
  where
    partEvalFeat = partEvalFeatDefault

instance (Literal ctx' :<: dom, PartialEval dom ctx dom) =>
    PartialEval (Literal ctx') ctx dom
  where
    partEvalFeat = partEvalFeatDefault

instance (Condition ctx' :<: dom, PartialEval dom ctx dom) =>
    PartialEval (Condition ctx') ctx dom
  where
    partEvalFeat ctx constFold cond@Condition args@(c :*: t :*: e :*: Nil)
        | Set.null cVars = partialEvalM ctx constFold t_or_e
        | otherwise      = partEvalFeatDefault ctx constFold cond args
      where
        (c',cVars) = runWriter $ partialEvalM ctx constFold c
        t_or_e     = if evalLambda c' then t else e

instance (Tuple ctx' :<: dom, PartialEval dom ctx dom) =>
    PartialEval (Tuple ctx') ctx dom
  where
    partEvalFeat = partEvalFeatDefault

instance (Select ctx' :<: dom, PartialEval dom ctx dom) =>
    PartialEval (Select ctx') ctx dom
  where
    partEvalFeat = partEvalFeatDefault

instance PartialEval dom ctx dom => PartialEval (Variable ctx) ctx dom
  where
    partEvalFeat _ _ var@(Variable v) Nil = do
        tell (singleton v)
        return (inject var)

instance PartialEval dom ctx dom => PartialEval (Lambda ctx) ctx dom
  where
    partEvalFeat ctx constFold lam@(Lambda v) (body :*: Nil) = do
        body' <- censor (delete v) $ partialEvalM ctx constFold body
        return $ inject lam :$: body'

instance (Let ctxa ctxb :<: dom, PartialEval dom ctx dom) =>
    PartialEval (Let ctxa ctxb) ctx dom
  where
    partEvalFeat = partEvalFeatDefault

