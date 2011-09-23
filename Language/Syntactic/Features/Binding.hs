{-# LANGUAGE OverlappingInstances #-}

-- | General binding constructs

module Language.Syntactic.Features.Binding where



import Control.Monad.Identity
import Control.Monad.Reader
import Data.Dynamic
import Data.Ix
import Data.Tree

import Data.Hash
import Data.Proxy

import Language.Syntactic
import Language.Syntactic.Features.Symbol
import Language.Syntactic.Features.Literal
import Language.Syntactic.Features.Condition
import Language.Syntactic.Features.Tuple



--------------------------------------------------------------------------------
-- * Variables
--------------------------------------------------------------------------------

-- | Variable identifier
newtype VarId = VarId { varInteger :: Integer }
  deriving (Eq, Ord, Num, Real, Integral, Enum, Ix)

instance Show VarId
  where
    show (VarId i) = show i

showVar :: VarId -> String
showVar v = "var" ++ show v



-- | Variables
data Variable ctx a
  where
    Variable :: (Typeable a, Sat ctx a) => VarId -> Variable ctx (Full a)
      -- 'Typeable' needed by the dynamic types in 'evalBind'.

instance WitnessCons (Variable ctx)
  where
    witnessCons (Variable _) = ConsWit

instance WitnessSat (Variable ctx)
  where
    type SatContext (Variable ctx) = ctx
    witnessSat (Variable _) = SatWit

instance MaybeWitnessSat ctx (Variable ctx)
  where
    maybeWitnessSat = maybeWitnessSatDefault

instance MaybeWitnessSat ctx1 (Variable ctx2)
  where
    maybeWitnessSat _ _ = Nothing

-- | 'exprEq' does strict identifier comparison; i.e. no alpha equivalence.
--
-- 'exprHash' assigns the same hash to all variables. This is a valid
-- over-approximation that enables the following property:
--
-- @`alphaEq` a b  ==>  `exprHash` a == `exprHash` b@
instance ExprEq (Variable ctx)
  where
    exprEq (Variable v1) (Variable v2) = v1==v2
    exprHash (Variable _)              = hashInt 0

instance Render (Variable ctx)
  where
    render (Variable v) = showVar v

instance ToTree (Variable ctx)
  where
    toTreePart [] (Variable v) = Node ("var:" ++ show v) []

-- | Partial `Variable` projection with explicit context
prjVariable :: (Variable ctx :<: sup) =>
    Proxy ctx -> sup a -> Maybe (Variable ctx a)
prjVariable _ = project



--------------------------------------------------------------------------------
-- * Lambda binding
--------------------------------------------------------------------------------

-- | Lambda binding
data Lambda ctx a
  where
    Lambda :: (Typeable a, Sat ctx a) =>
        VarId -> Lambda ctx (b :-> Full (a -> b))
      -- 'Typeable' needed by the dynamic types in 'evalBind'.

instance WitnessCons (Lambda ctx)
  where
    witnessCons (Lambda _) = ConsWit

instance MaybeWitnessSat ctx1 (Lambda ctx2)
  where
    maybeWitnessSat _ _ = Nothing

-- | 'exprEq' does strict identifier comparison; i.e. no alpha equivalence.
--
-- 'exprHash' assigns the same hash to all 'Lambda' bindings. This is a valid
-- over-approximation that enables the following property:
--
-- @`alphaEq` a b  ==>  `exprHash` a == `exprHash` b@
instance ExprEq (Lambda ctx)
  where
    exprEq (Lambda v1) (Lambda v2) = v1==v2
    exprHash (Lambda _)            = hashInt 0

instance Render (Lambda ctx)
  where
    renderPart [body] (Lambda v) = "(\\" ++ showVar v ++ " -> "  ++ body ++ ")"

instance ToTree (Lambda ctx)
  where
    toTreePart [body] (Lambda v) = Node ("Lambda " ++ show v) [body]

-- | Partial `Lambda` projection with explicit context
prjLambda :: (Lambda ctx :<: sup) => Proxy ctx -> sup a -> Maybe (Lambda ctx a)
prjLambda _ = project



-- | The class of n-ary binding functions
class NAry ctx a dom | a -> dom
    -- Note: using a functional dependency rather than an associated type,
    -- because this makes it possible to make a class alias constraining dom.
    -- GHC doesn't yet handle equality super classes.
  where
    type NAryEval a

    -- | N-ary binding by nested use of the supplied binder
    bindN
      :: Proxy ctx
      -> (  forall b c . (Typeable b, Typeable c, Sat ctx b)
         => (ASTF dom b -> ASTF dom c)
         -> ASTF dom (b -> c)
         )
      -> a -> ASTF dom (NAryEval a)

instance NAry ctx (ASTF dom a) dom
  where
    type NAryEval (ASTF dom a) = a
    bindN _ _ = id

instance (Typeable a, Sat ctx a, NAry ctx b dom, Typeable (NAryEval b)) =>
    NAry ctx (ASTF dom a -> b) dom
  where
    type NAryEval (ASTF dom a -> b) = a -> NAryEval b
    bindN ctx lambda = lambda . (bindN ctx lambda .)



--------------------------------------------------------------------------------
-- * Let binding
--------------------------------------------------------------------------------

-- | Let binding
--
-- A 'Let' expression is really just an application of a lambda binding (the
-- argument @(a -> b)@ is preferably constructed by 'Lambda').
data Let ctxa ctxb a
  where
    Let :: (Sat ctxa a, Sat ctxb b) => Let ctxa ctxb (a :-> (a -> b) :-> Full b)

instance WitnessCons (Let ctxa ctxb)
  where
    witnessCons Let = ConsWit

instance WitnessSat (Let ctxa ctxb)
  where
    type SatContext (Let ctxa ctxb) = ctxb
    witnessSat Let = SatWit

instance MaybeWitnessSat ctxb (Let ctxa ctxb)
  where
    maybeWitnessSat = maybeWitnessSatDefault

instance MaybeWitnessSat ctx (Let ctxa ctxb)
  where
    maybeWitnessSat _ _ = Nothing

instance ExprEq (Let ctxa ctxb)
  where
    exprEq Let Let = True

    exprHash Let = hashInt 0

instance Render (Let ctxa ctxb)
  where
    renderPart []    Let = "Let"
    renderPart [f,a] Let = "(" ++ unwords ["letBind",f,a] ++ ")"

instance ToTree (Let ctxa ctxb)
  where
    toTreePart [a,body] Let = case splitAt 7 node of
        ("Lambda ", var) -> Node ("Let " ++ var) [a,body']
        _                -> Node "Let" [a,body]
      where
        Node node [body'] = body
        var               = drop 7 node  -- Drop the "Lambda " prefix

instance Eval (Let ctxa ctxb)
  where
    evaluate Let = fromEval (flip ($))

-- | Partial `Let` projection with explicit context
prjLet :: (Let ctxa ctxb :<: sup) =>
    Proxy ctxa -> Proxy ctxb -> sup a -> Maybe (Let ctxa ctxb a)
prjLet _ _ = project



--------------------------------------------------------------------------------
-- * Interpretation
--------------------------------------------------------------------------------

-- | Alpha equivalence in an environment of variable equivalences. The supplied
-- equivalence function gets called when the argument expressions are not both
-- 'Variable's, both 'Lambda's or both ':$:'.
alphaEqM :: (Lambda ctx :<: dom, Variable ctx :<: dom)
    => Proxy ctx
    -> (forall a b . AST dom a -> AST dom b -> Reader [(VarId,VarId)] Bool)
    -> (forall a b . AST dom a -> AST dom b -> Reader [(VarId,VarId)] Bool)

-- TODO This function is not ideal, since the type says nothing about which
--      cases have been handled when calling 'eq'.

alphaEqM ctx eq
    ((prjLambda ctx -> Just (Lambda v1)) :$: a1)
    ((prjLambda ctx -> Just (Lambda v2)) :$: a2) =
        local ((v1,v2):) $ alphaEqM ctx eq a1 a2

alphaEqM ctx eq
    (prjVariable ctx -> Just (Variable v1))
    (prjVariable ctx -> Just (Variable v2)) = do
        env <- ask
        case lookup v1 env of
          Nothing  -> return (v1==v2)   -- Free variables
          Just v2' -> return (v2==v2')

alphaEqM ctx eq (f1 :$: a1) (f2 :$: a2) = do
    e <- alphaEqM ctx eq f1 f2
    if e then alphaEqM ctx eq a1 a2 else return False

alphaEqM _ eq a b = eq a b



-- | Alpha-equivalence on lambda expressions. Free variables are taken to be
-- equivalent if they have the same identifier.
alphaEq :: (Lambda ctx :<: dom, Variable ctx :<: dom, ExprEq dom) =>
    Proxy ctx -> AST dom a -> AST dom b -> Bool
alphaEq ctx a b = runReader (alphaEqM ctx (\a b -> return $ exprEq a b) a b) []



class EvalBind feature
  where
    evalBindFeat
        :: (EvalBind dom, ConsType a)
        => feature a
        -> HList (AST dom) a
        -> Reader [(VarId,Dynamic)] (EvalResult a)

instance (EvalBind sub1, EvalBind sub2) => EvalBind (sub1 :+: sub2)
  where
    evalBindFeat (InjectL a) = evalBindFeat a
    evalBindFeat (InjectR a) = evalBindFeat a

-- | Evaluation of possibly open expressions
evalBindM :: EvalBind dom => ASTF dom a -> Reader [(VarId,Dynamic)] a
evalBindM = liftM result . queryNode (\a -> liftM Full . evalBindFeat a)

-- | Evaluation of closed expressions
evalBind :: EvalBind dom => ASTF dom a -> a
evalBind = flip runReader [] . evalBindM

-- | Convenient default implementation of 'evalBindFeat'
evalBindFeatDefault :: (Eval feature, ConsType a, EvalBind dom)
    => feature a
    -> HList (AST dom) a
    -> Reader [(VarId,Dynamic)] (EvalResult a)
evalBindFeatDefault feature args = do
    args' <- mapHListM (liftM (Identity . Full) . evalBindM) args
    return $ appEvalHList (toEval $ evaluate feature) args'

instance EvalBind (Sym ctx)       where evalBindFeat = evalBindFeatDefault
instance EvalBind (Literal ctx)   where evalBindFeat = evalBindFeatDefault
instance EvalBind (Condition ctx) where evalBindFeat = evalBindFeatDefault
instance EvalBind (Tuple ctx)     where evalBindFeat = evalBindFeatDefault
instance EvalBind (Select ctx)    where evalBindFeat = evalBindFeatDefault
instance EvalBind (Let ctxa ctxb) where evalBindFeat = evalBindFeatDefault

instance EvalBind dom => EvalBind (Ann info dom)
  where
    evalBindFeat (Ann _ a) args = evalBindFeat a args

instance EvalBind (Lambda ctx)
  where
    evalBindFeat (Lambda v) (body :*: Nil) = do
        env <- ask
        return
            $ \a -> flip runReader ((v,toDyn a):env)
            $ evalBindM body

instance EvalBind (Variable ctx)
  where
    evalBindFeat (Variable v) Nil = do
        env <- ask
        case lookup v env of
            Nothing -> return $ error "evalBind: evaluating free variable"
            Just a  -> case fromDynamic a of
              Just a -> return a
              _      -> return $ error "evalBind: internal type error"

