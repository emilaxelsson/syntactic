{-# LANGUAGE OverlappingInstances #-}

-- | General binding constructs

module Language.Syntactic.Constructs.Binding where



import Control.Monad.Identity
import Control.Monad.Reader
import Data.Dynamic
import Data.Ix
import Data.Tree

import Data.Hash
import Data.Proxy

import Language.Syntactic
import Language.Syntactic.Constructs.Symbol
import Language.Syntactic.Constructs.Literal
import Language.Syntactic.Constructs.Condition
import Language.Syntactic.Constructs.Tuple
import Language.Syntactic.Constructs.Monad



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

-- | Let binding with explicit context
letBind :: (Sat ctx a, Sat ctx b) =>
    Proxy ctx -> Let ctx ctx (a :-> (a -> b) :-> Full b)
letBind _ = Let

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
    ((prjCtx ctx -> Just (Lambda v1)) :$: a1)
    ((prjCtx ctx -> Just (Lambda v2)) :$: a2) =
        local ((v1,v2):) $ alphaEqM ctx eq a1 a2

alphaEqM ctx eq
    (prjCtx ctx -> Just (Variable v1))
    (prjCtx ctx -> Just (Variable v2)) = do
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



class EvalBind sub
  where
    evalBindSym
        :: (EvalBind dom, ConsType a)
        => sub a
        -> HList (AST dom) a
        -> Reader [(VarId,Dynamic)] (EvalResult a)

instance (EvalBind sub1, EvalBind sub2) => EvalBind (sub1 :+: sub2)
  where
    evalBindSym (InjectL a) = evalBindSym a
    evalBindSym (InjectR a) = evalBindSym a

-- | Evaluation of possibly open expressions
evalBindM :: EvalBind dom => ASTF dom a -> Reader [(VarId,Dynamic)] a
evalBindM = liftM result . queryNode (\a -> liftM Full . evalBindSym a)

-- | Evaluation of closed expressions
evalBind :: EvalBind dom => ASTF dom a -> a
evalBind = flip runReader [] . evalBindM

-- | Convenient default implementation of 'evalBindSym'
evalBindSymDefault :: (Eval sub, ConsType a, EvalBind dom)
    => sub a
    -> HList (AST dom) a
    -> Reader [(VarId,Dynamic)] (EvalResult a)
evalBindSymDefault sym args = do
    args' <- mapHListM (liftM (Identity . Full) . evalBindM) args
    return $ appEvalHList (toEval $ evaluate sym) args'

instance EvalBind (Sym ctx)            where evalBindSym = evalBindSymDefault
instance EvalBind (Literal ctx)        where evalBindSym = evalBindSymDefault
instance EvalBind (Condition ctx)      where evalBindSym = evalBindSymDefault
instance EvalBind (Tuple ctx)          where evalBindSym = evalBindSymDefault
instance EvalBind (Select ctx)         where evalBindSym = evalBindSymDefault
instance EvalBind (Let ctxa ctxb)      where evalBindSym = evalBindSymDefault
instance Monad m => EvalBind (MONAD m) where evalBindSym = evalBindSymDefault

instance EvalBind dom => EvalBind (Ann info dom)
  where
    evalBindSym (Ann _ a) args = evalBindSym a args

instance EvalBind (Lambda ctx)
  where
    evalBindSym (Lambda v) (body :*: Nil) = do
        env <- ask
        return
            $ \a -> flip runReader ((v,toDyn a):env)
            $ evalBindM body

instance EvalBind (Variable ctx)
  where
    evalBindSym (Variable v) Nil = do
        env <- ask
        case lookup v env of
            Nothing -> return $ error "evalBind: evaluating free variable"
            Just a  -> case fromDynamic a of
              Just a -> return a
              _      -> return $ error "evalBind: internal type error"

