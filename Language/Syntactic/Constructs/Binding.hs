{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- | General binding constructs

module Language.Syntactic.Constructs.Binding where



import qualified Control.Monad.Identity as Monad
import Control.Monad.Reader
import Data.Dynamic
import Data.Ix
import Data.Tree

import Data.Hash
import Data.Proxy

import Language.Syntactic
import Language.Syntactic.Constructs.Condition
import Language.Syntactic.Constructs.Construct
import Language.Syntactic.Constructs.Decoration
import Language.Syntactic.Constructs.Identity
import Language.Syntactic.Constructs.Literal
import Language.Syntactic.Constructs.Monad
import Language.Syntactic.Constructs.Tuple



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
prjLet _ _ = prj



--------------------------------------------------------------------------------
-- * Interpretation
--------------------------------------------------------------------------------

-- | Capture-avoiding substitution
subst :: forall ctx dom a b
    .  (Lambda ctx :<: dom, Variable ctx :<: dom, Typeable a)
    => Proxy ctx
    -> VarId       -- ^ Variable to be substituted
    -> ASTF dom a  -- ^ Expression to substitute for
    -> ASTF dom b  -- ^ Expression to substitute in
    -> ASTF dom b
subst ctx v new a = go a
  where
    go :: AST dom c -> AST dom c
    go a@((prjCtx ctx -> Just (Lambda w)) :$ _)
        | v==w = a  -- Capture
    go (f :$ a) = go f :$ go a
    go (prjCtx ctx -> Just (Variable w))
        | v==w
        , Just new' <- gcast new
        = new'
    go a = a

-- | Beta-reduction of an expression. The expression to be reduced is assumed to
-- be a `Lambda`.
betaReduce :: forall ctx dom a b . (Lambda ctx :<: dom, Variable ctx :<: dom)
    => Proxy ctx
    -> ASTF dom a         -- ^ Argument
    -> ASTF dom (a -> b)  -- ^ Function to be reduced
    -> ASTF dom b
betaReduce ctx new ((prjCtx ctx -> Just (Lambda v)) :$ body) =
    subst ctx v new body



class EvalBind sub
  where
    evalBindSym
        :: (EvalBind dom, Signature a)
        => sub a
        -> Args (AST dom) a
        -> Reader [(VarId,Dynamic)] (DenResult a)

instance (EvalBind sub1, EvalBind sub2) => EvalBind (sub1 :+: sub2)
  where
    evalBindSym (InjL a) = evalBindSym a
    evalBindSym (InjR a) = evalBindSym a

-- | Evaluation of possibly open expressions
evalBindM :: EvalBind dom => ASTF dom a -> Reader [(VarId,Dynamic)] a
evalBindM = liftM result . queryNode (\a -> liftM Full . evalBindSym a)

-- | Evaluation of closed expressions
evalBind :: EvalBind dom => ASTF dom a -> a
evalBind = flip runReader [] . evalBindM

-- | Convenient default implementation of 'evalBindSym'
evalBindSymDefault :: (Eval sub, Signature a, EvalBind dom)
    => sub a
    -> Args (AST dom) a
    -> Reader [(VarId,Dynamic)] (DenResult a)
evalBindSymDefault sym args = do
    args' <- mapArgsM (liftM (Monad.Identity . Full) . evalBindM) args
    return $ appEvalArgs (toEval $ evaluate sym) args'

instance EvalBind (Identity ctx)       where evalBindSym = evalBindSymDefault
instance EvalBind (Construct ctx)      where evalBindSym = evalBindSymDefault
instance EvalBind (Literal ctx)        where evalBindSym = evalBindSymDefault
instance EvalBind (Condition ctx)      where evalBindSym = evalBindSymDefault
instance EvalBind (Tuple ctx)          where evalBindSym = evalBindSymDefault
instance EvalBind (Select ctx)         where evalBindSym = evalBindSymDefault
instance EvalBind (Let ctxa ctxb)      where evalBindSym = evalBindSymDefault
instance Monad m => EvalBind (MONAD m) where evalBindSym = evalBindSymDefault

instance EvalBind dom => EvalBind (Decor info dom)
  where
    evalBindSym a args = evalBindSym (decorExpr a) args

instance EvalBind (Lambda ctx)
  where
    evalBindSym (Lambda v) (body :* Nil) = do
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



--------------------------------------------------------------------------------
-- * Alpha equivalence
--------------------------------------------------------------------------------

-- | Environments containing a list of variable equivalences
class VarEqEnv a
  where
    prjVarEqEnv :: a -> [(VarId,VarId)]
    modVarEqEnv :: ([(VarId,VarId)] -> [(VarId,VarId)]) -> (a -> a)

instance VarEqEnv [(VarId,VarId)]
  where
    prjVarEqEnv = id
    modVarEqEnv = id

class AlphaEq sub1 sub2 dom env
  where
    alphaEqSym
        :: (Signature a, Signature b)
        => sub1 a
        -> Args (AST dom) a
        -> sub2 b
        -> Args (AST dom) b
        -> Reader env Bool

instance (AlphaEq subA1 subB1 dom env, AlphaEq subA2 subB2 dom env) =>
    AlphaEq (subA1 :+: subA2) (subB1 :+: subB2) dom env
  where
    alphaEqSym (InjL a) aArgs (InjL b) bArgs = alphaEqSym a aArgs b bArgs
    alphaEqSym (InjR a) aArgs (InjR b) bArgs = alphaEqSym a aArgs b bArgs
    alphaEqSym (InjL a) aArgs (InjR b) bArgs = return False
    alphaEqSym (InjR a) aArgs (InjL b) bArgs = return False

alphaEqM :: AlphaEq dom dom dom env =>
    ASTF dom a -> ASTF dom b -> Reader env Bool
alphaEqM a b = queryNodeSimple (alphaEqM2 b) a

alphaEqM2 :: (AlphaEq dom dom dom env, Signature a) =>
    ASTF dom b -> dom a -> Args (AST dom) a -> Reader env Bool
alphaEqM2 b a aArgs = queryNodeSimple (alphaEqSym a aArgs) b

-- | Alpha-equivalence on lambda expressions. Free variables are taken to be
-- equivalent if they have the same identifier.
alphaEq :: AlphaEq dom dom dom [(VarId,VarId)] =>
    ASTF dom a -> ASTF dom b -> Bool
alphaEq a b = flip runReader ([] :: [(VarId,VarId)]) $ alphaEqM a b

alphaEqSymDefault
    :: ( ExprEq sub
       , AlphaEq dom dom dom env
       , Signature a
       , Signature b
       )
    => sub a
    -> Args (AST dom) a
    -> sub b
    -> Args (AST dom) b
    -> Reader env Bool
alphaEqSymDefault a aArgs b bArgs
    | exprEq a b = alphaEqChildren a' b'
    | otherwise  = return False
  where
    a' = appArgs (Sym (undefined :: dom a)) aArgs
    b' = appArgs (Sym (undefined :: dom b)) bArgs

alphaEqChildren :: AlphaEq dom dom dom env =>
    AST dom a -> AST dom b -> Reader env Bool
alphaEqChildren (Sym _)  (Sym _)  = return True
alphaEqChildren (f :$ a) (g :$ b) = liftM2 (&&)
    (alphaEqChildren f g)
    (alphaEqM a b)
alphaEqChildren _ _ = return False

instance AlphaEq dom dom dom env => AlphaEq (Identity ctx)  (Identity ctx)  dom env where alphaEqSym = alphaEqSymDefault
instance AlphaEq dom dom dom env => AlphaEq (Construct ctx) (Construct ctx) dom env where alphaEqSym = alphaEqSymDefault
instance AlphaEq dom dom dom env => AlphaEq (Literal ctx)   (Literal ctx)   dom env where alphaEqSym = alphaEqSymDefault
instance AlphaEq dom dom dom env => AlphaEq (Condition ctx) (Condition ctx) dom env where alphaEqSym = alphaEqSymDefault
instance AlphaEq dom dom dom env => AlphaEq (Tuple ctx)     (Tuple ctx)     dom env where alphaEqSym = alphaEqSymDefault
instance AlphaEq dom dom dom env => AlphaEq (Select ctx)    (Select ctx)    dom env where alphaEqSym = alphaEqSymDefault
instance AlphaEq dom dom dom env => AlphaEq (Let ctxa ctxb) (Let ctxa ctxb) dom env where alphaEqSym = alphaEqSymDefault

instance (AlphaEq dom dom dom env, Monad m) => AlphaEq (MONAD m) (MONAD m) dom env
  where
    alphaEqSym = alphaEqSymDefault

instance AlphaEq dom dom (Decor info dom) env =>
    AlphaEq (Decor info dom) (Decor info dom) (Decor info dom) env
  where
    alphaEqSym a aArgs b bArgs =
        alphaEqSym (decorExpr a) aArgs (decorExpr b) bArgs

instance (AlphaEq dom dom dom env, VarEqEnv env) =>
    AlphaEq (Lambda ctx) (Lambda ctx) dom env
  where
    alphaEqSym (Lambda v1) (body1 :* Nil) (Lambda v2) (body2 :* Nil) =
        local (modVarEqEnv ((v1,v2):)) $ alphaEqM body1 body2

instance (AlphaEq dom dom dom env, VarEqEnv env) =>
    AlphaEq (Variable ctx) (Variable ctx) dom env
  where
    alphaEqSym (Variable v1) Nil (Variable v2) Nil = do
        env <- asks prjVarEqEnv
        case lookup v1 env of
          Nothing  -> return (v1==v2)   -- Free variables
          Just v2' -> return (v2==v2')

