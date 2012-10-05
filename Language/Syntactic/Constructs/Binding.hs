{-# LANGUAGE UndecidableInstances #-}

-- | General binding constructs

module Language.Syntactic.Constructs.Binding where



import qualified Control.Monad.Identity as Monad
import Control.Monad.Reader
import Data.Ix
import Data.Tree
import Data.Typeable

import Data.Hash

import Data.PolyProxy
import Data.DynamicAlt
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
data Variable a
  where
    Variable :: VarId -> Variable (Full a)

instance Constrained Variable
  where
    type Sat Variable = Top
    exprDict _ = Dict

-- | 'equal' does strict identifier comparison; i.e. no alpha equivalence.
--
-- 'exprHash' assigns the same hash to all variables. This is a valid
-- over-approximation that enables the following property:
--
-- @`alphaEq` a b  ==>  `exprHash` a == `exprHash` b@
instance Equality Variable
  where
    equal (Variable v1) (Variable v2) = v1==v2
    exprHash (Variable _)             = hashInt 0

instance Render Variable
  where
    render (Variable v) = showVar v

instance ToTree Variable
  where
    toTreeArgs [] (Variable v) = Node ("var:" ++ show v) []



--------------------------------------------------------------------------------
-- * Lambda binding
--------------------------------------------------------------------------------

-- | Lambda binding
data Lambda a
  where
    Lambda :: VarId -> Lambda (b :-> Full (a -> b))

instance Constrained Lambda
  where
    type Sat Lambda = Top
    exprDict _ = Dict

-- | 'equal' does strict identifier comparison; i.e. no alpha equivalence.
--
-- 'exprHash' assigns the same hash to all 'Lambda' bindings. This is a valid
-- over-approximation that enables the following property:
--
-- @`alphaEq` a b  ==>  `exprHash` a == `exprHash` b@
instance Equality Lambda
  where
    equal (Lambda v1) (Lambda v2) = v1==v2
    exprHash (Lambda _)           = hashInt 0

instance Render Lambda
  where
    renderArgs [body] (Lambda v) = "(\\" ++ showVar v ++ " -> "  ++ body ++ ")"

instance ToTree Lambda
  where
    toTreeArgs [body] (Lambda v) = Node ("Lambda " ++ show v) [body]



--------------------------------------------------------------------------------
-- * Let binding
--------------------------------------------------------------------------------

-- | Let binding
--
-- 'Let' is just an application operator with flipped argument order. The argument
-- @(a -> b)@ is preferably constructed by 'Lambda'.
data Let a
  where
    Let :: Let (a :-> (a -> b) :-> Full b)

instance Constrained Let
  where
    type Sat Let = Top
    exprDict _ = Dict

instance Equality Let
  where
    equal Let Let = True
    exprHash Let  = hashInt 0

instance Render Let
  where
    renderArgs []    Let = "Let"
    renderArgs [f,a] Let = "(" ++ unwords ["letBind",f,a] ++ ")"

instance ToTree Let
  where
    toTreeArgs [a,body] Let = case splitAt 7 node of
        ("Lambda ", var) -> Node ("Let " ++ var) [a,body']
        _                -> Node "Let" [a,body]
      where
        Node node ~[body'] = body
        var                = drop 7 node  -- Drop the "Lambda " prefix

instance Eval Let
  where
    evaluate Let = flip ($)



--------------------------------------------------------------------------------
-- * Interpretation
--------------------------------------------------------------------------------

-- | Should be a capture-avoiding substitution, but it is currently not correct.
--
-- Note: Variables with a different type than the new expression will be
-- silently ignored.
subst :: forall constr dom a b
    .  ( ConstrainedBy dom Typeable
       , Project Lambda dom
       , Project Variable dom
       )
    => VarId       -- ^ Variable to be substituted
    -> ASTF dom a  -- ^ Expression to substitute for
    -> ASTF dom b  -- ^ Expression to substitute in
    -> ASTF dom b
subst v new a = go a
  where
    go :: AST dom c -> AST dom c
    go a@((prj -> Just (Lambda w)) :$ _)
        | v==w = a  -- Capture
    go (f :$ a) = go f :$ go a
    go var
        | Just (Variable w) <- prj var
        , v==w
        , Dict <- exprDictSub pTypeable new
        , Dict <- exprDictSub pTypeable var
        , Just new' <- gcast new
        = new'
    go a = a
  -- TODO Make it correct (may need to alpha-convert `new` before inserting it)
  -- TODO Should there be an error if `gcast` fails? (See note in Haddock
  --      comment.)

-- | Beta-reduction of an expression. The expression to be reduced is assumed to
-- be a `Lambda`.
betaReduce
    :: ( ConstrainedBy dom Typeable
       , Project Lambda dom
       , Project Variable dom
       )
    => ASTF dom a         -- ^ Argument
    -> ASTF dom (a -> b)  -- ^ Function to be reduced
    -> ASTF dom b
betaReduce new (lam :$ body)
    | Just (Lambda v) <- prj lam = subst v new body



-- | Evaluation of expressions with variables
class EvalBind sub
  where
    evalBindSym
        :: (EvalBind dom, ConstrainedBy dom Typeable, Typeable (DenResult sig))
        => sub sig
        -> Args (AST dom) sig
        -> Reader [(VarId,Dynamic)] (DenResult sig)
  -- `(Typeable (DenResult sig))` is required because this dictionary cannot (in
  -- general) be obtained from `sub`. It can only be obtained from `dom`, and
  -- this is what `evalBindM` does.

instance (EvalBind sub1, EvalBind sub2) => EvalBind (sub1 :+: sub2)
  where
    evalBindSym (InjL a) = evalBindSym a
    evalBindSym (InjR a) = evalBindSym a

-- | Evaluation of possibly open expressions
evalBindM :: (EvalBind dom, ConstrainedBy dom Typeable) =>
    ASTF dom a -> Reader [(VarId,Dynamic)] a
evalBindM a
    | Dict <- exprDictSub pTypeable a
    = liftM result $ match (\s -> liftM Full . evalBindSym s) a

-- | Evaluation of closed expressions
evalBind :: (EvalBind dom, ConstrainedBy dom Typeable) => ASTF dom a -> a
evalBind = flip runReader [] . evalBindM

-- | Apply a symbol denotation to a list of arguments
appDen :: Denotation sig -> Args Monad.Identity sig -> DenResult sig
appDen a Nil       = a
appDen f (a :* as) = appDen (f $ result $ Monad.runIdentity a) as

-- | Convenient default implementation of 'evalBindSym'
evalBindSymDefault
    :: (Eval sub, EvalBind dom, ConstrainedBy dom Typeable)
    => sub sig
    -> Args (AST dom) sig
    -> Reader [(VarId,Dynamic)] (DenResult sig)
evalBindSymDefault sym args = do
    args' <- mapArgsM (liftM (Monad.Identity . Full) . evalBindM) args
    return $ appDen (evaluate sym) args'

instance EvalBind dom => EvalBind (dom :| pred)
  where
    evalBindSym (C a) = evalBindSym a

instance EvalBind dom => EvalBind (dom :|| pred)
  where
    evalBindSym (C' a) = evalBindSym a

instance EvalBind dom => EvalBind (SubConstr1 dom p)
  where
    evalBindSym (SubConstr1 a) = evalBindSym a

instance EvalBind dom => EvalBind (SubConstr2 dom pa pb)
  where
    evalBindSym (SubConstr2 a) = evalBindSym a

instance EvalBind Empty
  where
    evalBindSym = error "Not implemented: evalBindSym for Empty"

instance EvalBind dom => EvalBind (Decor info dom)
  where
    evalBindSym = evalBindSym . decorExpr

instance EvalBind Identity  where evalBindSym = evalBindSymDefault
instance EvalBind Construct where evalBindSym = evalBindSymDefault
instance EvalBind Literal   where evalBindSym = evalBindSymDefault
instance EvalBind Condition where evalBindSym = evalBindSymDefault
instance EvalBind Tuple     where evalBindSym = evalBindSymDefault
instance EvalBind Select    where evalBindSym = evalBindSymDefault
instance EvalBind Let       where evalBindSym = evalBindSymDefault

instance Monad m => EvalBind (MONAD m) where evalBindSym = evalBindSymDefault

instance EvalBind Variable
  where
    evalBindSym (Variable v) Nil = do
        env <- ask
        case lookup v env of
            Nothing -> return $ error "evalBind: evaluating free variable"
            Just a  -> case fromDyn a of
              Just a -> return a
              _      -> return $ error "evalBind: internal type error"

instance EvalBind Lambda
  where
    evalBindSym lam@(Lambda v) (body :* Nil) = do
        env <- ask
        return
            $ \a -> flip runReader ((v, toDyn (funType lam) a):env)
            $ evalBindM body
      where
        funType :: Lambda (b :-> Full (a -> b)) -> P (a -> b)
        funType _ = P



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

-- | Alpha-equivalence
class AlphaEq sub1 sub2 dom env
  where
    alphaEqSym
        :: sub1 a
        -> Args (AST dom) a
        -> sub2 b
        -> Args (AST dom) b
        -> Reader env Bool

instance (AlphaEq subA1 subB1 dom env, AlphaEq subA2 subB2 dom env) =>
    AlphaEq (subA1 :+: subA2) (subB1 :+: subB2) dom env
  where
    alphaEqSym (InjL a) aArgs (InjL b) bArgs = alphaEqSym a aArgs b bArgs
    alphaEqSym (InjR a) aArgs (InjR b) bArgs = alphaEqSym a aArgs b bArgs
    alphaEqSym _ _ _ _ = return False

alphaEqM :: AlphaEq dom dom dom env =>
    ASTF dom a -> ASTF dom b -> Reader env Bool
alphaEqM a b = simpleMatch (alphaEqM2 b) a

alphaEqM2 :: AlphaEq dom dom dom env =>
    ASTF dom b -> dom a -> Args (AST dom) a -> Reader env Bool
alphaEqM2 b a aArgs = simpleMatch (alphaEqSym a aArgs) b

-- | Alpha-equivalence on lambda expressions. Free variables are taken to be
-- equivalent if they have the same identifier.
alphaEq :: AlphaEq dom dom dom [(VarId,VarId)] =>
    ASTF dom a -> ASTF dom b -> Bool
alphaEq a b = flip runReader ([] :: [(VarId,VarId)]) $ alphaEqM a b

alphaEqSymDefault :: (Equality sub, AlphaEq dom dom dom env)
    => sub a
    -> Args (AST dom) a
    -> sub b
    -> Args (AST dom) b
    -> Reader env Bool
alphaEqSymDefault a aArgs b bArgs
    | equal a b = alphaEqChildren a' b'
    | otherwise = return False
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

instance AlphaEq sub sub dom env => AlphaEq (sub :| pred) (sub :| pred) dom env
  where
    alphaEqSym (C a) aArgs (C b) bArgs = alphaEqSym a aArgs b bArgs

instance AlphaEq sub sub dom env => AlphaEq (sub :|| pred) (sub :|| pred) dom env
  where
    alphaEqSym (C' a) aArgs (C' b) bArgs = alphaEqSym a aArgs b bArgs

instance AlphaEq sub sub dom env => AlphaEq (SubConstr1 sub p) (SubConstr1 sub p) dom env
  where
    alphaEqSym (SubConstr1 a) aArgs (SubConstr1 b) bArgs = alphaEqSym a aArgs b bArgs

instance AlphaEq sub sub dom env => AlphaEq (SubConstr2 sub pa pb) (SubConstr2 sub pa pb) dom env
  where
    alphaEqSym (SubConstr2 a) aArgs (SubConstr2 b) bArgs = alphaEqSym a aArgs b bArgs

instance AlphaEq Empty Empty dom env
  where
    alphaEqSym = error "Not implemented: alphaEqSym for Empty"

instance AlphaEq dom dom dom env => AlphaEq Condition Condition dom env where alphaEqSym = alphaEqSymDefault
instance AlphaEq dom dom dom env => AlphaEq Construct Construct dom env where alphaEqSym = alphaEqSymDefault
instance AlphaEq dom dom dom env => AlphaEq Identity  Identity  dom env where alphaEqSym = alphaEqSymDefault
instance AlphaEq dom dom dom env => AlphaEq Let       Let       dom env where alphaEqSym = alphaEqSymDefault
instance AlphaEq dom dom dom env => AlphaEq Literal   Literal   dom env where alphaEqSym = alphaEqSymDefault
instance AlphaEq dom dom dom env => AlphaEq Select    Select    dom env where alphaEqSym = alphaEqSymDefault
instance AlphaEq dom dom dom env => AlphaEq Tuple     Tuple     dom env where alphaEqSym = alphaEqSymDefault

instance AlphaEq sub sub dom env =>
    AlphaEq (Decor info sub) (Decor info sub) dom env
  where
    alphaEqSym a aArgs b bArgs =
        alphaEqSym (decorExpr a) aArgs (decorExpr b) bArgs

instance (AlphaEq dom dom dom env, Monad m) => AlphaEq (MONAD m) (MONAD m) dom env
  where
    alphaEqSym = alphaEqSymDefault

instance (AlphaEq dom dom dom env, VarEqEnv env) =>
    AlphaEq Variable Variable dom env
  where
    alphaEqSym (Variable v1) Nil (Variable v2) Nil = do
        env <- asks prjVarEqEnv
        case lookup v1 env of
          Nothing  -> return (v1==v2)   -- Free variables
          Just v2' -> return (v2==v2')

instance (AlphaEq dom dom dom env, VarEqEnv env) =>
    AlphaEq Lambda Lambda dom env
  where
    alphaEqSym (Lambda v1) (body1 :* Nil) (Lambda v2) (body2 :* Nil) =
        local (modVarEqEnv ((v1,v2):)) $ alphaEqM body1 body2

