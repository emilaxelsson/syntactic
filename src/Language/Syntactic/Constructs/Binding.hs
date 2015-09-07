{-# LANGUAGE DefaultSignatures #-}
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
    {-# SPECIALIZE instance Constrained Variable #-}
    {-# INLINABLE exprDict #-}
    type Sat Variable = Top
    exprDict = const Dict

-- | 'equal' does strict identifier comparison; i.e. no alpha equivalence.
--
-- 'exprHash' assigns the same hash to all variables. This is a valid
-- over-approximation that enables the following property:
--
-- @`alphaEq` a b  ==>  `exprHash` a == `exprHash` b@
instance Equality Variable
  where
    {-# SPECIALIZE instance Equality Variable #-}
    {-# INLINABLE equal #-}
    {-# INLINABLE exprHash #-}
    equal (Variable v1) (Variable v2) = v1==v2
    exprHash (Variable _)             = hashInt 0

instance Render Variable
  where
    {-# SPECIALIZE instance Render Variable #-}
    {-# INLINABLE renderSym #-}
    renderSym (Variable v) = showVar v

instance StringTree Variable
  where
    {-# SPECIALIZE instance StringTree Variable #-}
    {-# INLINABLE stringTreeSym #-}
    stringTreeSym [] (Variable v) = Node ("var:" ++ show v) []



--------------------------------------------------------------------------------
-- * Lambda binding
--------------------------------------------------------------------------------

-- | Lambda binding
data Lambda a
  where
    Lambda :: VarId -> Lambda (b :-> Full (a -> b))

instance Constrained Lambda
  where
    {-# SPECIALIZE instance Constrained Lambda #-}
    {-# INLINABLE exprDict #-}
    type Sat Lambda = Top
    exprDict = const Dict

-- | 'equal' does strict identifier comparison; i.e. no alpha equivalence.
--
-- 'exprHash' assigns the same hash to all 'Lambda' bindings. This is a valid
-- over-approximation that enables the following property:
--
-- @`alphaEq` a b  ==>  `exprHash` a == `exprHash` b@
instance Equality Lambda
  where
    {-# SPECIALIZE instance Equality Lambda #-}
    {-# INLINABLE equal #-}
    {-# INLINABLE exprHash #-}
    equal (Lambda v1) (Lambda v2) = v1==v2
    exprHash (Lambda _)           = hashInt 0

instance Render Lambda
  where
    {-# SPECIALIZE instance Render Lambda #-}
    {-# INLINABLE renderSym #-}
    {-# INLINABLE renderArgs #-}
    renderSym (Lambda v) = "Lambda " ++ show v
    renderArgs [body] (Lambda v) = "(\\" ++ showVar v ++ " -> "  ++ body ++ ")"

instance StringTree Lambda
  where
    {-# SPECIALIZE instance StringTree Lambda #-}
    {-# INLINABLE stringTreeSym #-}
    stringTreeSym [body] (Lambda v) = Node ("Lambda " ++ show v) [body]

-- | Allow an existing binding to be used with a body of a different type
reuseLambda :: Lambda (b :-> Full (a -> b)) -> Lambda (c :-> Full (a -> c))
reuseLambda (Lambda v) = Lambda v
{-# INLINABLE reuseLambda #-}



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
    {-# SPECIALIZE instance Constrained Let #-}
    {-# INLINABLE exprDict #-}
    type Sat Let = Top
    exprDict = const Dict

instance Equality Let
  where
    {-# SPECIALIZE instance Equality Let #-}
    {-# INLINABLE equal #-}
    {-# INLINABLE exprHash #-}
    equal Let Let = True
    exprHash Let  = hashInt 0

instance Render Let
  where
    {-# SPECIALIZE instance Render Let #-}
    {-# INLINABLE renderSym #-}
    {-# INLINABLE renderArgs #-}
    renderSym Let = "Let"
    renderArgs []    Let = "Let"
    renderArgs [f,a] Let = "(" ++ unwords ["letBind",f,a] ++ ")"

instance StringTree Let
  where
    {-# SPECIALIZE instance StringTree Let #-}
    {-# INLINABLE stringTreeSym #-}
    stringTreeSym [a,body] Let = case splitAt 7 node of
        ("Lambda ", var) -> Node ("Let " ++ var) [a,body']
        _                -> Node "Let" [a,body]
      where
        Node node ~[body'] = body

instance Eval Let
  where
    {-# SPECIALIZE instance Eval Let #-}
    {-# INLINABLE evaluate #-}
    evaluate Let = flip ($)



--------------------------------------------------------------------------------
-- * Interpretation
--------------------------------------------------------------------------------

-- | Should be a capture-avoiding substitution, but it is currently not correct.
--
-- Note: Variables with a different type than the new expression will be
-- silently ignored.
subst :: forall dom a b
    .  ( ConstrainedBy dom Typeable
       , Project Lambda dom
       , Project Variable dom
       )
    => VarId       -- ^ Variable to be substituted
    -> ASTF dom a  -- ^ Expression to substitute for
    -> ASTF dom b  -- ^ Expression to substitute in
    -> ASTF dom b
subst v new = go
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
{-# INLINABLE betaReduce #-}



-- | Evaluation of expressions with variables
class EvalBind sub
  where
    evalBindSym
        :: (EvalBind dom, ConstrainedBy dom Typeable, Typeable (DenResult sig))
        => sub sig
        -> Args (AST dom) sig
        -> Reader [(VarId,Dynamic)] (DenResult sig)
    default evalBindSym
        :: (Eval sub, EvalBind dom, ConstrainedBy dom Typeable, Typeable (DenResult sig))
        => sub sig
        -> Args (AST dom) sig
        -> Reader [(VarId,Dynamic)] (DenResult sig)
    evalBindSym = evalBindSymDefault
    {-# INLINABLE evalBindSym #-}
  -- `(Typeable (DenResult sig))` is required because this dictionary cannot (in
  -- general) be obtained from `sub`. It can only be obtained from `dom`, and
  -- this is what `evalBindM` does.

instance (EvalBind sub1, EvalBind sub2) => EvalBind (sub1 :+: sub2)
  where
    {-# SPECIALIZE instance (EvalBind sub1, EvalBind sub2) => EvalBind (sub1 :+: sub2) #-}
    {-# INLINABLE evalBindSym #-}
    evalBindSym (InjL a) = evalBindSym a
    evalBindSym (InjR a) = evalBindSym a

-- | Evaluation of possibly open expressions
evalBindM :: (EvalBind dom, ConstrainedBy dom Typeable) =>
    ASTF dom a -> Reader [(VarId,Dynamic)] a
evalBindM a
    | Dict <- exprDictSub pTypeable a
    = liftM result $ match (\s -> liftM Full . evalBindSym s) a
{-# INLINABLE evalBindM #-}

-- | Evaluation of closed expressions
evalBind :: (EvalBind dom, ConstrainedBy dom Typeable) => ASTF dom a -> a
evalBind = flip runReader [] . evalBindM
{-# INLINABLE evalBind #-}

-- | Apply a symbol denotation to a list of arguments
appDen :: Denotation sig -> Args Monad.Identity sig -> DenResult sig
appDen a Nil       = a
appDen f (a :* as) = appDen (f $ result $ Monad.runIdentity a) as
{-# INLINABLE appDen #-}

-- | Convenient default implementation of 'evalBindSym'
evalBindSymDefault
    :: (Eval sub, EvalBind dom, ConstrainedBy dom Typeable)
    => sub sig
    -> Args (AST dom) sig
    -> Reader [(VarId,Dynamic)] (DenResult sig)
evalBindSymDefault sym args = do
    args' <- mapArgsM (liftM (Monad.Identity . Full) . evalBindM) args
    return $ appDen (evaluate sym) args'
{-# INLINABLE evalBindSymDefault #-}

instance EvalBind dom => EvalBind (dom :| pred)
  where
    {-# SPECIALIZE instance (EvalBind dom) => EvalBind (dom :| pred) #-}
    {-# INLINABLE evalBindSym #-}
    evalBindSym (C a) = evalBindSym a

instance EvalBind dom => EvalBind (dom :|| pred)
  where
    {-# SPECIALIZE instance (EvalBind dom) => EvalBind (dom :|| pred) #-}
    {-# INLINABLE evalBindSym #-}
    evalBindSym (C' a) = evalBindSym a

instance EvalBind dom => EvalBind (SubConstr1 c dom p)
  where
    {-# SPECIALIZE instance (EvalBind dom) => EvalBind (SubConstr1 c dom p) #-}
    {-# INLINABLE evalBindSym #-}
    evalBindSym (SubConstr1 a) = evalBindSym a

instance EvalBind dom => EvalBind (SubConstr2 c dom pa pb)
  where
    {-# SPECIALIZE instance (EvalBind dom) => EvalBind (SubConstr2 c dom pa pb) #-}
    {-# INLINABLE evalBindSym #-}
    evalBindSym (SubConstr2 a) = evalBindSym a

instance EvalBind Empty
  where
    {-# SPECIALIZE instance EvalBind Empty #-}
    evalBindSym = error "Not implemented: evalBindSym for Empty"

instance EvalBind dom => EvalBind (Decor info dom)
  where
    {-# SPECIALIZE instance (EvalBind dom) => EvalBind (Decor info dom) #-}
    {-# INLINABLE evalBindSym #-}
    evalBindSym = evalBindSym . decorExpr

instance EvalBind Identity where {-# SPECIALIZE instance EvalBind Identity #-}
instance EvalBind Construct where {-# SPECIALIZE instance EvalBind Construct #-}
instance EvalBind Literal where {-# SPECIALIZE instance EvalBind Literal #-}
instance EvalBind Condition where {-# SPECIALIZE instance EvalBind Condition #-}
instance EvalBind Tuple where {-# SPECIALIZE instance EvalBind Tuple #-}
instance EvalBind Select where {-# SPECIALIZE instance EvalBind Select #-}
instance EvalBind Let where {-# SPECIALIZE instance EvalBind Let #-}

instance Monad m => EvalBind (MONAD m) where
  {-# SPECIALIZE instance Monad m => EvalBind (MONAD m) #-}

instance EvalBind Variable
  where
    {-# SPECIALIZE instance EvalBind Variable #-}
    {-# INLINABLE evalBindSym #-}
    evalBindSym (Variable v) _ = do
        env <- ask
        case lookup v env of
            Nothing -> return $ error "evalBind: evaluating free variable"
            Just a  -> case fromDyn a of
              Just b -> return b
              _      -> return $ error "evalBind: internal type error"

instance EvalBind Lambda
  where
    {-# SPECIALIZE instance EvalBind Lambda #-}
    {-# INLINABLE evalBindSym #-}
    evalBindSym lam@(Lambda v) (body :* Nil) = do
        env <- ask
        return
            $ \a -> flip runReader ((v, toDyn (funType lam) a):env)
            $ evalBindM body
      where
        funType :: Lambda (b :-> Full (a -> b)) -> P (a -> b)
        funType = const P



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
    {-# SPECIALIZE instance VarEqEnv [(VarId,VarId)] #-}
    {-# INLINABLE prjVarEqEnv #-}
    {-# INLINABLE modVarEqEnv #-}
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
    default alphaEqSym
        :: (AlphaEq dom dom dom env, Equality sub2, sub1 ~ sub2)
        => sub1 a
        -> Args (AST dom) a
        -> sub2 b
        -> Args (AST dom) b
        -> Reader env Bool
    alphaEqSym = alphaEqSymDefault
    {-# INLINABLE alphaEqSym #-}

instance (AlphaEq subA1 subB1 dom env, AlphaEq subA2 subB2 dom env) =>
    AlphaEq (subA1 :+: subA2) (subB1 :+: subB2) dom env
  where
    {-# SPECIALIZE instance
          (AlphaEq subA1 subB1 dom env, AlphaEq subA2 subB2 dom env) =>
            AlphaEq (subA1 :+: subA2) (subB1 :+: subB2) dom env #-}
    {-# INLINABLE alphaEqSym #-}
    alphaEqSym (InjL a) aArgs (InjL b) bArgs = alphaEqSym a aArgs b bArgs
    alphaEqSym (InjR a) aArgs (InjR b) bArgs = alphaEqSym a aArgs b bArgs
    alphaEqSym _ _ _ _ = return False

alphaEqM :: AlphaEq dom dom dom env =>
    ASTF dom a -> ASTF dom b -> Reader env Bool
alphaEqM a b = simpleMatch (alphaEqM2 b) a
{-# INLINABLE alphaEqM #-}

alphaEqM2 :: AlphaEq dom dom dom env =>
    ASTF dom b -> dom a -> Args (AST dom) a -> Reader env Bool
alphaEqM2 b a aArgs = simpleMatch (alphaEqSym a aArgs) b
{-# INLINABLE alphaEqM2 #-}

-- | Alpha-equivalence on lambda expressions. Free variables are taken to be
-- equivalent if they have the same identifier.
alphaEq :: AlphaEq dom dom dom [(VarId,VarId)] =>
    ASTF dom a -> ASTF dom b -> Bool
alphaEq a b = flip runReader ([] :: [(VarId,VarId)]) $ alphaEqM a b
{-# INLINABLE alphaEq #-}

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
{-# INLINABLE alphaEqSymDefault #-}

alphaEqChildren :: AlphaEq dom dom dom env =>
    AST dom a -> AST dom b -> Reader env Bool
alphaEqChildren (Sym _)  (Sym _)  = return True
alphaEqChildren (f :$ a) (g :$ b) = liftM2 (&&)
    (alphaEqChildren f g)
    (alphaEqM a b)
alphaEqChildren _ _ = return False
{-# INLINABLE alphaEqChildren #-}

instance AlphaEq sub sub dom env => AlphaEq (sub :| pred) (sub :| pred) dom env
  where
    {-# SPECIALIZE instance (AlphaEq sub sub dom env) =>
          AlphaEq (sub :| pred) (sub :| pred) dom env #-}
    {-# INLINABLE alphaEqSym #-}
    alphaEqSym (C a) aArgs (C b) bArgs = alphaEqSym a aArgs b bArgs

instance AlphaEq sub sub dom env => AlphaEq (sub :|| pred) (sub :|| pred) dom env
  where
    {-# SPECIALIZE instance (AlphaEq sub sub dom env) =>
          AlphaEq (sub :|| pred) (sub :|| pred) dom env #-}
    {-# INLINABLE alphaEqSym #-}
    alphaEqSym (C' a) aArgs (C' b) bArgs = alphaEqSym a aArgs b bArgs

instance AlphaEq sub sub dom env => AlphaEq (SubConstr1 c sub p) (SubConstr1 c sub p) dom env
  where
    {-# SPECIALIZE instance (AlphaEq sub sub dom env) =>
          AlphaEq (SubConstr1 c sub p) (SubConstr1 c sub p) dom env #-}
    {-# INLINABLE alphaEqSym #-}
    alphaEqSym (SubConstr1 a) aArgs (SubConstr1 b) bArgs = alphaEqSym a aArgs b bArgs

instance AlphaEq sub sub dom env =>
    AlphaEq (SubConstr2 c sub pa pb) (SubConstr2 c sub pa pb) dom env
  where
    {-# SPECIALIZE instance (AlphaEq sub sub dom env) =>
          AlphaEq (SubConstr2 c sub pa pb) (SubConstr2 c sub pa pb) dom env #-}
    {-# INLINABLE alphaEqSym #-}
    alphaEqSym (SubConstr2 a) aArgs (SubConstr2 b) bArgs = alphaEqSym a aArgs b bArgs

instance AlphaEq Empty Empty dom env
  where
    {-# SPECIALIZE instance AlphaEq Empty Empty dom env #-}
    alphaEqSym = error "Not implemented: alphaEqSym for Empty"

instance AlphaEq dom dom dom env => AlphaEq Condition Condition dom env where
  {-# SPECIALIZE instance AlphaEq dom dom dom env =>
        AlphaEq Condition Condition dom env #-}
instance AlphaEq dom dom dom env => AlphaEq Construct Construct dom env where
  {-# SPECIALIZE instance AlphaEq dom dom dom env =>
        AlphaEq Construct Construct dom env #-}
instance AlphaEq dom dom dom env => AlphaEq Identity  Identity  dom env where
  {-# SPECIALIZE instance AlphaEq dom dom dom env =>
        AlphaEq Identity Identity dom env #-}
instance AlphaEq dom dom dom env => AlphaEq Let       Let       dom env where
  {-# SPECIALIZE instance AlphaEq dom dom dom env =>
        AlphaEq Let Let dom env #-}
instance AlphaEq dom dom dom env => AlphaEq Literal   Literal   dom env where
  {-# SPECIALIZE instance AlphaEq dom dom dom env =>
        AlphaEq Literal Literal dom env #-}
instance AlphaEq dom dom dom env => AlphaEq Select    Select    dom env where
  {-# SPECIALIZE instance AlphaEq dom dom dom env =>
        AlphaEq Select Select dom env #-}
instance AlphaEq dom dom dom env => AlphaEq Tuple     Tuple     dom env where
  {-# SPECIALIZE instance AlphaEq dom dom dom env =>
        AlphaEq Tuple Tuple dom env #-}

instance AlphaEq sub sub dom env =>
    AlphaEq (Decor info sub) (Decor info sub) dom env
  where
    {-# SPECIALIZE instance (AlphaEq sub sub dom env) =>
          AlphaEq (Decor info sub) (Decor info sub) dom env #-}
    {-# INLINABLE alphaEqSym #-}
    alphaEqSym a aArgs b bArgs =
        alphaEqSym (decorExpr a) aArgs (decorExpr b) bArgs

instance (AlphaEq dom dom dom env, Monad m) => AlphaEq (MONAD m) (MONAD m) dom env
  where
    {-# SPECIALIZE instance (AlphaEq dom dom dom env, Monad m) =>
          AlphaEq (MONAD m) (MONAD m) dom env #-}

instance (AlphaEq dom dom dom env, VarEqEnv env) =>
    AlphaEq Variable Variable dom env
  where
    {-# SPECIALIZE instance (AlphaEq dom dom dom env, VarEqEnv env) =>
          AlphaEq Variable Variable dom env #-}
    {-# INLINABLE alphaEqSym #-}
    alphaEqSym (Variable v1) _ (Variable v2) _ = do
        env <- asks prjVarEqEnv
        case lookup v1 env of
          Nothing  -> return (v1==v2)   -- Free variables
          Just v2' -> return (v2==v2')

instance (AlphaEq dom dom dom env, VarEqEnv env) =>
    AlphaEq Lambda Lambda dom env
  where
    {-# SPECIALIZE instance (AlphaEq dom dom dom env, VarEqEnv env) =>
          AlphaEq Lambda Lambda dom env #-}
    {-# INLINABLE alphaEqSym #-}
    alphaEqSym (Lambda v1) (body1 :* Nil) (Lambda v2) (body2 :* Nil) =
        local (modVarEqEnv ((v1,v2):)) $ alphaEqM body1 body2
