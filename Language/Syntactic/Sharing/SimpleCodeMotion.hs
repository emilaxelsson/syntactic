-- | Simple code motion transformation performing common sub-expression
-- elimination and variable hoisting. Note that the implementation is very
-- inefficient.
--
-- The code is based on an implementation by Gergely Dévai.

module Language.Syntactic.Sharing.SimpleCodeMotion
    ( BindDict (..)
    , codeMotion
    , defaultBindDict
    , reifySmart
    ) where



import Control.Monad.State
import Data.Set as Set
import Data.Typeable

import Data.Proxy

import Language.Syntactic
import Language.Syntactic.Constructs.Binding
import Language.Syntactic.Constructs.Binding.HigherOrder



-- | Interface for binding constructs
data BindDict ctx dom = BindDict
    { prjVariable :: forall a   . dom a -> Maybe VarId
    , prjLambda   :: forall a   . dom a -> Maybe VarId
    , injVariable :: forall a   . (Sat ctx a, Typeable a)            => ASTF dom a -> VarId -> dom (Full a)
    , injLambda   :: forall a b . (Sat ctx a, Typeable a, Sat ctx b) => ASTF dom b -> VarId -> dom (b :-> Full (a -> b))
    , injLet      :: forall a b . (Sat ctx a, Sat ctx b)             => ASTF dom b -> dom (a :-> (a -> b) :-> Full b)
    }
  -- TODO `injLambda` has more constraints than the `Lambda` constructor. This
  --      is demanded by the Feldspar implementation. One way to make things
  --      more consistent would be to add an extra `ctx` parameter to `Lambda`
  --      (like `Let`).

-- | Substituting a sub-expression. Assumes no variable capturing in the
-- expressions involved.
substitute :: forall dom a b
    .  (Typeable a, Typeable b, AlphaEq dom dom dom [(VarId,VarId)])
    => ASTF dom a  -- ^ Sub-expression to be replaced
    -> ASTF dom a  -- ^ Replacing sub-expression
    -> ASTF dom b  -- ^ Whole expression
    -> ASTF dom b
substitute x y a
    | Just y' <- gcast y, alphaEq x a = y'
    | otherwise = subst a
  where
    subst :: Typeable c => AST dom c -> AST dom c
    subst (f :$ a) = subst f :$ substitute x y a
    subst a = a

-- | Count the number of occurrences of a sub-expression
count :: forall dom a b . AlphaEq dom dom dom [(VarId,VarId)]
    => ASTF dom a  -- ^ Expression to count
    -> ASTF dom b  -- ^ Expression to count in
    -> Int
count a b
    | alphaEq a b = 1
    | otherwise   = cnt b
  where
    cnt :: AST dom c -> Int
    cnt (f :$ b) = cnt f + count a b
    cnt _        = 0

nonTerminal :: AST dom a -> Bool
nonTerminal (_ :$ _) = True
nonTerminal _        = False

data SomeAST ctx dom
  where
    SomeAST :: (Sat ctx a, Typeable a) => ASTF dom a -> SomeAST ctx dom

-- | Environment for the expression in the 'choose' function
data Env ctx dom = Env
    { inLambda :: Bool  -- ^ Whether the current expression is inside a lambda
    , canShare :: forall a . dom a -> Bool
        -- ^ Whether a given symbol can be shared
    , counter  :: SomeAST ctx dom -> Int
        -- ^ Counting the number of occurrences of an expression in the
        -- environment
    , dependencies :: Set VarId
        -- ^ The set of variables that are not allowed to occur in the chosen
        -- expression
    }

independent :: BindDict ctx dom -> Env ctx dom -> AST dom a -> Bool
independent bindDict env (Sym (prjVariable bindDict -> Just v)) =
    not (v `member` dependencies env)
independent bindDict env (f :$ a) =
    independent bindDict env f && independent bindDict env a
independent _ _ _ = True

-- | Checks whether a sub-expression in a given environment can be lifted out
liftable :: (Sat ctx a, Typeable a) =>
    BindDict ctx dom -> Env ctx dom -> ASTF dom a -> Bool
liftable bindDict env a = independent bindDict env a && heuristic
    -- Lifting dependent expressions is semantically incorrect
  where
    heuristic
        =  queryNodeSimple (const . canShare env) a
        && nonTerminal a
        && (inLambda env || (counter env (SomeAST a) > 1))

-- | Choose a sub-expression to share
choose
    :: ( AlphaEq dom dom dom [(VarId,VarId)]
       , MaybeWitnessSat ctx dom
       , Typeable a
       )
    => BindDict ctx dom
    -> (forall a . dom a -> Bool)
    -> ASTF dom a
    -> Maybe (SomeAST ctx dom)
choose bindDict canShr a = chooseEnv bindDict env a
  where
    env = Env
        { inLambda     = False
        , canShare     = canShr
        , counter      = \(SomeAST b) -> count b a
        , dependencies = empty
        }

-- | Choose a sub-expression to share in an 'Env' environment
chooseEnv :: forall ctx dom a . (MaybeWitnessSat ctx dom, Typeable a) =>
    BindDict ctx dom -> Env ctx dom -> ASTF dom a -> Maybe (SomeAST ctx dom)
chooseEnv bindDict env a
    | Just SatWit <- maybeWitnessSat (Proxy :: Proxy ctx) a
    , liftable bindDict env a
    = Just (SomeAST a)
    | otherwise = chooseEnvSub bindDict env a

-- | Like 'chooseEnv', but does not consider the top expression for sharing
chooseEnvSub :: MaybeWitnessSat ctx dom =>
    BindDict ctx dom -> Env ctx dom -> AST dom a -> Maybe (SomeAST ctx dom)
chooseEnvSub bindDict env (Sym (prjLambda bindDict -> Just v) :$ a) =
    chooseEnv bindDict env' a
  where
    env' = env
        { inLambda     = True
        , dependencies = insert v (dependencies env)
        }
chooseEnvSub bindDict env (f :$ a) =
    chooseEnvSub bindDict env f `mplus` chooseEnv bindDict env a
chooseEnvSub _ _ _ = Nothing



-- | Perform common sub-expression elimination and variable hoisting
codeMotion :: forall ctx dom a
    .  ( AlphaEq dom dom dom [(VarId,VarId)]
       , MaybeWitnessSat ctx dom
       , Typeable a
       )
    => BindDict ctx dom
    -> (forall a . dom a -> Bool)
    -> ASTF dom a
    -> State VarId (ASTF dom a)
codeMotion bindDict canShr a
    | Just SatWit <- maybeWitnessSat ctx a
    , Just b      <- choose bindDict canShr a
    = share b
    | otherwise = descend a
  where
    ctx = Proxy :: Proxy ctx

    share :: Sat ctx a => SomeAST ctx dom -> State VarId (ASTF dom a)
    share (SomeAST b) = do
        b' <- codeMotion bindDict canShr b
        v  <- get; put (v+1)
        let x = Sym (injVariable bindDict b v)
        body <- codeMotion bindDict canShr $ substitute b x a
        return
            $  Sym (injLet bindDict body)
            :$ b'
            :$ (Sym (injLambda bindDict body v) :$ body)

    descend :: AST dom b -> State VarId (AST dom b)
    descend (f :$ a) = liftM2 (:$) (descend f) (codeMotion bindDict canShr a)
    descend a = return a



defaultBindDict :: forall ctx dom
    .  ( Variable ctx :<: dom
       , Lambda ctx   :<: dom
       , Let ctx ctx  :<: dom
       )
    => BindDict ctx dom
defaultBindDict = BindDict
    { prjVariable = \a -> do
        Variable v <- prjCtx ctx a
        return v

    , prjLambda = \a -> do
        Lambda v <- prjCtx ctx a
        return v

    , injVariable = \_ v -> inj (Variable v `withContext` ctx)
    , injLambda   = \_ v -> inj (Lambda   v `withContext` ctx)
    , injLet      = \_   -> inj (letBind ctx)
    }
  where
    ctx = Proxy :: Proxy ctx



-- | Like 'reify' but with common sub-expression elimination and variable
-- hoisting
reifySmart :: forall ctx dom a
    .  ( Let ctx ctx :<: dom
       , AlphaEq dom dom (Lambda ctx :+: Variable ctx :+: dom) [(VarId,VarId)]
       , MaybeWitnessSat ctx dom
       , Syntactic a (HODomain ctx dom)
       )
    => (forall a . (Lambda ctx :+: Variable ctx :+: dom) a -> Bool)
    -> a
    -> ASTF (Lambda ctx :+: Variable ctx :+: dom) (Internal a)
reifySmart canShr = flip evalState 0 .
    (codeMotion dict canShr <=< reifyM . desugar)
  where
    dict = defaultBindDict :: BindDict ctx (Lambda ctx :+: Variable ctx :+: dom)

