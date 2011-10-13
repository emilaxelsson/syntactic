-- | Simple code motion transformation performing common sub-expression
-- elimination and variable hoisting. Note that the implementation is very
-- inefficient.
--
-- The code is based on an implementation by Gergely Dévai.

module Language.Syntactic.Sharing.SimpleCodeMotion
    ( codeMotion
    , reifySmart
    ) where



import Control.Monad.State
import Data.Set as Set
import Data.Typeable

import Data.Proxy

import Language.Syntactic
import Language.Syntactic.Constructs.Binding
import Language.Syntactic.Constructs.Binding.HigherOrder



-- | Substituting a sub-expression
substitute :: forall ctx dom a b
    .  ( Typeable a
       , Typeable b
       , Variable ctx :<: dom
       , Lambda ctx :<: dom
       , ExprEq dom
       )
    => Proxy ctx
    -> ASTF dom a  -- ^ Sub-expression to be replaced
    -> ASTF dom a  -- ^ Replacing sub-expression
    -> ASTF dom b  -- ^ Whole expression
    -> ASTF dom b
substitute ctx x y a = subst a
  where
    subst :: Typeable c => AST dom c -> AST dom c
    subst a | Just y' <- gcast y, alphaEq ctx x a = y'
    subst (f :$: a) = subst f :$: subst a
    subst a = a

-- | Count the number of occurrences of a sub-expression
count :: (Variable ctx :<: dom, Lambda ctx :<: dom, ExprEq dom)
    => Proxy ctx
    -> AST dom a  -- ^ Expression to count
    -> AST dom b  -- ^ Expression to count in
    -> VarId
count ctx a b
    | alphaEq ctx a b = 1
count ctx a (f :$: b) = count ctx a f + count ctx a b
count ctx a _         = 0

nonTerminal :: AST dom a -> Bool
nonTerminal (_ :$: _) = True
nonTerminal _         = False

data SomeAST ctx dom
  where
    SomeAST :: (Sat ctx a, Typeable a) => ASTF dom a -> SomeAST ctx dom

-- | Environment for the expression in the 'choose' function
data Env ctx dom = Env
    { context  :: Proxy ctx
    , inLambda :: Bool  -- ^ Whether the current expression is inside a lambda
    , counter  :: SomeAST ctx dom -> VarId
        -- ^ Counting the number of occurrences of an expression in the
        -- environment
    , dependencies :: Set VarId
        -- ^ The set of variables that are not allowed to occur in the chosen
        -- expression
    }

independent :: (Variable ctx :<: dom) => Env ctx dom -> AST dom a -> Bool
independent env (prjCtx (context env) -> Just (Variable v)) =
    not (v `member` dependencies env)
independent env (f :$: a) = independent env f && independent env a
independent _ _           = True

-- | Checks whether a sub-expression in a given environment can be lifted out
liftable :: (Variable ctx :<: dom, Lambda ctx :<: dom, Sat ctx a, Typeable a) =>
    Env ctx dom -> ASTF dom a -> Bool
liftable env a = independent env a && heuristic
    -- Lifting dependent expressions is semantically incorrect
  where
    heuristic = nonTerminal a && (inLambda env || (counter env (SomeAST a) > 1))

-- | Choose a sub-expression to share
choose :: forall ctx dom a
    .  ( Variable ctx :<: dom
       , Lambda ctx :<: dom
       , ExprEq dom
       , MaybeWitnessSat ctx dom
       , Typeable a
       )
    => ASTF dom a -> Maybe (SomeAST ctx dom)
choose a = chooseEnv env a
  where
    ctx = Proxy :: Proxy ctx

    env :: Env ctx dom
    env = Env
        { inLambda     = False
        , counter      = \(SomeAST b) -> count ctx b a
        , dependencies = empty
        , context      = ctx
        }

-- | Choose a sub-expression to share in an 'Env' environment
chooseEnv
    :: ( Variable ctx :<: dom
       , Lambda ctx :<: dom
       , MaybeWitnessSat ctx dom
       , Typeable a
       )
    => Env ctx dom -> ASTF dom a -> Maybe (SomeAST ctx dom)
chooseEnv env a
    | Just SatWit <- maybeWitnessSat (context env) a
    , liftable env a
    = Just (SomeAST a)
    | otherwise = chooseEnvSub env a

-- | Like 'chooseEnv', but does not consider the top expression for sharing
chooseEnvSub
    :: (Variable ctx :<: dom, Lambda ctx :<: dom, MaybeWitnessSat ctx dom)
    => Env ctx dom -> AST dom a -> Maybe (SomeAST ctx dom)
chooseEnvSub env ((prjCtx (context env) -> Just (Lambda v)) :$: a) =
    chooseEnv env' a
  where
    env' = env
        { inLambda     = True
        , dependencies = insert v (dependencies env)
        }
chooseEnvSub env (f :$: a) = chooseEnvSub env f `mplus` chooseEnv env a
chooseEnvSub _ _ = Nothing

-- | Perform common sub-expression elimination and variable hoisting
codeMotion :: forall ctx dom a
    .  ( Variable ctx :<: dom
       , Lambda ctx :<: dom
       , Let ctx ctx :<: dom
       , ExprEq dom
       , MaybeWitnessSat ctx dom
       , Typeable a
       )
    => Proxy ctx -> ASTF dom a -> State VarId (ASTF dom a)
codeMotion ctx a
    | Just SatWit <- maybeWitnessSat ctx a
    , Just b      <- choose a
    = share b
    | otherwise = descend ctx a
  where
    share :: Sat ctx a => SomeAST ctx dom -> State VarId (ASTF dom a)
    share (SomeAST b) = do
        b' <- codeMotion ctx b
        v  <- get; put (v+1)
        let x = inject (Variable v `withContext` ctx)
        body <- codeMotion ctx $ substitute ctx b x a
        return
            $   inject (letBind ctx)
            :$: b'
            :$: (inject (Lambda v `withContext` ctx) :$: body)

descend
    :: ( Variable ctx :<: dom
       , Lambda ctx :<: dom
       , Let ctx ctx :<: dom
       , ExprEq dom
       , MaybeWitnessSat ctx dom
       )
    => Proxy ctx -> AST dom a -> State VarId (AST dom a)
descend ctx (f :$: a) = liftM2 (:$:) (descend ctx f) (codeMotion ctx a)
descend _ a = return a

-- | Like 'reify' but with common sub-expression elimination and variable
-- hoisting
reifySmart
    :: ( Let ctx ctx :<: dom
       , ExprEq dom
       , MaybeWitnessSat ctx dom
       , Syntactic a (HODomain ctx dom)
       )
    => Proxy ctx
    -> a
    -> ASTF (Lambda ctx :+: Variable ctx :+: dom) (Internal a)
reifySmart ctx = flip evalState 0 . (codeMotion ctx <=< reifyM) . desugar

