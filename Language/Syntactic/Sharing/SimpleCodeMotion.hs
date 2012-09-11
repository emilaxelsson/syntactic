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
    , reifySmartDefault
    ) where



import Control.Monad.State
import Data.Set as Set
import Data.Typeable

import Language.Syntactic
import Language.Syntactic.Constructs.Binding
import Language.Syntactic.Constructs.Binding.HigherOrder



-- | Interface for binding constructs
data BindDict dom = BindDict
    { prjVariable :: forall a   . dom a -> Maybe VarId
    , prjLambda   :: forall a   . dom a -> Maybe VarId
    , injVariable :: forall a   . ASTF dom a -> VarId -> dom (Full a)
    , injLambda   :: forall a b . ASTF dom a -> ASTF dom b -> VarId -> dom (b :-> Full (a -> b))
    , injLet      :: forall a b . ASTF dom b -> dom (a :-> (a -> b) :-> Full b)
    }

-- | Substituting a sub-expression. Assumes no variable capturing in the
-- expressions involved.
substitute :: forall dom a b
    .  (ConstrainedBy dom Typeable, AlphaEq dom dom dom [(VarId,VarId)])
    => ASTF dom a  -- ^ Sub-expression to be replaced
    -> ASTF dom a  -- ^ Replacing sub-expression
    -> ASTF dom b  -- ^ Whole expression
    -> ASTF dom b
substitute x y a
    | Dict :: Dict (Typeable a) <- exprDictSub y
    , Dict :: Dict (Typeable b) <- exprDictSub a
    , Just y' <- gcast y, alphaEq x a = y'
    | otherwise = subst a
  where
    subst :: AST dom c -> AST dom c
    subst (f :$ a) = subst f :$ substitute x y a
    subst a = a

-- | Count the number of occurrences of a sub-expression
count :: forall dom a b
    .  AlphaEq dom dom dom [(VarId,VarId)]
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

-- | Environment for the expression in the 'choose' function
data Env dom = Env
    { inLambda :: Bool  -- ^ Whether the current expression is inside a lambda
    , canShare :: forall a . dom a -> Bool
        -- ^ Whether a given symbol can be shared
    , counter  :: ASTE dom -> Int
        -- ^ Counting the number of occurrences of an expression in the
        -- environment
    , dependencies :: Set VarId
        -- ^ The set of variables that are not allowed to occur in the chosen
        -- expression
    }

independent :: BindDict dom -> Env dom -> AST dom a -> Bool
independent bindDict env (Sym (prjVariable bindDict -> Just v)) =
    not (v `member` dependencies env)
independent bindDict env (f :$ a) =
    independent bindDict env f && independent bindDict env a
independent _ _ _ = True

-- | Checks whether a sub-expression in a given environment can be lifted out
liftable :: BindDict dom -> Env dom -> ASTF dom a -> Bool
liftable bindDict env a = independent bindDict env a && heuristic
    -- Lifting dependent expressions is semantically incorrect
  where
    heuristic
        =  simpleMatch (const . canShare env) a
        && nonTerminal a
        && (inLambda env || (counter env (ASTE a) > 1))

-- | Choose a sub-expression to share
choose
    :: AlphaEq dom dom dom [(VarId,VarId)]
    => BindDict dom
    -> (forall a . dom a -> Bool)
    -> ASTF dom a
    -> Maybe (ASTE dom)
choose bindDict canShr a = chooseEnv bindDict env a
  where
    env = Env
        { inLambda     = False
        , canShare     = canShr
        , counter      = \(ASTE b) -> count b a
        , dependencies = empty
        }

-- | Choose a sub-expression to share in an 'Env' environment
chooseEnv :: BindDict dom -> Env dom -> ASTF dom a -> Maybe (ASTE dom)
chooseEnv bindDict env a
    | liftable bindDict env a = Just (ASTE a)
    | otherwise               = chooseEnvSub bindDict env a

-- | Like 'chooseEnv', but does not consider the top expression for sharing
chooseEnvSub :: BindDict dom -> Env dom -> AST dom a -> Maybe (ASTE dom)
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
codeMotion :: forall dom a
    .  ( ConstrainedBy dom Typeable
       , AlphaEq dom dom dom [(VarId,VarId)]
       )
    => BindDict dom
    -> (forall a . dom a -> Bool)
    -> ASTF dom a
    -> State VarId (ASTF dom a)
codeMotion bindDict canShr a
    | Just b <- choose bindDict canShr a = share b
    | otherwise                          = descend a
  where
    share (ASTE b) = do
        b' <- codeMotion bindDict canShr b
        v  <- get; put (v+1)
        let x = Sym (injVariable bindDict b v)
        body <- codeMotion bindDict canShr $ substitute b x a
        return
            $  Sym (injLet bindDict body)
            :$ b'
            :$ (Sym (injLambda bindDict b' body v) :$ body)

    descend :: AST dom b -> State VarId (AST dom b)
    descend (f :$ a) = liftM2 (:$) (descend f) (codeMotion bindDict canShr a)
    descend a        = return a



defaultBindDict
    :: (Variable :<: dom, Lambda :<: dom, Let :<: dom, Constrained dom)
    => BindDict (dom :|| Typeable)
defaultBindDict = BindDict
    { prjVariable = \a -> do
        Variable v <- prj a
        return v

    , prjLambda = \a -> do
        Lambda v <- prj a
        return v

    , injVariable = \ref v -> case exprDict ref of
        Dict -> C' $ inj (Variable v)
    , injLambda = \refa refb v -> case (exprDict refa, exprDict refb) of
        (Dict, Dict) -> C' $ inj (Lambda v)
    , injLet = \ref -> case exprDict ref of
        Dict -> C' $ inj Let
    }



-- TODO Abstract away from Typeable?

-- | Like 'reify' but with common sub-expression elimination and variable
-- hoisting
reifySmart
    :: ( AlphaEq dom dom ((Lambda :+: Variable :+: dom) :|| Typeable) [(VarId,VarId)]
       , Syntactic a (HODomain dom Typeable)
       )
    => BindDict ((Lambda :+: Variable :+: dom) :|| Typeable)
    -> (forall a . ((Lambda :+: Variable :+: dom) :|| Typeable) a -> Bool)
    -> a
    -> ASTF ((Lambda :+: Variable :+: dom) :|| Typeable) (Internal a)
reifySmart dict canShr = flip evalState 0 .
    (codeMotion dict canShr <=< reifyM . desugar)

reifySmartDefault
    :: ( Let :<: dom
       , AlphaEq dom dom ((Lambda :+: Variable :+: dom) :|| Typeable) [(VarId,VarId)]
       , Syntactic a (HODomain dom Typeable)
       )
    => (forall a . ((Lambda :+: Variable :+: dom) :|| Typeable) a -> Bool)
    -> a
    -> ASTF ((Lambda :+: Variable :+: dom) :|| Typeable) (Internal a)
reifySmartDefault = reifySmart defaultBindDict

