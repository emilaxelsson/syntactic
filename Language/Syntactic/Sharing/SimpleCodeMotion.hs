-- | Simple code motion transformation performing common sub-expression
-- elimination and variable hoisting. Note that the implementation is very
-- inefficient.
--
-- The code is based on an implementation by Gergely Dévai.

module Language.Syntactic.Sharing.SimpleCodeMotion
    ( BindDict (..)
    , codeMotion
    , bindDictFO
    , reifySmart
    , reifySmartFO
    ) where



import Control.Monad.State
import Data.Set as Set
import Data.Typeable

import Language.Syntactic
import Language.Syntactic.Constructs.Binding
import Language.Syntactic.Constructs.Binding.HigherOrder



-- | Interface for binding constructs
data BindDict dom pVar = BindDict
    { prjVariable :: forall sig . dom sig -> Maybe ((Variable :|| pVar) sig)
    , prjLambda   :: forall sig . dom sig -> Maybe ((ArgConstr Lambda pVar) sig)
    , injVariable :: forall a   . pVar a => ASTF dom a -> VarId -> dom (Full a)
    , injLambda   :: forall a b . pVar a => ASTF dom a -> ASTF dom b -> VarId -> dom (b :-> Full (a -> b))
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

-- | Function that decides whether a given symbol can be shared
type CanShare dom pVar =
    forall sig . dom sig -> Maybe (Dict (pVar (DenResult sig)))

-- | Environment for the expression in the 'choose' function
data Env dom = Env
    { inLambda :: Bool  -- ^ Whether the current expression is inside a lambda
    , counter  :: ASTE dom -> Int
        -- ^ Counting the number of occurrences of an expression in the
        -- environment
    , dependencies :: Set VarId
        -- ^ The set of variables that are not allowed to occur in the chosen
        -- expression
    }

independent ::
    CanShare dom pVar -> BindDict dom pVar -> Env dom -> AST dom a -> Bool
independent cs bd env (Sym (prjVariable bd -> Just (C' (Variable v)))) =
    not (v `member` dependencies env)
independent cs bd env (f :$ a) =
    independent cs bd env f && independent cs bd env a
independent _ _ _ _ = True

-- | Checks whether a sub-expression in a given environment can be lifted out
liftable ::
    CanShare dom pVar -> BindDict dom pVar -> Env dom -> ASTF dom a -> Bool
liftable cs bd env a = independent cs bd env a && heuristic
    -- Lifting dependent expressions is semantically incorrect
  where
    heuristic
        =  nonTerminal a
        && (inLambda env || (counter env (ASTE a) > 1))

-- | Choose a sub-expression to share
choose
    :: AlphaEq dom dom dom [(VarId,VarId)]
    => CanShare dom pVar
    -> BindDict dom pVar
    -> ASTF dom a
    -> Maybe (ASTB dom pVar)
choose cs bd a = chooseEnv cs bd env a
  where
    env = Env
        { inLambda     = False
        , counter      = \(ASTE b) -> count b a
        , dependencies = empty
        }

data Temp pVar a
  where
    Temp :: Maybe (Dict (pVar a)) -> Temp pVar (Full a)

-- | Choose a sub-expression to share in an 'Env' environment
chooseEnv :: forall dom pVar a
    .  CanShare dom pVar
    -> BindDict dom pVar
    -> Env dom
    -> ASTF dom a
    -> Maybe (ASTB dom pVar)
chooseEnv cs bd env a
    | Temp (Just Dict) :: Temp pVar (Full a) <- match (const . Temp . cs) a
    , liftable cs bd env a
    = Just (ASTB a)
chooseEnv cs bd env a = chooseEnvSub cs bd env a

-- | Like 'chooseEnv', but does not consider the top expression for sharing
chooseEnvSub
    :: CanShare dom pVar
    -> BindDict dom pVar
    -> Env dom
    -> AST dom a
    -> Maybe (ASTB dom pVar)
chooseEnvSub cs bd env (Sym lam :$ a)
    | Just (ArgConstr (Lambda v)) <- prjLambda bd lam
    = chooseEnv cs bd (env' v) a
  where
    env' v = env
        { inLambda     = True
        , dependencies = insert v (dependencies env)
        }
chooseEnvSub cs bd env (f :$ a) =
    chooseEnvSub cs bd env f `mplus` chooseEnv cs bd env a
chooseEnvSub _ _ _ _ = Nothing



-- | Perform common sub-expression elimination and variable hoisting
codeMotion :: forall dom pVar a
    .  ( ConstrainedBy dom Typeable
       , AlphaEq dom dom dom [(VarId,VarId)]
       )
    => BindDict dom pVar
    -> (forall sig . dom sig -> Maybe (Dict (pVar (DenResult sig))))
    -> ASTF dom a
    -> State VarId (ASTF dom a)
codeMotion bd cs a
    | Just b <- choose cs bd a = share b
    | otherwise                = descend a
  where
    share (ASTB b) = do
        b' <- codeMotion bd cs b
        v  <- get; put (v+1)
        let x = Sym (injVariable bd b v)
        body <- codeMotion bd cs $ substitute b x a
        return
            $  Sym (injLet bd body)
            :$ b'
            :$ (Sym (injLambda bd b' body v) :$ body)

    descend :: AST dom b -> State VarId (AST dom b)
    descend (f :$ a) = liftM2 (:$) (descend f) (codeMotion bd cs a)
    descend a        = return a



defaultBindDict
    :: (Variable :<: dom, Lambda :<: dom, Let :<: dom, Constrained dom)
    => BindDict (dom :|| Typeable) Top
defaultBindDict = BindDict
    { prjVariable = fmap C' . prj

    , prjLambda = \a -> do
        lam@(Lambda _) <- prj a
        return (ArgConstr lam)

    , injVariable = \ref v -> case exprDict ref of
        Dict -> C' $ inj (Variable v)
    , injLambda = \refa refb v -> case (exprDict refa, exprDict refb) of
        (Dict, Dict) -> C' $ inj (Lambda v)
    , injLet = \ref -> case exprDict ref of
        Dict -> C' $ inj Let
    }



bindDictFO
    :: (Let :<: dom)
    => BindDict (FODomain dom Typeable Top) Top
bindDictFO = BindDict
    { prjVariable = prj
    , prjLambda   = prj
    , injVariable = \ref v -> case exprDict ref of
        Dict -> injC (constr' pTop (Variable v))
    , injLambda = \refa refb v -> case (exprDict refa, exprDict refb) of
        (Dict, Dict) -> injC $ argConstr pTop $ Lambda v
    , injLet = \ref -> case exprDict ref of
        Dict -> C' $ inj Let
    }



-- TODO Abstract away from Typeable?

-- | Like 'reify' but with common sub-expression elimination and variable
-- hoisting
reifySmart :: forall dom a
    .  ( AlphaEq dom dom (FODomain dom Typeable Top) [(VarId,VarId)]
       , Syntactic a (HODomain dom Typeable Top)
       )
    => BindDict (FODomain dom Typeable Top) Top
    -> (forall sig . FODomain dom Typeable Top sig -> Bool)
    -> a
    -> ASTF (FODomain dom Typeable Top) (Internal a)
reifySmart dict cs = flip evalState 0 .
    (codeMotion dict cs' <=< reifyM . desugar)
  where
    cs' :: FODomain dom Typeable Top sig -> Maybe (Dict (Top (DenResult sig)))
    cs' a = if cs a then Just Dict else Nothing

reifySmartFO
  :: ( Let :<: dom
     , Syntactic a (HODomain dom Typeable Top)
     , AlphaEq dom dom (FODomain dom Typeable Top) [(VarId, VarId)]
     )
  => (forall sig . FODomain dom Typeable Top sig -> Bool)
  -> a
  -> ASTF (FODomain dom Typeable Top) (Internal a)
reifySmartFO = reifySmart bindDictFO

