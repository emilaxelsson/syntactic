-- | Simple code motion transformation performing common sub-expression elimination and variable
-- hoisting. Note that the implementation is very inefficient.
--
-- The code is based on an implementation by Gergely Dévai.

module Language.Syntactic.Sharing.SimpleCodeMotion
    ( PrjDict (..)
    , InjDict (..)
    , MkInjDict
    , codeMotion
    , prjDictFO
    , reifySmart
    , mkInjDictFO
    ) where



import Control.Monad.State
import Data.Set as Set
import Data.Typeable

import Language.Syntactic
import Language.Syntactic.Constructs.Binding
import Language.Syntactic.Constructs.Binding.HigherOrder



-- | Interface for projecting binding constructs
data PrjDict dom = PrjDict
    { prjVariable :: forall sig . dom sig -> Maybe VarId
    , prjLambda   :: forall sig . dom sig -> Maybe VarId
    }

-- | Interface for injecting binding constructs
data InjDict dom a b = InjDict
    { injVariable :: VarId -> dom (Full a)
    , injLambda   :: VarId -> dom (b :-> Full (a -> b))
    , injLet      :: dom (a :-> (a -> b) :-> Full b)
    }

-- | A function that, if possible, returns an 'InjDict' for sharing a specific sub-expression. The
-- first argument is the expression to be shared, and the second argument the expression in which it
-- will be shared.
--
-- This function makes the caller of 'codeMotion' responsible for making sure that the necessary
-- type constraints are fulfilled (otherwise 'Nothing' is returned). It also makes it possible to
-- transfer information, e.g. from the shared expression to the introduced variable.
type MkInjDict dom = forall a b . ASTF dom a -> ASTF dom b -> Maybe (InjDict dom a b)



-- | Substituting a sub-expression. Assumes no variable capturing in the
-- expressions involved.
substitute :: forall dom a b
    .  (ConstrainedBy dom Typeable, AlphaEq dom dom dom [(VarId,VarId)])
    => ASTF dom a  -- ^ Sub-expression to be replaced
    -> ASTF dom a  -- ^ Replacing sub-expression
    -> ASTF dom b  -- ^ Whole expression
    -> ASTF dom b
substitute x y a
    | Dict <- exprDictSub pTypeable y
    , Dict <- exprDictSub pTypeable a
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
    , counter  :: ASTE dom -> Int
        -- ^ Counting the number of occurrences of an expression in the
        -- environment
    , dependencies :: Set VarId
        -- ^ The set of variables that are not allowed to occur in the chosen
        -- expression
    }

independent :: PrjDict dom -> Env dom -> AST dom a -> Bool
independent pd env (Sym (prjVariable pd -> Just v)) = not (v `member` dependencies env)
independent pd env (f :$ a) = independent pd env f && independent pd env a
independent _ _ _ = True

-- | Checks whether a sub-expression in a given environment can be lifted out
liftable :: PrjDict dom -> Env dom -> ASTF dom a -> Bool
liftable pd env a = independent pd env a && heuristic
    -- Lifting dependent expressions is semantically incorrect
  where
    heuristic =  nonTerminal a && (inLambda env || (counter env (ASTE a) > 1))



-- | A sub-expression chosen to be shared together with an evidence that it can actually be shared
-- in the whole expression under consideration
data Chosen dom a
  where
    Chosen :: InjDict dom b a -> ASTF dom b -> Chosen dom a

-- | Choose a sub-expression to share
choose :: forall dom a
    .  (AlphaEq dom dom dom [(VarId,VarId)])
    => PrjDict dom
    -> MkInjDict dom
    -> ASTF dom a
    -> Maybe (Chosen dom a)
choose pd mkId a = chooseEnv initEnv a
  where
    initEnv = Env
        { inLambda     = False
        , counter      = \(ASTE b) -> count b a
        , dependencies = empty
        }

    chooseEnv :: Env dom -> ASTF dom b -> Maybe (Chosen dom a)
    chooseEnv env b
        | liftable pd env b = do
            id <- mkId b a
            return $ Chosen id b
    chooseEnv env b = chooseEnvSub env b

    -- | Like 'chooseEnv', but does not consider the top expression for sharing
    chooseEnvSub :: Env dom -> AST dom b -> Maybe (Chosen dom a)
    chooseEnvSub env (Sym lam :$ b)
        | Just v <- prjLambda pd lam
        = chooseEnv (env' v) b
      where
        env' v = env
            { inLambda     = True
            , dependencies = insert v (dependencies env)
            }
    chooseEnvSub env (s :$ b) = chooseEnvSub env s `mplus` chooseEnv env b
    chooseEnvSub _ _ = Nothing



-- | Perform common sub-expression elimination and variable hoisting
codeMotion :: forall dom a
    .  ( ConstrainedBy dom Typeable
       , AlphaEq dom dom dom [(VarId,VarId)]
       )
    => PrjDict dom
    -> MkInjDict dom
    -> ASTF dom a
    -> State VarId (ASTF dom a)
codeMotion pd mkId a
    | Just (Chosen id b) <- choose pd mkId a = share id b
    | otherwise = descend a
  where
    share :: InjDict dom b a -> ASTF dom b -> State VarId (ASTF dom a)
    share id b = do
        b' <- codeMotion pd mkId b
        v  <- get; put (v+1)
        let x = Sym (injVariable id v)
        body <- codeMotion pd mkId $ substitute b x a
        return
            $  Sym (injLet id)
            :$ b'
            :$ (Sym (injLambda id v) :$ body)

    descend :: AST dom b -> State VarId (AST dom b)
    descend (f :$ a) = liftM2 (:$) (descend f) (codeMotion pd mkId a)
    descend a        = return a



-- | A 'PrjDict' implementation for 'FODomain'
prjDictFO :: forall dom p pVar . PrjDict (FODomain dom p pVar)
prjDictFO = PrjDict
    { prjVariable = fmap (\(C' (Variable v)) -> v)       . prjP (P::P (Variable :|| pVar))
    , prjLambda   = fmap (\(SubConstr2 (Lambda v)) -> v) . prjP (P::P (CLambda pVar))
    }

-- | Like 'reify' but with common sub-expression elimination and variable hoisting
reifySmart :: forall dom p pVar a
    .  ( AlphaEq dom dom (FODomain dom p pVar) [(VarId,VarId)]
       , Syntactic a
       , Domain a ~ HODomain dom p pVar
       , p :< Typeable
       )
    => MkInjDict (FODomain dom p pVar)
    -> a
    -> ASTF (FODomain dom p pVar) (Internal a)
reifySmart mkId = flip evalState 0 . (codeMotion prjDictFO mkId <=< reifyM . desugar)



-- | An 'MkInjDict' implementation for 'FODomain'
--
-- The supplied function determines whether or not an expression can be shared by returning a
-- witness that the type of the expression satisfies the predicate @pVar@.
mkInjDictFO :: forall dom pVar . (Let :<: dom)
    => (forall a . ASTF (FODomain dom Typeable pVar) a -> Maybe (Dict (pVar a)))
    -> MkInjDict (FODomain dom Typeable pVar)
mkInjDictFO canShare a b
    | Dict <- exprDict a
    , Dict <- exprDict b
    , Just Dict <- canShare a
    = Just $ InjDict
        { injVariable = \v -> injC (symType pVar $ C' (Variable v))
        , injLambda   = \v -> injC (symType pLam $ SubConstr2 (Lambda v))
        , injLet      = C' $ inj Let
        }
  where
    pVar = P::P (Variable :|| pVar)
    pLam = P::P (CLambda pVar)
mkInjDictFO _ _ _ = Nothing

