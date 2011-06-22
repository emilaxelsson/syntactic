-- | General binding constructs

module Language.Syntactic.Features.Binding where



import Control.Monad.Reader
import Data.Dynamic
import Data.Ix
import Data.Tree

import Data.Hash

import Language.Syntactic



-- | Variable identifier
newtype VarId = VarId { varInteger :: Integer }
  deriving (Eq, Ord, Num, Enum, Ix)

instance Show VarId
  where
    show (VarId i) = show i

showVar :: VarId -> String
showVar v = "var" ++ show v



-- | Variables
data Variable a
  where
    Variable :: Typeable a => VarId -> Variable (Full a)

-- | Strict identifier comparison; i.e. no alpha equivalence
instance ExprEq Variable
  where
    exprEq (Variable v1) (Variable v2) = v1==v2

instance Render Variable
  where
    render (Variable v) = showVar v

instance ToTree Variable
  where
    toTreePart [] (Variable v) = Node ("var:" ++ show v) []



-- | Lambda binding
data Lambda a
  where
    Lambda :: (Typeable a, Typeable b) => VarId -> Lambda (b :-> Full (a -> b))

-- | Strict identifier comparison; i.e. no alpha equivalence
instance ExprEq Lambda
  where
    exprEq (Lambda v1) (Lambda v2) = v1==v2

instance Render Lambda
  where
    renderPart [body] (Lambda v) = "(\\" ++ showVar v ++ " -> "  ++ body ++ ")"

instance ToTree Lambda
  where
    toTreePart [body] (Lambda v) = Node ("Lambda " ++ show v) [body]



-- | Alpha-equivalence on 'Lambda' expressions. Free variables are taken to be
-- equvalent if they have the same identifier.
alphaEqM :: ExprEq dom
    => AST (Lambda :+: Variable :+: dom) a
    -> AST (Lambda :+: Variable :+: dom) b
    -> Reader [(VarId,VarId)] Bool

-- alphaEqM (project -> Just (Variable v1)) (project -> Just (Variable v2)) = do  -- Not accepted by GHC-6.12
alphaEqM (Symbol (InjectR (InjectL (Variable v1)))) (Symbol (InjectR (InjectL (Variable v2)))) = do
    env <- ask
    case lookup v1 env of
      Nothing  -> return (v1==v2)   -- Free variables
      Just v2' -> return (v2==v2')

alphaEqM
--     ((project -> Just (Lambda v1)) :$: a1)
--     ((project -> Just (Lambda v2)) :$: a2)  -- Not accepted by GHC-6.12
    (Symbol (InjectL (Lambda v1)) :$: a1)
    (Symbol (InjectL (Lambda v2)) :$: a2)
      = local ((v1,v2):) $ alphaEqM a1 a2

alphaEqM (f1 :$: a1) (f2 :$: a2) = do
    e <- alphaEqM f1 f2
    if e then alphaEqM a1 a2 else return False

alphaEqM
    (Symbol (InjectR (InjectR a)))
    (Symbol (InjectR (InjectR b)))
      = return (exprEq a b)

alphaEqM _ _ = return False



alphaEq :: ExprEq dom
    => AST (Lambda :+: Variable :+: dom) a
    -> AST (Lambda :+: Variable :+: dom) b
    -> Bool
alphaEq a b = runReader (alphaEqM a b) []



-- | Evaluation of possibly open 'LambdaAST' expressions
evalLambdaM :: (Eval dom, MonadReader [(VarId,Dynamic)] m) =>
    ASTF (Lambda :+: Variable :+: dom) a -> m a
evalLambdaM = liftM result . eval
  where
    eval :: (Eval dom, MonadReader [(VarId,Dynamic)] m) =>
        AST (Lambda :+: Variable :+: dom) a -> m a
--     eval (project -> Just (Variable v)) = do  -- Not accepted by GHC-6.12
    eval (Symbol (InjectR (InjectL (Variable v)))) = do
        env <- ask
        case lookup v env of
          Nothing -> return $ error "eval: evaluating free variable"
          Just a  -> case fromDynamic a of
            Just a -> return (Full a)
            _      -> return $ error "eval: internal type error"

--     eval ((project -> Just (Lambda v)) :$: body) = do  -- Not accepted by GHC-6.12
    eval (Symbol (InjectL (Lambda v)) :$: body) = do
        env <- ask
        return
            $ Full
            $ \a -> flip runReader ((v,toDyn a):env)
            $ liftM result
            $ eval body

    eval (f :$: a) = do
        f' <- eval f
        a' <- eval a
        return (f' $: result a')

    eval (Symbol (InjectR (InjectR a))) = return (evaluate a)



-- | Evaluation of closed 'Lambda' expressions
evalLambda :: Eval dom => ASTF (Lambda :+: Variable :+: dom) a -> a
evalLambda = flip runReader [] . evalLambdaM



-- | The class of n-ary binding functions
class NAry a dom | a -> dom
    -- Note: using a two-parameter class rather than an associated type, because
    -- this makes it possible to make a class alias constraining dom. GHC
    -- doesn't yet handle equality super classes.
  where
    type NAryEval a

    -- | N-ary binding by nested use of the supplied binder
    bindN
      :: (  forall b c . (Typeable b, Typeable c)
         => (ASTF dom b -> ASTF dom c)
         -> ASTF dom (b -> c)
         )
      -> a -> ASTF dom (NAryEval a)

instance NAry (ASTF dom a) dom
  where
    type NAryEval (ASTF dom a) = a
    bindN _ = id

instance (Typeable a, NAry b dom, Typeable (NAryEval b)) =>
    NAry (ASTF dom a -> b) dom
  where
    type NAryEval (ASTF dom a -> b) = a -> NAryEval b
    bindN lambda = lambda . (bindN lambda .)



-- | Let binding
data Let a
  where
    Let :: Let (a :-> (a -> b) :-> Full b)

instance ExprEq Let
  where
    exprEq Let Let = True

instance Render Let
  where
    renderPart []    Let = "Let"
    renderPart [f,a] Let = "(" ++ unwords ["letBind",f,a] ++ ")"

instance ToTree Let
  where
    toTreePart [a,body] Let = Node ("Let " ++ var) [a,body']
      where
        Node node [body'] = body
        var               = drop 7 node  -- Drop the "Lambda " prefix

instance Eval Let
  where
    evaluate Let = fromEval (flip ($))

instance ExprHash Let
  where
    exprHash Let = hashInt 0

