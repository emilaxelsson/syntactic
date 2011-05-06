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

instance Render Lambda
  where
    renderPart [body] (Lambda v) = "(\\" ++ showVar v ++ " -> "  ++ body ++ ")"

instance ToTree Lambda
  where
    toTreePart [body] (Lambda v) = Node ("Lambda " ++ show v) [body]



-- | Alpha-equivalence on 'Lambda' expressions. Free variables are taken to be
-- equvalent if they have the same identifier.
eqLambda :: ExprEq dom
    => AST (Lambda :+: Variable :+: dom) a
    -> AST (Lambda :+: Variable :+: dom) b
    -> Reader [(VarId,VarId)] Bool

eqLambda (project -> Just (Variable v1)) (project -> Just (Variable v2)) = do
    env <- ask
    case lookup v1 env of
      Nothing  -> return (v1==v2)   -- Free variables
      Just v2' -> return (v2==v2')

eqLambda
    ((project -> Just (Lambda v1)) :$: a1)
    ((project -> Just (Lambda v2)) :$: a2)
      = local ((v1,v2):) $ eqLambda a1 a2

eqLambda (f1 :$: a1) (f2 :$: a2) = do
    e <- eqLambda f1 f2
    if e then eqLambda a1 a2 else return False

eqLambda
    (Symbol (InjectR (InjectR a)))
    (Symbol (InjectR (InjectR b)))
      = return (exprEq a b)

eqLambda _ _ = return False



-- | Evaluation of possibly open 'LambdaAST' expressions
evalLambdaM :: (Eval dom, MonadReader [(VarId,Dynamic)] m) =>
    AST (Lambda :+: Variable :+: dom) (Full a) -> m a
evalLambdaM = liftM result . eval
  where
    eval :: (Eval dom, MonadReader [(VarId,Dynamic)] m) =>
        AST (Lambda :+: Variable :+: dom) a -> m a
    eval (project -> Just (Variable v)) = do
        env <- ask
        case lookup v env of
          Nothing -> return $ error "eval: evaluating free variable"
          Just a  -> case fromDynamic a of
            Just a -> return (Full a)
            _      -> return $ error "eval: internal type error"

    eval ((project -> Just (Lambda v)) :$: body) = do
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
evalLambda :: Eval dom => AST (Lambda :+: Variable :+: dom) (Full a) -> a
evalLambda = flip runReader [] . evalLambdaM



-- | The class of n-ary binding functions
class NAry a
  where
    type NAryEval a
    type NAryDom  a :: * -> *

    -- | N-ary binding by nested use of the supplied binder
    bindN
      :: (  forall b c . (Typeable b, Typeable c)
         => (AST (NAryDom a) (Full b) -> AST (NAryDom a) (Full c))
         -> AST (NAryDom a) (Full (b -> c))
         )
      -> a -> AST (NAryDom a) (Full (NAryEval a))

instance NAry (AST dom (Full a))
  where
    type NAryEval (AST dom (Full a)) = a
    type NAryDom  (AST dom (Full a)) = dom
    bindN _ = id

instance
    ( Typeable a
    , NAry b
    , Typeable (NAryEval b)
    , NAryDom b ~ dom
    ) =>
      NAry (AST dom (Full a) -> b)
  where
    type NAryEval (AST dom (Full a) -> b) = a -> NAryEval b
    type NAryDom  (AST dom (Full a) -> b) = dom
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
    render Let = "Let"

instance ToTree Let
  where
    toTreePart [a,body] Let = Node ("Let " ++ var) [a,body']
      where
        Node node [body'] = body
        var               = drop 7 node  -- Drop the "Lambda " prefix

instance Eval Let
  where
    evaluate Let = consEval (flip ($))

instance ExprHash Let
  where
    exprHash Let = hashInt 0

