-- | General binding constructs

module Language.Syntactic.Features.Binding where



import Control.Monad.Reader
import Data.Dynamic
import Data.Ix
import Data.Tree

import Data.Hash
import Data.Proxy

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
data Variable ctx a
  where
    Variable :: (Typeable a, Sat ctx a) =>
        Proxy ctx -> VarId -> Variable ctx (Full a)
      -- 'Typeable' needed by the dynamic types in 'evalLambda'.

instance WitnessCons (Variable ctx)
  where
    witnessCons (Variable _ _) = ConsWit

-- | Strict identifier comparison; i.e. no alpha equivalence
instance ExprEq (Variable ctx)
  where
    exprEq (Variable _ v1) (Variable _ v2) = v1==v2

instance Render (Variable ctx)
  where
    render (Variable _ v) = showVar v

instance ToTree (Variable ctx)
  where
    toTreePart [] (Variable _ v) = Node ("var:" ++ show v) []

-- | Partial `Variable` projection with explicit context
prjVariable :: (Variable ctx :<: sup) =>
    Proxy ctx -> sup a -> Maybe (Variable ctx a)
prjVariable _ = project



-- | Lambda binding
data Lambda ctx a
  where
    Lambda :: (Typeable a, Sat ctx a) =>
        Proxy ctx -> VarId -> Lambda ctx (b :-> Full (a -> b))
      -- 'Typeable' needed by the dynamic types in 'evalLambda'.

instance WitnessCons (Lambda ctx)
  where
    witnessCons (Lambda _ _) = ConsWit

-- | Strict identifier comparison; i.e. no alpha equivalence
instance ExprEq (Lambda ctx)
  where
    exprEq (Lambda _ v1) (Lambda _ v2) = v1==v2

instance Render (Lambda ctx)
  where
    renderPart [body] (Lambda _ v) =
        "(\\" ++ showVar v ++ " -> "  ++ body ++ ")"

instance ToTree (Lambda ctx)
  where
    toTreePart [body] (Lambda _ v) = Node ("Lambda " ++ show v) [body]

-- | Partial `Lambda` projection with explicit context
prjLambda :: (Lambda ctx :<: sup) => Proxy ctx -> sup a -> Maybe (Lambda ctx a)
prjLambda _ = project



-- | Alpha-equivalence on 'Lambda' expressions. Free variables are taken to be
-- equvalent if they have the same identifier.
alphaEqM :: ExprEq dom
    => AST (Lambda ctx :+: Variable ctx :+: dom) a
    -> AST (Lambda ctx :+: Variable ctx :+: dom) b
    -> Reader [(VarId,VarId)] Bool

alphaEqM
    (Symbol (InjectR (InjectL (Variable _ v1))))
    (Symbol (InjectR (InjectL (Variable _ v2))))
      = do env <- ask
           case lookup v1 env of
             Nothing  -> return (v1==v2)   -- Free variables
             Just v2' -> return (v2==v2')

alphaEqM
    (Symbol (InjectL (Lambda _ v1)) :$: a1)
    (Symbol (InjectL (Lambda _ v2)) :$: a2)
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
    => AST (Lambda ctx :+: Variable ctx :+: dom) a
    -> AST (Lambda ctx :+: Variable ctx :+: dom) b
    -> Bool
alphaEq a b = runReader (alphaEqM a b) []



-- | Evaluation of possibly open 'LambdaAST' expressions
evalLambdaM :: (Eval dom, MonadReader [(VarId,Dynamic)] m) =>
    ASTF (Lambda ctx :+: Variable ctx :+: dom) a -> m a
evalLambdaM = liftM result . eval
  where
    eval :: (Eval dom, MonadReader [(VarId,Dynamic)] m) =>
        AST (Lambda ctx :+: Variable ctx :+: dom) a -> m a
    eval (Symbol (InjectR (InjectL (Variable _ v)))) = do
        env <- ask
        case lookup v env of
          Nothing -> return $ error "eval: evaluating free variable"
          Just a  -> case fromDynamic a of
            Just a -> return (Full a)
            _      -> return $ error "eval: internal type error"

    eval (Symbol (InjectL (Lambda _ v)) :$: body) = do
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
evalLambda :: Eval dom => ASTF (Lambda ctx :+: Variable ctx :+: dom) a -> a
evalLambda = flip runReader [] . evalLambdaM



-- | The class of n-ary binding functions
class NAry ctx a dom | a -> dom
    -- Note: using a functional dependency rather than an associated type,
    -- because this makes it possible to make a class alias constraining dom.
    -- GHC doesn't yet handle equality super classes.
  where
    type NAryEval a

    -- | N-ary binding by nested use of the supplied binder
    bindN
      :: Proxy ctx
      -> (  forall b c . (Typeable b, Typeable c, Sat ctx b)
         => (ASTF dom b -> ASTF dom c)
         -> ASTF dom (b -> c)
         )
      -> a -> ASTF dom (NAryEval a)

instance Sat ctx a => NAry ctx (ASTF dom a) dom
  where
    type NAryEval (ASTF dom a) = a
    bindN _ _ = id

instance (Typeable a, Sat ctx a, NAry ctx b dom, Typeable (NAryEval b)) =>
    NAry ctx (ASTF dom a -> b) dom
  where
    type NAryEval (ASTF dom a -> b) = a -> NAryEval b
    bindN ctx lambda = lambda . (bindN ctx lambda .)



-- | Let binding
--
-- A 'Let' expression is really just an application of a lambda binding (the
-- argument @(a -> b)@ is preferably constructed by 'Lambda').
data Let ctxa ctxb a
  where
    Let :: (Sat ctxa a, Sat ctxb b) =>
        Proxy ctxa -> Proxy ctxb -> Let ctxa ctxb (a :-> (a -> b) :-> Full b)

instance WitnessCons (Let ctxa ctxb)
  where
    witnessCons (Let _ _) = ConsWit

instance ExprEq (Let ctxa ctxb)
  where
    exprEq (Let _ _) (Let _ _) = True

instance Render (Let ctxa ctxb)
  where
    renderPart []    (Let _ _) = "Let"
    renderPart [f,a] (Let _ _) = "(" ++ unwords ["letBind",f,a] ++ ")"

instance ToTree (Let ctxa ctxb)
  where
    toTreePart [a,body] (Let _ _) = Node ("Let " ++ var) [a,body']
      where
        Node node [body'] = body
        var               = drop 7 node  -- Drop the "Lambda " prefix

instance Eval (Let ctxa ctxb)
  where
    evaluate (Let _ _) = fromEval (flip ($))

instance ExprHash (Let ctxa ctxb)
  where
    exprHash (Let _ _) = hashInt 0

-- | Partial `Let` projection with explicit context
prjLet :: (Let ctxa ctxb :<: sup) =>
    Proxy ctxa -> Proxy ctxb -> sup a -> Maybe (Let ctxa ctxb a)
prjLet _ _ = project

