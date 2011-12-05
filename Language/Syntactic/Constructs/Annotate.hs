-- | Annotations for syntax trees

module Language.Syntactic.Constructs.Annotate where



import Data.Tree

import Language.Syntactic.Syntax
import Language.Syntactic.Interpretation.Equality
import Language.Syntactic.Interpretation.Render
import Language.Syntactic.Interpretation.Evaluation



-- | Annotating an expression with arbitrary information.
--
-- This can be used to annotate every node of a syntax tree, which is done by
-- changing
--
-- > AST dom a
--
-- to
--
-- > AST (Ann info dom) a
--
-- Injection/projection of an annotated tree is done using
-- 'injectAnn' / 'projectAnn'.
data Ann info expr a
  where
    Ann
        :: { annInfo :: info (EvalResult a)
           , annExpr :: expr a
           }
        -> Ann info expr a

type AnnSTF info dom a = ASTF (Ann info dom) a



instance WitnessCons dom => WitnessCons (Ann info dom)
  where
    witnessCons (Ann _ a) = witnessCons a

instance WitnessSat expr => WitnessSat (Ann info expr)
  where
    type SatContext (Ann info expr) = SatContext expr
    witnessSat (Ann _ a) = witnessSat a

instance MaybeWitnessSat ctx dom => MaybeWitnessSat ctx (Ann info dom)
  where
    maybeWitnessSat ctx (Ann _ a) = maybeWitnessSat ctx a

instance ExprEq expr => ExprEq (Ann info expr)
  where
    exprEq a b = annExpr a `exprEq` annExpr b
    exprHash   = exprHash . annExpr

instance Render expr => Render (Ann info expr)
  where
    render = render . annExpr

instance ToTree expr => ToTree (Ann info expr)
  where
    toTreePart args = toTreePart args . annExpr

instance Eval expr => Eval (Ann info expr)
  where
    evaluate = evaluate . annExpr



injectAnn :: (sub :<: sup, ConsType a) =>
    info (EvalResult a) -> sub a -> AST (Ann info sup) a
injectAnn info = Symbol . Ann info . inject

projectAnn :: (sub :<: sup) =>
    AST (Ann info sup) a -> Maybe (info (EvalResult a), sub a)
projectAnn a = do
    Symbol (Ann info b) <- return a
    c                   <- project b
    return (info, c)

-- | Get the annotation of the top-level node
getInfo :: AST (Ann info dom) a -> info (EvalResult a)
getInfo (Symbol (Ann info _)) = info
getInfo (f :$: _)             = getInfo f

-- | Lift a function that operates on expressions with associated information to
-- operate on an 'Ann' expression. This function is convenient to use together
-- with e.g. 'queryNodeSimple' when the domain has the form @(`Ann` info dom)@.
liftAnn :: (expr a -> info (EvalResult a) -> b) -> (Ann info expr a -> b)
liftAnn f (Ann info a) = f a info

-- | Collect the annotations of all nodes
collectInfo :: (forall a . info a -> b) -> AST (Ann info dom) a -> [b]
collectInfo coll (Symbol (Ann info _)) = [coll info]
collectInfo coll (f :$: a) = collectInfo coll f ++ collectInfo coll a

-- | Rendering of annotated syntax trees
toTreeAnn :: forall info dom a . (Render info, ToTree dom) =>
    ASTF (Ann info dom) a -> Tree String
toTreeAnn a = mkTree [] a
  where
    mkTree :: [Tree String] -> AST (Ann info dom) b -> Tree String
    mkTree args (Symbol (Ann info expr)) = Node infoStr [toTreePart args expr]
      where
        infoStr = "<<" ++ render info ++ ">>"
    mkTree args (f :$: a) = mkTree (mkTree [] a : args) f

-- | Show an annotated syntax tree using ASCII art
showAnn :: (Render info, ToTree dom) => ASTF (Ann info dom) a -> String
showAnn = drawTree . toTreeAnn

-- | Print an annotated syntax tree using ASCII art
drawAnn :: (Render info, ToTree dom) => ASTF (Ann info dom) a -> IO ()
drawAnn = putStrLn . showAnn

-- | Strip annotations from an 'AST'
stripAnn :: AST (Ann info dom) a -> AST dom a
stripAnn (Symbol (Ann _ a)) = Symbol a
stripAnn (f :$: a)          = stripAnn f :$: stripAnn a

