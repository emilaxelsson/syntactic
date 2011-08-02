-- | Annotations for syntax trees

module Language.Syntactic.Features.Annotate where



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

-- | Collect the annotations of all nodes
collectInfo :: (forall a . info a -> b) -> AST (Ann info dom) a -> [b]
collectInfo coll (Symbol (Ann info _)) = [coll info]
collectInfo coll (f :$: a) = collectInfo coll f ++ collectInfo coll a

