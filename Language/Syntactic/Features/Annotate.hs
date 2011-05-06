-- | Annotations for syntax trees

module Language.Syntactic.Features.Annotate where



import Language.Syntactic.Syntax
import Language.Syntactic.Analysis.Equality
import Language.Syntactic.Analysis.Render
import Language.Syntactic.Analysis.Evaluation
import Language.Syntactic.Analysis.Hash



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
    Ann :: info (EvalResult a) -> expr a -> Ann info expr a



instance ExprEq expr => ExprEq (Ann info expr)
  where
    Ann _ a `exprEq` Ann _ b = exprEq a b

instance Render expr => Render (Ann info expr)
  where
    render (Ann _ a) = render a

instance ToTree expr => ToTree (Ann info expr)
  where
    toTreePart args (Ann _ a) = toTreePart args a

instance Eval expr => Eval (Ann info expr)
  where
    evaluate (Ann _ a) = evaluate a

instance ExprHash expr => ExprHash (Ann info expr)
  where
    exprHash (Ann _ a) = exprHash a



injectAnn :: (sub :<: sup, ConsType a) =>
    info (EvalResult a) -> sub a -> AST (Ann info sup) a
injectAnn info = Symbol . Ann info . inject

projectAnn :: (sub :<: sup) =>
    AST (Ann info sup) a -> Maybe (info (EvalResult a), sub a)
projectAnn a = do
    Symbol (Ann info b) <- return a
    c                   <- project b
    return (info, c)

getInfo :: AST (Ann info sup) a -> info (EvalResult a)
getInfo (Symbol (Ann info _)) = info
getInfo (f :$: _)             = getInfo f

