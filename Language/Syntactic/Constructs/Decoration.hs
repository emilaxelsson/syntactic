-- | Construct for decorating expressions with additional information

module Language.Syntactic.Constructs.Decoration where



import Control.Monad.Identity
import Data.Tree

import Data.Proxy

import Language.Syntactic.Syntax
import Language.Syntactic.Interpretation.Equality
import Language.Syntactic.Interpretation.Evaluation
import Language.Syntactic.Interpretation.Render



--------------------------------------------------------------------------------
-- * Decoration
--------------------------------------------------------------------------------

-- | Decorating an expression with additional information
--
-- One usage of 'Decor' is to decorate every node of a syntax tree. This is done
-- simply by changing
--
-- > AST dom a
--
-- to
--
-- > AST (Decor info dom) a
--
-- Injection\/projection of an decorated tree is done using 'injDecor' \/
-- 'prjDecor'.
data Decor info expr a
  where
    Decor
        :: { decorInfo :: info (DenResult a)
           , decorExpr :: expr a
           }
        -> Decor info expr a



instance WitnessCons dom => WitnessCons (Decor info dom)
  where
    witnessCons (Decor _ a) = witnessCons a

instance WitnessSat expr => WitnessSat (Decor info expr)
  where
    type SatContext (Decor info expr) = SatContext expr
    witnessSat (Decor _ a) = witnessSat a

instance MaybeWitnessSat ctx dom => MaybeWitnessSat ctx (Decor info dom)
  where
    maybeWitnessSat ctx (Decor _ a) = maybeWitnessSat ctx a

instance ExprEq expr => ExprEq (Decor info expr)
  where
    exprEq a b = decorExpr a `exprEq` decorExpr b
    exprHash   = exprHash . decorExpr

instance Render expr => Render (Decor info expr)
  where
    renderPart args = renderPart args . decorExpr
    render = render . decorExpr

instance ToTree expr => ToTree (Decor info expr)
  where
    toTreePart args = toTreePart args . decorExpr

instance Eval expr => Eval (Decor info expr)
  where
    evaluate = evaluate . decorExpr



injDecor :: (sub :<: sup, Signature a) =>
    info (DenResult a) -> sub a -> AST (Decor info sup) a
injDecor info = Sym . Decor info . inj

prjDecor :: (sub :<: sup) =>
    AST (Decor info sup) a -> Maybe (info (DenResult a), sub a)
prjDecor a = do
    Sym (Decor info b) <- return a
    c                  <- prj b
    return (info, c)

-- | 'injDecor' with explicit context
injDecorCtx :: (sub ctx :<: sup, Signature a) =>
    Proxy ctx -> info (DenResult a) -> sub ctx a -> AST (Decor info sup) a
injDecorCtx ctx info = Sym . Decor info . injCtx ctx

-- | 'prjDecor' with explicit context
prjDecorCtx :: (sub ctx :<: sup)
    => Proxy ctx -> AST (Decor info sup) a
    -> Maybe (info (DenResult a), sub ctx a)
prjDecorCtx ctx a = do
    Sym (Decor info b) <- return a
    c                  <- prjCtx ctx b
    return (info, c)

-- | Get the decoration of the top-level node
getInfo :: AST (Decor info dom) a -> info (DenResult a)
getInfo (Sym (Decor info _)) = info
getInfo (f :$ _)             = getInfo f

-- | Update the decoration of the top-level node
updateDecor :: forall info dom a .
    (info a -> info a) -> ASTF (Decor info dom) a -> ASTF (Decor info dom) a
updateDecor f = runIdentity . transformNode update
  where
    update
        :: (Signature b, a ~ DenResult b)
        => Decor info dom b
        -> Args (AST (Decor info dom)) b
        -> Identity (ASTF (Decor info dom) a)
    update (Decor info a) args = Identity $ appArgs (Sym sym) args
      where
        sym = Decor (f info) a

-- | Lift a function that operates on expressions with associated information to
-- operate on an 'Decor' expression. This function is convenient to use together
-- with e.g. 'queryNodeSimple' when the domain has the form
-- @(`Decor` info dom)@.
liftDecor :: (expr a -> info (DenResult a) -> b) -> (Decor info expr a -> b)
liftDecor f (Decor info a) = f a info

-- | Collect the decorations of all nodes
collectInfo :: (forall a . info a -> b) -> AST (Decor info dom) a -> [b]
collectInfo coll (Sym (Decor info _)) = [coll info]
collectInfo coll (f :$ a) = collectInfo coll f ++ collectInfo coll a

-- | Rendering of decorated syntax trees
toTreeDecor :: forall info dom a . (Render info, ToTree dom) =>
    ASTF (Decor info dom) a -> Tree String
toTreeDecor a = mkTree [] a
  where
    mkTree :: [Tree String] -> AST (Decor info dom) b -> Tree String
    mkTree args (Sym (Decor info expr)) = Node infoStr [toTreePart args expr]
      where
        infoStr = "<<" ++ render info ++ ">>"
    mkTree args (f :$ a) = mkTree (mkTree [] a : args) f

-- | Show an decorated syntax tree using ASCII art
showDecor :: (Render info, ToTree dom) => ASTF (Decor info dom) a -> String
showDecor = drawTree . toTreeDecor

-- | Print an decorated syntax tree using ASCII art
drawDecor :: (Render info, ToTree dom) => ASTF (Decor info dom) a -> IO ()
drawDecor = putStrLn . showDecor

-- | Strip decorations from an 'AST'
stripDecor :: AST (Decor info dom) a -> AST dom a
stripDecor (Sym (Decor _ a)) = Sym a
stripDecor (f :$ a)          = stripDecor f :$ stripDecor a

