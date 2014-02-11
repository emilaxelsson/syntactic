{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Construct for decorating expressions with additional information

module Language.Syntactic.Constructs.Decoration where



import Data.Tree (Tree (..))

import Data.Tree.View

import Language.Syntactic



--------------------------------------------------------------------------------
-- * Decoration
--------------------------------------------------------------------------------

-- | Decorating symbols with additional information
--
-- One usage of 'Decor' is to decorate every node of a syntax tree. This is done
-- simply by changing
--
-- > AST dom sig
--
-- to
--
-- > AST (Decor info dom) sig
data Decor info expr sig
  where
    Decor
        :: { decorInfo :: info (DenResult sig)
           , decorExpr :: expr sig
           }
        -> Decor info expr sig

instance Constrained expr => Constrained (Decor info expr)
  where
    type Sat (Decor info expr) = Sat expr
    exprDict (Decor _ a) = exprDict a

instance Project sub sup => Project sub (Decor info sup)
  where
    prj = prj . decorExpr

instance Equality expr => Equality (Decor info expr)
  where
    equal a b = decorExpr a `equal` decorExpr b
    exprHash  = exprHash . decorExpr

instance Render expr => Render (Decor info expr)
  where
    renderSym = renderSym . decorExpr
    renderArgs args = renderArgs args . decorExpr

instance StringTree expr => StringTree (Decor info expr)
  where
    stringTreeSym args = stringTreeSym args . decorExpr

instance Eval expr => Eval (Decor info expr)
  where
    evaluate = evaluate . decorExpr



-- | Get the decoration of the top-level node
getInfo :: AST (Decor info dom) sig -> info (DenResult sig)
getInfo (Sym (Decor info _)) = info
getInfo (f :$ _)             = getInfo f

-- | Update the decoration of the top-level node
updateDecor :: forall info dom a .
    (info a -> info a) -> ASTF (Decor info dom) a -> ASTF (Decor info dom) a
updateDecor f = match update
  where
    update
        :: (a ~ DenResult sig)
        => Decor info dom sig
        -> Args (AST (Decor info dom)) sig
        -> ASTF (Decor info dom) a
    update (Decor info a) args = appArgs (Sym sym) args
      where
        sym = Decor (f info) a

-- | Lift a function that operates on expressions with associated information to
-- operate on an 'Decor' expression. This function is convenient to use together
-- with e.g. 'queryNodeSimple' when the domain has the form
-- @(`Decor` info dom)@.
liftDecor :: (expr s -> info (DenResult s) -> b) -> (Decor info expr s -> b)
liftDecor f (Decor info a) = f a info

-- | Collect the decorations of all nodes
collectInfo :: (forall sig . info sig -> b) -> AST (Decor info dom) sig -> [b]
collectInfo coll (Sym (Decor info _)) = [coll info]
collectInfo coll (f :$ a) = collectInfo coll f ++ collectInfo coll a

-- | Rendering of decorated syntax trees
stringTreeDecor :: forall info dom a . (StringTree dom) =>
    (forall a. info a -> String) -> ASTF (Decor info dom) a -> Tree String
stringTreeDecor showInfo a = mkTree [] a
  where
    mkTree :: [Tree String] -> AST (Decor info dom) sig -> Tree String
    mkTree args (Sym (Decor info expr)) = Node infoStr [stringTreeSym args expr]
      where
        infoStr = "<<" ++ showInfo info ++ ">>"
    mkTree args (f :$ a) = mkTree (mkTree [] a : args) f

-- | Show an decorated syntax tree using ASCII art
showDecorWith :: StringTree dom => (forall a. info a -> String) -> ASTF (Decor info dom) a -> String
showDecorWith showInfo = showTree . stringTreeDecor showInfo

-- | Print an decorated syntax tree using ASCII art
drawDecorWith :: StringTree dom => (forall a. info a -> String) -> ASTF (Decor info dom) a -> IO ()
drawDecorWith showInfo = putStrLn . showDecorWith showInfo

-- | Strip decorations from an 'AST'
stripDecor :: AST (Decor info dom) sig -> AST dom sig
stripDecor (Sym (Decor _ a)) = Sym a
stripDecor (f :$ a)          = stripDecor f :$ stripDecor a

