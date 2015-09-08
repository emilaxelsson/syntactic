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
    {-# SPECIALIZE instance (Constrained expr) => Constrained (Decor info expr) #-}
    {-# INLINABLE exprDict #-}
    type Sat (Decor info expr) = Sat expr
    exprDict (Decor _ a) = exprDict a

instance Project sub sup => Project sub (Decor info sup)
  where
    {-# SPECIALIZE instance (Project sub sup) => Project sub (Decor info sup) #-}
    {-# INLINABLE prj #-}
    prj = prj . decorExpr

instance Equality expr => Equality (Decor info expr)
  where
    {-# SPECIALIZE instance (Equality expr) => Equality (Decor info expr) #-}
    {-# INLINABLE equal #-}
    {-# INLINABLE exprHash #-}
    equal a b = decorExpr a `equal` decorExpr b
    exprHash  = exprHash . decorExpr

instance Render expr => Render (Decor info expr)
  where
    {-# SPECIALIZE instance (Render expr) => Render (Decor info expr) #-}
    {-# INLINABLE renderSym #-}
    {-# INLINABLE renderArgs #-}
    renderSym = renderSym . decorExpr
    renderArgs args = renderArgs args . decorExpr

instance StringTree expr => StringTree (Decor info expr)
  where
    {-# SPECIALIZE instance (StringTree expr) => StringTree (Decor info expr) #-}
    {-# INLINABLE stringTreeSym #-}
    stringTreeSym args = stringTreeSym args . decorExpr

instance Eval expr => Eval (Decor info expr)
  where
    {-# SPECIALIZE instance (Eval expr) => Eval (Decor info expr) #-}
    {-# INLINABLE evaluate #-}
    evaluate = evaluate . decorExpr



-- | Get the decoration of the top-level node
getInfo :: AST (Decor info dom) sig -> info (DenResult sig)
getInfo (Sym (Decor info _)) = info
getInfo (f :$ _)             = getInfo f
{-# INLINABLE getInfo #-}

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
{-# INLINABLE liftDecor #-}

-- | Collect the decorations of all nodes
collectInfo :: (forall sig . info sig -> b) -> AST (Decor info dom) a -> [b]
collectInfo coll (Sym (Decor info _)) = [coll info]
collectInfo coll (f :$ a) = collectInfo coll f ++ collectInfo coll a

-- | Rendering of decorated syntax trees
stringTreeDecor :: forall info dom a . (StringTree dom) =>
    (forall sig. info sig -> String) -> ASTF (Decor info dom) a -> Tree String
stringTreeDecor showInfo = mkTree []
  where
    mkTree :: [Tree String] -> AST (Decor info dom) sig -> Tree String
    mkTree args (Sym (Decor info expr)) = Node infoStr [stringTreeSym args expr]
      where
        infoStr = "<<" ++ showInfo info ++ ">>"
    mkTree args (f :$ a) = mkTree (mkTree [] a : args) f

-- | Show an decorated syntax tree using ASCII art
showDecorWith :: StringTree dom
              => (forall sig. info sig -> String)
              -> ASTF (Decor info dom) a -> String
showDecorWith showInfo = showTree . stringTreeDecor showInfo

-- | Print an decorated syntax tree using ASCII art
drawDecorWith :: StringTree dom
              => (forall sig. info sig -> String)
              -> ASTF (Decor info dom) a -> IO ()
drawDecorWith showInfo = putStrLn . showDecorWith showInfo

writeHtmlDecorWith :: forall info sym a. (StringTree sym)
                   => (forall sig. info sig -> String)
                   -> FilePath -> ASTF (Decor info sym) a -> IO ()
writeHtmlDecorWith showInfo file = writeHtmlTree file . mkTree []
  where
    mkTree :: [Tree NodeInfo] -> AST (Decor info sym) sig -> Tree NodeInfo
    mkTree args (f :$ a) = mkTree (mkTree [] a : args) f
    mkTree args (Sym (Decor info expr)) = Node (NodeInfo (renderSym expr) (showInfo info)) args

-- | Strip decorations from an 'AST'
stripDecor :: AST (Decor info dom) sig -> AST dom sig
stripDecor (Sym (Decor _ a)) = Sym a
stripDecor (f :$ a)          = stripDecor f :$ stripDecor a
{-# INLINABLE stripDecor #-}
