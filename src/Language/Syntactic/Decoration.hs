{-# LANGUAGE CPP #-}

#ifndef MIN_VERSION_GLASGOW_HASKELL
#define MIN_VERSION_GLASGOW_HASKELL(a,b,c,d) 0
#endif
  -- MIN_VERSION_GLASGOW_HASKELL was introduced in GHC 7.10

#if MIN_VERSION_GLASGOW_HASKELL(7,10,0,0)
#else
{-# LANGUAGE OverlappingInstances #-}
#endif

-- | Construct for decorating symbols or expressions with additional information

module Language.Syntactic.Decoration where



import Data.Tree (Tree (..))

import Data.Tree.View

import Language.Syntactic.Syntax
import Language.Syntactic.Traversal
import Language.Syntactic.Interpretation
import Language.Syntactic.Sugar



-- | Decorating symbols or expressions with additional information
--
-- One usage of ':&:' is to decorate every node of a syntax tree. This is done
-- simply by changing
--
-- > AST sym sig
--
-- to
--
-- > AST (sym :&: info) sig
data (expr :&: info) sig
  where
    (:&:)
        :: { decorExpr :: expr sig
           , decorInfo :: info (DenResult sig)
           }
        -> (expr :&: info) sig

instance Symbol sym => Symbol (sym :&: info)
  where
    symSig = symSig . decorExpr

instance (NFData1 sym, NFData1 info) => NFData1 (sym :&: info)
  where
    rnf1 (s :&: i) = rnf1 s `seq` rnf1 i `seq` ()

instance Project sub sup => Project sub (sup :&: info)
  where
    prj = prj . decorExpr

instance Equality expr => Equality (expr :&: info)
  where
    equal a b = decorExpr a `equal` decorExpr b
    hash      = hash . decorExpr

instance Render expr => Render (expr :&: info)
  where
    renderSym       = renderSym . decorExpr
    renderArgs args = renderArgs args . decorExpr

instance StringTree expr => StringTree (expr :&: info)
  where
    stringTreeSym args = stringTreeSym args . decorExpr



-- | Map over a decoration
mapDecor
    :: (sym1 sig -> sym2 sig)
    -> (info1 (DenResult sig) -> info2 (DenResult sig))
    -> ((sym1 :&: info1) sig -> (sym2 :&: info2) sig)
mapDecor fs fi (s :&: i) = fs s :&: fi i

-- | Get the decoration of the top-level node
getDecor :: AST (sym :&: info) sig -> info (DenResult sig)
getDecor (Sym (_ :&: info)) = info
getDecor (f :$ _)           = getDecor f

-- | Update the decoration of the top-level node
updateDecor :: forall info sym a .
    (info a -> info a) -> ASTF (sym :&: info) a -> ASTF (sym :&: info) a
updateDecor f = match update
  where
    update
        :: (a ~ DenResult sig)
        => (sym :&: info) sig
        -> Args (AST (sym :&: info)) sig
        -> ASTF (sym :&: info) a
    update (a :&: info) args = appArgs (Sym sym) args
      where
        sym = a :&: (f info)

-- | Lift a function that operates on expressions with associated information to
-- operate on a ':&:' expression. This function is convenient to use together
-- with e.g. 'queryNodeSimple' when the domain has the form @(sym `:&:` info)@.
liftDecor :: (expr s -> info (DenResult s) -> b) -> ((expr :&: info) s -> b)
liftDecor f (a :&: info) = f a info

-- | Strip decorations from an 'AST'
stripDecor :: AST (sym :&: info) sig -> AST sym sig
stripDecor (Sym (a :&: _)) = Sym a
stripDecor (f :$ a)        = stripDecor f :$ stripDecor a

-- | Rendering of decorated syntax trees
stringTreeDecor :: forall info sym a . StringTree sym =>
    (forall a . info a -> String) -> ASTF (sym :&: info) a -> Tree String
stringTreeDecor showInfo a = mkTree [] a
  where
    mkTree :: [Tree String] -> AST (sym :&: info) sig -> Tree String
    mkTree args (Sym (expr :&: info)) = Node infoStr [stringTreeSym args expr]
      where
        infoStr = "<<" ++ showInfo info ++ ">>"
    mkTree args (f :$ a) = mkTree (mkTree [] a : args) f

-- | Show an decorated syntax tree using ASCII art
showDecorWith :: StringTree sym => (forall a . info a -> String) -> ASTF (sym :&: info) a -> String
showDecorWith showInfo = showTree . stringTreeDecor showInfo

-- | Print an decorated syntax tree using ASCII art
drawDecorWith :: StringTree sym => (forall a . info a -> String) -> ASTF (sym :&: info) a -> IO ()
drawDecorWith showInfo = putStrLn . showDecorWith showInfo

writeHtmlDecorWith :: forall info sym a. (StringTree sym)
                   => (forall b. info b -> String) -> FilePath -> ASTF (sym :&: info) a -> IO ()
writeHtmlDecorWith showInfo file a = writeHtmlTree Nothing file $ mkTree [] a
  where
    mkTree :: [Tree NodeInfo] -> AST (sym :&: info) sig -> Tree NodeInfo
    mkTree args (f :$ a) = mkTree (mkTree [] a : args) f
    mkTree args (Sym (expr :&: info)) =
      Node (NodeInfo InitiallyExpanded (renderSym expr) (showInfo info)) args

-- | Make a smart constructor of a symbol. 'smartSymDecor' has any type of the
-- form:
--
-- > smartSymDecor :: (sub :<: AST (sup :&: info))
-- >     => info x
-- >     -> sub (a :-> b :-> ... :-> Full x)
-- >     -> (ASTF sup a -> ASTF sup b -> ... -> ASTF sup x)
smartSymDecor
    :: ( Signature sig
       , f              ~ SmartFun (sup :&: info) sig
       , sig            ~ SmartSig f
       , (sup :&: info) ~ SmartSym f
       , sub :<: sup
       )
    => info (DenResult sig) -> sub sig -> f
smartSymDecor d = smartSym' . (:&: d) . inj

-- | \"Sugared\" symbol application
--
-- 'sugarSymDecor' has any type of the form:
--
-- > sugarSymDecor ::
-- >     ( sub :<: AST (sup :&: info)
-- >     , Syntactic a
-- >     , Syntactic b
-- >     , ...
-- >     , Syntactic x
-- >     , Domain a ~ Domain b ~ ... ~ Domain x
-- >     ) => info (Internal x)
-- >       -> sub (Internal a :-> Internal b :-> ... :-> Full (Internal x))
-- >       -> (a -> b -> ... -> x)
sugarSymDecor
    :: ( Signature sig
       , fi             ~ SmartFun (sup :&: info) sig
       , sig            ~ SmartSig fi
       , (sup :&: info) ~ SmartSym fi
       , SyntacticN f fi
       , sub :<: sup
       )
    => info (DenResult sig) -> sub sig -> f
sugarSymDecor i = sugarN . smartSymDecor i

