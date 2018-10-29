{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}

#ifndef MIN_VERSION_GLASGOW_HASKELL
#define MIN_VERSION_GLASGOW_HASKELL(a,b,c,d) 0
#endif
  -- MIN_VERSION_GLASGOW_HASKELL was introduced in GHC 7.10

#if MIN_VERSION_GLASGOW_HASKELL(7,10,0,0)
#else
{-# LANGUAGE OverlappingInstances #-}
#endif

-- | Generic representation of typed syntax trees
--
-- For details, see: A Generic Abstract Syntax Model for Embedded Languages
-- (ICFP 2012, <https://emilaxelsson.github.io/documents/axelsson2012generic.pdf>).

module Language.Syntactic.Syntax
    ( -- * Syntax trees
      AST (..)
    , ASTF
    , ASTFull (..)
    , Full (..)
    , (:->) (..)
    , SigRep (..)
    , Signature (..)
    , DenResult
    , Symbol (..)
    , size
      -- * Smart constructors
    , SmartFun
    , SmartSig
    , SmartSym
    , smartSym'
      -- * Open symbol domains
    , (:+:) (..)
    , Project (..)
    , (:<:) (..)
    , smartSym
    , smartSymTyped
    , Empty
      -- * Existential quantification
    , E (..)
    , liftE
    , liftE2
    , EF (..)
    , liftEF
    , liftEF2
      -- * Type casting expressions
    , Typed (..)
    , injT
    , castExpr
      -- * Misc.
    , NFData1 (..)
    , symType
    , prjP
    ) where



import Control.DeepSeq (NFData (..))
import Data.Typeable
#if MIN_VERSION_GLASGOW_HASKELL(7,10,0,0)
#else
import Data.Foldable (Foldable)
import Data.Proxy  -- Needed by GHC < 7.8
import Data.Traversable (Traversable)
#endif



--------------------------------------------------------------------------------
-- * Syntax trees
--------------------------------------------------------------------------------

-- | Generic abstract syntax tree, parameterized by a symbol domain
--
-- @(`AST` sym (a `:->` b))@ represents a partially applied (or unapplied)
-- symbol, missing at least one argument, while @(`AST` sym (`Full` a))@
-- represents a fully applied symbol, i.e. a complete syntax tree.
data AST sym sig
  where
    Sym  :: sym sig -> AST sym sig
    (:$) :: AST sym (a :-> sig) -> AST sym (Full a) -> AST sym sig

infixl 1 :$

-- | Fully applied abstract syntax tree
type ASTF sym a = AST sym (Full a)

-- | Fully applied abstract syntax tree
--
-- This type is like 'AST', but being a newtype, it is a proper type constructor
-- that can be partially applied.
newtype ASTFull sym a = ASTFull {unASTFull :: ASTF sym a}

instance Functor sym => Functor (AST sym)
  where
    fmap f (Sym s)  = Sym (fmap f s)
    fmap f (s :$ a) = fmap (fmap f) s :$ a

-- | Signature of a fully applied symbol
newtype Full a = Full { result :: a }
  deriving (Eq, Show, Typeable, Functor)

-- | Signature of a partially applied (or unapplied) symbol
newtype a :-> sig = Partial (a -> sig)
  deriving (Typeable, Functor)

infixr :->

-- | Witness of the arity of a symbol signature
data SigRep sig
  where
    SigFull :: SigRep (Full a)
    SigMore :: SigRep sig -> SigRep (a :-> sig)

-- | Valid symbol signatures
class Signature sig
  where
    signature :: SigRep sig

instance Signature (Full a)
  where
    signature = SigFull

instance Signature sig => Signature (a :-> sig)
  where
    signature = SigMore signature

-- | The result type of a symbol with the given signature
type family   DenResult sig
type instance DenResult (Full a)    = a
type instance DenResult (a :-> sig) = DenResult sig

-- | Valid symbols to use in an 'AST'
class Symbol sym
  where
    -- | Reify the signature of a symbol
    symSig :: sym sig -> SigRep sig

instance NFData1 sym => NFData (AST sym sig)
  where
    rnf (Sym s)  = rnf1 s
    rnf (s :$ a) = rnf s `seq` rnf a

-- | Count the number of symbols in an 'AST'
size :: AST sym sig -> Int
size (Sym _)  = 1
size (s :$ a) = size s + size a



--------------------------------------------------------------------------------
-- * Smart constructors
--------------------------------------------------------------------------------

-- | Maps a symbol signature to the type of the corresponding smart constructor:
--
-- > SmartFun sym (a :-> b :-> ... :-> Full x) = ASTF sym a -> ASTF sym b -> ... -> ASTF sym x
type family   SmartFun (sym :: * -> *) sig
type instance SmartFun sym (Full a)    = ASTF sym a
type instance SmartFun sym (a :-> sig) = ASTF sym a -> SmartFun sym sig

-- | Maps a smart constructor type to the corresponding symbol signature:
--
-- > SmartSig (ASTF sym a -> ASTF sym b -> ... -> ASTF sym x) = a :-> b :-> ... :-> Full x
type family   SmartSig f
type instance SmartSig (AST sym sig)     = sig
type instance SmartSig (ASTF sym a -> f) = a :-> SmartSig f

-- | Returns the symbol in the result of a smart constructor
type family   SmartSym f :: * -> *
type instance SmartSym (AST sym sig) = sym
type instance SmartSym (a -> f)      = SmartSym f

-- | Make a smart constructor of a symbol. 'smartSym'' has any type of the form:
--
-- > smartSym'
-- >     :: sym (a :-> b :-> ... :-> Full x)
-- >     -> (ASTF sym a -> ASTF sym b -> ... -> ASTF sym x)
smartSym' :: forall sig f sym
    .  ( Signature sig
       , f   ~ SmartFun sym sig
       , sig ~ SmartSig f
       , sym ~ SmartSym f
       )
    => sym sig -> f
smartSym' s = go (signature :: SigRep sig) (Sym s)
  where
    go :: forall sig . SigRep sig -> AST sym sig -> SmartFun sym sig
    go SigFull s       = s
    go (SigMore sig) s = \a -> go sig (s :$ a)



--------------------------------------------------------------------------------
-- * Open symbol domains
--------------------------------------------------------------------------------

-- | Direct sum of two symbol domains
data (sym1 :+: sym2) sig
  where
    InjL :: sym1 a -> (sym1 :+: sym2) a
    InjR :: sym2 a -> (sym1 :+: sym2) a
  deriving (Functor, Foldable, Traversable)

infixr :+:

instance (Symbol sym1, Symbol sym2) => Symbol (sym1 :+: sym2)
  where
    symSig (InjL s) = symSig s
    symSig (InjR s) = symSig s

instance (NFData1 sym1, NFData1 sym2) => NFData1 (sym1 :+: sym2)
  where
    rnf1 (InjL s) = rnf1 s
    rnf1 (InjR s) = rnf1 s

-- | Symbol projection
--
-- The class is defined for /all pairs of types/, but 'prj' can only succeed if @sup@ is of the form
-- @(... `:+:` sub `:+:` ...)@.
class Project sub sup
  where
    -- | Partial projection from @sup@ to @sub@
    prj :: sup a -> Maybe (sub a)

instance Project sub sup => Project sub (AST sup)
  where
    prj (Sym s) = prj s
    prj _       = Nothing

instance {-# OVERLAPS #-} Project sym sym
  where
    prj = Just

instance {-# OVERLAPS #-} Project sym1 (sym1 :+: sym2)
  where
    prj (InjL a) = Just a
    prj _        = Nothing

instance {-# OVERLAPS #-} Project sym1 sym3 => Project sym1 (sym2 :+: sym3)
  where
    prj (InjR a) = prj a
    prj _        = Nothing


-- | Symbol injection
--
-- The class includes types @sub@ and @sup@ where @sup@ is of the form @(... `:+:` sub `:+:` ...)@.
class Project sub sup => sub :<: sup
  where
    -- | Injection from @sub@ to @sup@
    inj :: sub a -> sup a

instance {-# OVERLAPS #-} (sub :<: sup) => (sub :<: AST sup)
  where
    inj = Sym . inj

instance {-# OVERLAPS #-} (sym :<: sym)
  where
    inj = id

instance {-# OVERLAPS #-} (sym1 :<: (sym1 :+: sym2))
  where
    inj = InjL

instance {-# OVERLAPS #-} (sym1 :<: sym3) => (sym1 :<: (sym2 :+: sym3))
  where
    inj = InjR . inj

-- The reason for separating the `Project` and `(:<:)` classes is that there are
-- types that can be instances of the former but not the latter due to type
-- constraints on the `a` type.

-- | Make a smart constructor of a symbol. 'smartSym' has any type of the form:
--
-- > smartSym :: (sub :<: AST sup)
-- >     => sub (a :-> b :-> ... :-> Full x)
-- >     -> (ASTF sup a -> ASTF sup b -> ... -> ASTF sup x)
smartSym
    :: ( Signature sig
       , f   ~ SmartFun sup sig
       , sig ~ SmartSig f
       , sup ~ SmartSym f
       , sub :<: sup
       )
    => sub sig -> f
smartSym = smartSym' . inj

-- | Make a smart constructor of a symbol. 'smartSymTyped' has any type of the
-- form:
--
-- > smartSymTyped :: (sub :<: AST (Typed sup), Typeable x)
-- >     => sub (a :-> b :-> ... :-> Full x)
-- >     -> (ASTF sup a -> ASTF sup b -> ... -> ASTF sup x)
smartSymTyped
    :: ( Signature sig
       , f         ~ SmartFun (Typed sup) sig
       , sig       ~ SmartSig f
       , Typed sup ~ SmartSym f
       , sub :<: sup
       , Typeable (DenResult sig)
       )
    => sub sig -> f
smartSymTyped = smartSym' . Typed . inj

-- | Empty symbol type
--
-- Can be used to make uninhabited 'AST' types. It can also be used as a terminator in co-product
-- lists (e.g. to avoid overlapping instances):
--
-- > (A :+: B :+: Empty)
data Empty :: * -> *



--------------------------------------------------------------------------------
-- * Existential quantification
--------------------------------------------------------------------------------

-- | Existential quantification
data E e
  where
    E :: e a -> E e

liftE :: (forall a . e a -> b) -> E e -> b
liftE f (E a) = f a

liftE2 :: (forall a b . e a -> e b -> c) -> E e -> E e -> c
liftE2 f (E a) (E b) = f a b

-- | Existential quantification of 'Full'-indexed type
data EF e
  where
    EF :: e (Full a) -> EF e

liftEF :: (forall a . e (Full a) -> b) -> EF e -> b
liftEF f (EF a) = f a

liftEF2 :: (forall a b . e (Full a) -> e (Full b) -> c) -> EF e -> EF e -> c
liftEF2 f (EF a) (EF b) = f a b



--------------------------------------------------------------------------------
-- * Type casting expressions
--------------------------------------------------------------------------------

-- | \"Typed\" symbol. Using @`Typed` sym@ instead of @sym@ gives access to the
-- function 'castExpr' for casting expressions.
data Typed sym sig
  where
    Typed :: Typeable (DenResult sig) => sym sig -> Typed sym sig

instance Project sub sup => Project sub (Typed sup)
  where
    prj (Typed s) = prj s

-- | Inject a symbol in an 'AST' with a 'Typed' domain
injT :: (sub :<: sup, Typeable (DenResult sig)) =>
    sub sig -> AST (Typed sup) sig
injT = Sym . Typed . inj

-- | Type cast an expression
castExpr :: forall sym a b
    .  ASTF (Typed sym) a  -- ^ Expression to cast
    -> ASTF (Typed sym) b  -- ^ Witness for typeability of result
    -> Maybe (ASTF (Typed sym) b)
castExpr a b = cast1 a
  where
    cast1 :: (DenResult sig ~ a) => AST (Typed sym) sig -> Maybe (ASTF (Typed sym) b)
    cast1 (s :$ _) = cast1 s
    cast1 (Sym (Typed _)) = cast2 b
      where
        cast2 :: (DenResult sig ~ b) => AST (Typed sym) sig -> Maybe (ASTF (Typed sym) b)
        cast2 (s :$ _)        = cast2 s
        cast2 (Sym (Typed _)) = gcast a
  -- Could be simplified using `simpleMatch`, but that would give an import
  -- cycle.
  --
  --     castExpr a b =
  --       simpleMatch
  --         (\(Typed _) _ -> simpleMatch
  --           (\(Typed _) _ -> gcast a
  --           ) b
  --         ) a



--------------------------------------------------------------------------------
-- * Misc.
--------------------------------------------------------------------------------

-- | Higher-kinded version of 'NFData'
class NFData1 c
  where
    -- | Force a symbol to normal form
    rnf1 :: c a -> ()
    rnf1 s = s `seq` ()

-- | Constrain a symbol to a specific type
symType :: Proxy sym -> sym sig -> sym sig
symType _ = id

-- | Projection to a specific symbol type
prjP :: Project sub sup => Proxy sub -> sup sig -> Maybe (sub sig)
prjP _ = prj

