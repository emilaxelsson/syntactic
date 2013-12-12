{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -cpp #-}

-- | Generic representation of typed syntax trees
--
-- For details, see: A Generic Abstract Syntax Model for Embedded Languages
-- (ICFP 2012, <http://www.cse.chalmers.se/~emax/documents/axelsson2012generic.pdf>).

module Data.Syntactic.Syntax
    ( -- * Syntax trees
      AST (..)
    , ASTF
    , Full (..)
    , (:->) (..)
    , size
    , ApplySym (..)
    , DenResult
      -- * Open symbol domains
    , (:+:) (..)
    , Project (..)
    , (:<:) (..)
    , appSym
      -- * Type inference
    , symType
    , prjP
    ) where



import Control.Monad.Instances  -- TODO Not needed in GHC 7.6
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Data.Typeable

import Data.PolyProxy



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

-- | Count the number of symbols in an expression
size :: AST sym sig -> Int
size (Sym _)  = 1
size (s :$ a) = size s + size a

-- | Class for the type-level recursion needed by 'appSym'
class ApplySym sig f sym | sig sym -> f, f -> sig sym
  where
    appSym' :: AST sym sig -> f

instance ApplySym (Full a) (ASTF sym a) sym
  where
    appSym' = id

instance ApplySym sig f sym => ApplySym (a :-> sig) (ASTF sym a -> f) sym
  where
    appSym' s a = appSym' (s :$ a)

-- | The result type of a symbol with the given signature
type family   DenResult sig
type instance DenResult (Full a)    = a
type instance DenResult (a :-> sig) = DenResult sig



--------------------------------------------------------------------------------
-- * Open symbol domains
--------------------------------------------------------------------------------

-- | Direct sum of two symbol domains
data (sym1 :+: sym2) a
  where
    InjL :: sym1 a -> (sym1 :+: sym2) a
    InjR :: sym2 a -> (sym1 :+: sym2) a
  deriving (Functor, Foldable, Traversable)

infixr :+:

-- | Symbol projection
class Project sub sup
  where
    -- | Partial projection from @sup@ to @sub@
    prj :: sup a -> Maybe (sub a)

instance Project sub sup => Project sub (AST sup)
  where
    prj (Sym s) = prj s
    prj _       = Nothing

instance Project expr expr
  where
    prj = Just

instance Project expr1 (expr1 :+: expr2)
  where
    prj (InjL a) = Just a
    prj _        = Nothing

instance Project expr1 expr3 => Project expr1 (expr2 :+: expr3)
  where
    prj (InjR a) = prj a
    prj _        = Nothing

-- | Symbol subsumption
class Project sub sup => sub :<: sup
  where
    -- | Injection from @sub@ to @sup@
    inj :: sub a -> sup a

instance (sub :<: sup) => (sub :<: AST sup)
  where
    inj = Sym . inj

instance (expr :<: expr)
  where
    inj = id

instance (expr1 :<: (expr1 :+: expr2))
  where
    inj = InjL

instance (expr1 :<: expr3) => (expr1 :<: (expr2 :+: expr3))
  where
    inj = InjR . inj

-- The reason for separating the `Project` and `(:<:)` classes is that there are
-- types that can be instances of the former but not the latter due to type
-- constraints on the `a` type.

-- | Generic symbol application
--
-- 'appSym' has any type of the form:
--
-- > appSym :: (sub :<: AST sup)
-- >     => sub (a :-> b :-> ... :-> Full x)
-- >     -> (ASTF sup a -> ASTF sup b -> ... -> ASTF sup x)
appSym :: (sub :<: AST sup, ApplySym sig f sup) => sub sig -> f
appSym = appSym' . inj



--------------------------------------------------------------------------------
-- * Type inference
--------------------------------------------------------------------------------

-- | Constrain a symbol to a specific type
symType :: P sym -> sym sig -> sym sig
symType _ = id

-- | Projection to a specific symbol type
prjP :: Project sub sup => P sub -> sup sig -> Maybe (sub sig)
prjP _ = prj

