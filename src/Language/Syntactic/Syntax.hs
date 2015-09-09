{-# LANGUAGE CPP #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif
{-# LANGUAGE UndecidableInstances #-}

-- | Generic representation of typed syntax trees
--
-- For details, see: A Generic Abstract Syntax Model for Embedded Languages
-- (ICFP 2012, <http://www.cse.chalmers.se/~emax/documents/axelsson2012generic.pdf>).

module Language.Syntactic.Syntax
    ( -- * Syntax trees
      AST (..)
    , ASTF
    , Full (..)
    , (:->) (..)
    , size
    , ApplySym (..)
    , DenResult
      -- * Symbol domains
    , (:+:) (..)
    , Project (..)
    , (:<:) (..)
    , appSym
      -- * Type inference
    , symType
    , prjP
    ) where


#if (__GLASGOW_HASKELL__ <= 704)
import Control.Monad.Instances ()
#endif
import Data.Typeable

import Data.PolyProxy



--------------------------------------------------------------------------------
-- * Syntax trees
--------------------------------------------------------------------------------

-- | Generic abstract syntax tree, parameterized by a symbol domain
--
-- @(`AST` dom (a `:->` b))@ represents a partially applied (or unapplied)
-- symbol, missing at least one argument, while @(`AST` dom (`Full` a))@
-- represents a fully applied symbol, i.e. a complete syntax tree.
data AST dom sig
  where
    Sym  :: dom sig -> AST dom sig
    (:$) :: AST dom (a :-> sig) -> AST dom (Full a) -> AST dom sig

infixl 1 :$

-- | Fully applied abstract syntax tree
type ASTF dom a = AST dom (Full a)

instance Functor dom => Functor (AST dom)
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
size :: AST dom sig -> Int
size (Sym _)  = 1
size (s :$ a) = size s + size a

-- | Class for the type-level recursion needed by 'appSym'
class ApplySym sig f dom | sig dom -> f, f -> sig dom
  where
    appSym' :: AST dom sig -> f

instance ApplySym (Full a) (ASTF dom a) dom
  where
    {-# SPECIALIZE instance ApplySym (Full a) (ASTF dom a) dom #-}
    {-# INLINABLE appSym' #-}
    appSym' = id

instance ApplySym sig f dom => ApplySym (a :-> sig) (ASTF dom a -> f) dom
  where
    {-# SPECIALIZE instance ApplySym sig f dom => ApplySym (a :-> sig) (ASTF dom a -> f) dom #-}
    {-# INLINABLE appSym' #-}
    appSym' sym a = appSym' (sym :$ a)

-- | The result type of a symbol with the given signature
type family   DenResult sig
type instance DenResult (Full a)    = a
type instance DenResult (a :-> sig) = DenResult sig



--------------------------------------------------------------------------------
-- * Symbol domains
--------------------------------------------------------------------------------

-- | Direct sum of two symbol domains
data (dom1 :+: dom2) a
  where
    InjL :: dom1 a -> (dom1 :+: dom2) a
    InjR :: dom2 a -> (dom1 :+: dom2) a
  deriving (Functor)

infixr :+:

-- | Symbol projection
class Project sub sup
  where
    -- | Partial projection from @sup@ to @sub@
    prj :: sup a -> Maybe (sub a)

instance Project sub sup => Project sub (AST sup)
  where
    {-# SPECIALIZE instance Project sub sup => Project sub (AST sup) #-}
    {-# INLINABLE prj #-}
    prj (Sym a) = prj a
    prj _       = Nothing

instance Project expr expr
  where
    {-# SPECIALIZE instance Project expr expr #-}
    {-# INLINABLE prj #-}
    prj = Just

instance {-# OVERLAPPING #-} Project expr1 (expr1 :+: expr2)
  where
    {-# SPECIALIZE instance Project expr1 (expr1 :+: expr2) #-}
    {-# INLINABLE prj #-}
    prj (InjL a) = Just a
    prj _        = Nothing

instance {-# OVERLAPPING #-} Project expr1 expr3 => Project expr1 (expr2 :+: expr3)
  where
    {-# SPECIALIZE instance Project expr1 expr3 => Project expr1 (expr2 :+: expr3) #-}
    {-# INLINABLE prj #-}
    prj (InjR a) = prj a
    prj _        = Nothing

-- | Symbol subsumption
class Project sub sup => sub :<: sup
  where
    -- | Injection from @sub@ to @sup@
    inj :: sub a -> sup a

instance (sub :<: sup) => (sub :<: AST sup)
  where
    {-# SPECIALIZE instance (sub :<: sup) => (sub :<: AST sup) #-}
    {-# INLINABLE inj #-}
    inj = Sym . inj

instance (expr :<: expr)
  where
    {-# SPECIALIZE instance (expr :<: expr) #-}
    {-# INLINABLE inj #-}
    inj = id

instance {-# OVERLAPPING #-} (expr1 :<: (expr1 :+: expr2))
  where
    {-# SPECIALIZE instance (expr1 :<: (expr1 :+: expr2)) #-}
    {-# INLINABLE inj #-}
    inj = InjL

instance {-# OVERLAPPING #-} (expr1 :<: expr3) => (expr1 :<: (expr2 :+: expr3))
  where
    {-# SPECIALIZE instance (expr1 :<: expr3) => (expr1 :<: (expr2 :+: expr3)) #-}
    {-# INLINABLE inj #-}
    inj = InjR . inj

-- The reason for separating the `Project` and `(:<:)` classes is that there are
-- types that can be instances of the former but not the latter due to type
-- constraints on the `a` type.

-- | Generic symbol application
--
-- 'appSym' has any type of the form:
--
-- > appSym :: (expr :<: AST dom)
-- >     => expr (a :-> b :-> ... :-> Full x)
-- >     -> (ASTF dom a -> ASTF dom b -> ... -> ASTF dom x)
appSym :: (ApplySym sig f dom, sym :<: AST dom) => sym sig -> f
appSym = appSym' . inj
{-# INLINABLE appSym #-}



--------------------------------------------------------------------------------
-- * Type inference
--------------------------------------------------------------------------------

-- | Constrain a symbol to a specific type
symType :: P sym -> sym sig -> sym sig
symType = const id
{-# INLINABLE symType #-}

-- | Projection to a specific symbol type
prjP :: Project sub sup => P sub -> sup sig -> Maybe (sub sig)
prjP = const prj
{-# INLINABLE prjP #-}
