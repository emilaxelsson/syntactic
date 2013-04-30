{-# LANGUAGE TemplateHaskell #-}

-- | Construction and elimination of tuples in the object language

module Language.Syntactic.Constructs.Tuple where



import Data.Tuple.Select

import Language.Syntactic



--------------------------------------------------------------------------------
-- * Construction
--------------------------------------------------------------------------------

-- | Expressions for constructing tuples
data Tuple sig
  where
    Tup2 :: Tuple (a :-> b :-> Full (a,b))
    Tup3 :: Tuple (a :-> b :-> c :-> Full (a,b,c))
    Tup4 :: Tuple (a :-> b :-> c :-> d :-> Full (a,b,c,d))
    Tup5 :: Tuple (a :-> b :-> c :-> d :-> e :-> Full (a,b,c,d,e))
    Tup6 :: Tuple (a :-> b :-> c :-> d :-> e :-> f :-> Full (a,b,c,d,e,f))
    Tup7 :: Tuple (a :-> b :-> c :-> d :-> e :-> f :-> g :-> Full (a,b,c,d,e,f,g))

instance Constrained Tuple
  where
    type Sat Tuple = Top
    exprDict _ = Dict

instance Semantic Tuple
  where
    semantics Tup2 = Sem "tup2" (,)
    semantics Tup3 = Sem "tup3" (,,)
    semantics Tup4 = Sem "tup4" (,,,)
    semantics Tup5 = Sem "tup5" (,,,,)
    semantics Tup6 = Sem "tup6" (,,,,,)
    semantics Tup7 = Sem "tup7" (,,,,,,)

semanticInstances ''Tuple



--------------------------------------------------------------------------------
-- * Projection
--------------------------------------------------------------------------------

-- | These families ('Sel1'' - 'Sel7'') are needed because of the problem
-- described in:
--
-- <http://emil-fp.blogspot.com/2011/08/fundeps-weaker-than-type-families.html>
type family Sel1' a
type instance Sel1' (a,b)           = a
type instance Sel1' (a,b,c)         = a
type instance Sel1' (a,b,c,d)       = a
type instance Sel1' (a,b,c,d,e)     = a
type instance Sel1' (a,b,c,d,e,f)   = a
type instance Sel1' (a,b,c,d,e,f,g) = a

type family Sel2' a
type instance Sel2' (a,b)           = b
type instance Sel2' (a,b,c)         = b
type instance Sel2' (a,b,c,d)       = b
type instance Sel2' (a,b,c,d,e)     = b
type instance Sel2' (a,b,c,d,e,f)   = b
type instance Sel2' (a,b,c,d,e,f,g) = b

type family Sel3' a
type instance Sel3' (a,b,c)         = c
type instance Sel3' (a,b,c,d)       = c
type instance Sel3' (a,b,c,d,e)     = c
type instance Sel3' (a,b,c,d,e,f)   = c
type instance Sel3' (a,b,c,d,e,f,g) = c

type family Sel4' a
type instance Sel4' (a,b,c,d)       = d
type instance Sel4' (a,b,c,d,e)     = d
type instance Sel4' (a,b,c,d,e,f)   = d
type instance Sel4' (a,b,c,d,e,f,g) = d

type family Sel5' a
type instance Sel5' (a,b,c,d,e)     = e
type instance Sel5' (a,b,c,d,e,f)   = e
type instance Sel5' (a,b,c,d,e,f,g) = e

type family Sel6' a
type instance Sel6' (a,b,c,d,e,f)   = f
type instance Sel6' (a,b,c,d,e,f,g) = f

type family Sel7' a
type instance Sel7' (a,b,c,d,e,f,g) = g

-- | Expressions for selecting elements of a tuple
data Select a
  where
    Sel1 :: (Sel1 a b, Sel1' a ~ b) => Select (a :-> Full b)
    Sel2 :: (Sel2 a b, Sel2' a ~ b) => Select (a :-> Full b)
    Sel3 :: (Sel3 a b, Sel3' a ~ b) => Select (a :-> Full b)
    Sel4 :: (Sel4 a b, Sel4' a ~ b) => Select (a :-> Full b)
    Sel5 :: (Sel5 a b, Sel5' a ~ b) => Select (a :-> Full b)
    Sel6 :: (Sel6 a b, Sel6' a ~ b) => Select (a :-> Full b)
    Sel7 :: (Sel7 a b, Sel7' a ~ b) => Select (a :-> Full b)

instance Constrained Select
  where
    type Sat Select = Top
    exprDict _ = Dict

instance Semantic Select
  where
    semantics Sel1 = Sem "sel1" sel1
    semantics Sel2 = Sem "sel2" sel2
    semantics Sel3 = Sem "sel3" sel3
    semantics Sel4 = Sem "sel4" sel4
    semantics Sel5 = Sem "sel5" sel5
    semantics Sel6 = Sem "sel6" sel6
    semantics Sel7 = Sem "sel7" sel7

semanticInstances ''Select

-- | Return the selected position, e.g.
--
-- > selectPos (Sel3 poly :: Select Poly ((Int,Int,Int,Int) :-> Full Int)) = 3
selectPos :: Select a -> Int
selectPos Sel1 = 1
selectPos Sel2 = 2
selectPos Sel3 = 3
selectPos Sel4 = 4
selectPos Sel5 = 5
selectPos Sel6 = 6
selectPos Sel7 = 7

