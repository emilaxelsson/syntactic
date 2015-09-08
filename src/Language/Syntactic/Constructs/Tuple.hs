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
    Tup8 :: Tuple (a :-> b :-> c :-> d :-> e :-> f :-> g :-> h :-> Full (a,b,c,d,e,f,g,h))
    Tup9 :: Tuple (a :-> b :-> c :-> d :-> e :-> f :-> g :-> h :-> i :-> Full (a,b,c,d,e,f,g,h,i))
    Tup10 :: Tuple (a :-> b :-> c :-> d :-> e :-> f :-> g :-> h :-> i :-> j :-> Full (a,b,c,d,e,f,g,h,i,j))
    Tup11 :: Tuple (a :-> b :-> c :-> d :-> e :-> f :-> g :-> h :-> i :-> j :-> k :-> Full (a,b,c,d,e,f,g,h,i,j,k))
    Tup12 :: Tuple (a :-> b :-> c :-> d :-> e :-> f :-> g :-> h :-> i :-> j :-> k :-> l :-> Full (a,b,c,d,e,f,g,h,i,j,k,l))
    Tup13 :: Tuple (a :-> b :-> c :-> d :-> e :-> f :-> g :-> h :-> i :-> j :-> k :-> l :-> m :-> Full (a,b,c,d,e,f,g,h,i,j,k,l,m))
    Tup14 :: Tuple (a :-> b :-> c :-> d :-> e :-> f :-> g :-> h :-> i :-> j :-> k :-> l :-> m :-> n :-> Full (a,b,c,d,e,f,g,h,i,j,k,l,m,n))
    Tup15 :: Tuple (a :-> b :-> c :-> d :-> e :-> f :-> g :-> h :-> i :-> j :-> k :-> l :-> m :-> n :-> o :-> Full (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o))

instance Constrained Tuple
  where
    {-# SPECIALIZE instance Constrained Tuple #-}
    {-# INLINE exprDict #-}
    type Sat Tuple = Top
    exprDict = const Dict

instance Semantic Tuple
  where
    {-# SPECIALIZE instance Semantic Tuple #-}
    {-# INLINABLE semantics #-}
    semantics Tup2  = Sem "tup2"  (,)
    semantics Tup3  = Sem "tup3"  (,,)
    semantics Tup4  = Sem "tup4"  (,,,)
    semantics Tup5  = Sem "tup5"  (,,,,)
    semantics Tup6  = Sem "tup6"  (,,,,,)
    semantics Tup7  = Sem "tup7"  (,,,,,,)
    semantics Tup8  = Sem "tup8"  (,,,,,,,)
    semantics Tup9  = Sem "tup9"  (,,,,,,,,)
    semantics Tup10 = Sem "tup10" (,,,,,,,,,)
    semantics Tup11 = Sem "tup11" (,,,,,,,,,,)
    semantics Tup12 = Sem "tup12" (,,,,,,,,,,,)
    semantics Tup13 = Sem "tup13" (,,,,,,,,,,,,)
    semantics Tup14 = Sem "tup14" (,,,,,,,,,,,,,)
    semantics Tup15 = Sem "tup15" (,,,,,,,,,,,,,,)

semanticInstances ''Tuple



--------------------------------------------------------------------------------
-- * Projection
--------------------------------------------------------------------------------

-- | These families ('Sel1'' - 'Sel15'') are needed because of the problem
-- described in:
--
-- <http://emil-fp.blogspot.com/2011/08/fundeps-weaker-than-type-families.html>
type family Sel1' a
type instance Sel1' (a,b)                           = a
type instance Sel1' (a,b,c)                         = a
type instance Sel1' (a,b,c,d)                       = a
type instance Sel1' (a,b,c,d,e)                     = a
type instance Sel1' (a,b,c,d,e,f)                   = a
type instance Sel1' (a,b,c,d,e,f,g)                 = a
type instance Sel1' (a,b,c,d,e,f,g,h)               = a
type instance Sel1' (a,b,c,d,e,f,g,h,i)             = a
type instance Sel1' (a,b,c,d,e,f,g,h,i,j)           = a
type instance Sel1' (a,b,c,d,e,f,g,h,i,j,k)         = a
type instance Sel1' (a,b,c,d,e,f,g,h,i,j,k,l)       = a
type instance Sel1' (a,b,c,d,e,f,g,h,i,j,k,l,m)     = a
type instance Sel1' (a,b,c,d,e,f,g,h,i,j,k,l,m,n)   = a
type instance Sel1' (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) = a

type family Sel2' a
type instance Sel2' (a,b)                           = b
type instance Sel2' (a,b,c)                         = b
type instance Sel2' (a,b,c,d)                       = b
type instance Sel2' (a,b,c,d,e)                     = b
type instance Sel2' (a,b,c,d,e,f)                   = b
type instance Sel2' (a,b,c,d,e,f,g)                 = b
type instance Sel2' (a,b,c,d,e,f,g,h)               = b
type instance Sel2' (a,b,c,d,e,f,g,h,i)             = b
type instance Sel2' (a,b,c,d,e,f,g,h,i,j)           = b
type instance Sel2' (a,b,c,d,e,f,g,h,i,j,k)         = b
type instance Sel2' (a,b,c,d,e,f,g,h,i,j,k,l)       = b
type instance Sel2' (a,b,c,d,e,f,g,h,i,j,k,l,m)     = b
type instance Sel2' (a,b,c,d,e,f,g,h,i,j,k,l,m,n)   = b
type instance Sel2' (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) = b

type family Sel3' a
type instance Sel3' (a,b,c)                         = c
type instance Sel3' (a,b,c,d)                       = c
type instance Sel3' (a,b,c,d,e)                     = c
type instance Sel3' (a,b,c,d,e,f)                   = c
type instance Sel3' (a,b,c,d,e,f,g)                 = c
type instance Sel3' (a,b,c,d,e,f,g,h)               = c
type instance Sel3' (a,b,c,d,e,f,g,h,i)             = c
type instance Sel3' (a,b,c,d,e,f,g,h,i,j)           = c
type instance Sel3' (a,b,c,d,e,f,g,h,i,j,k)         = c
type instance Sel3' (a,b,c,d,e,f,g,h,i,j,k,l)       = c
type instance Sel3' (a,b,c,d,e,f,g,h,i,j,k,l,m)     = c
type instance Sel3' (a,b,c,d,e,f,g,h,i,j,k,l,m,n)   = c
type instance Sel3' (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) = c

type family Sel4' a
type instance Sel4' (a,b,c,d)                       = d
type instance Sel4' (a,b,c,d,e)                     = d
type instance Sel4' (a,b,c,d,e,f)                   = d
type instance Sel4' (a,b,c,d,e,f,g)                 = d
type instance Sel4' (a,b,c,d,e,f,g,h)               = d
type instance Sel4' (a,b,c,d,e,f,g,h,i)             = d
type instance Sel4' (a,b,c,d,e,f,g,h,i,j)           = d
type instance Sel4' (a,b,c,d,e,f,g,h,i,j,k)         = d
type instance Sel4' (a,b,c,d,e,f,g,h,i,j,k,l)       = d
type instance Sel4' (a,b,c,d,e,f,g,h,i,j,k,l,m)     = d
type instance Sel4' (a,b,c,d,e,f,g,h,i,j,k,l,m,n)   = d
type instance Sel4' (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) = d

type family Sel5' a
type instance Sel5' (a,b,c,d,e)                     = e
type instance Sel5' (a,b,c,d,e,f)                   = e
type instance Sel5' (a,b,c,d,e,f,g)                 = e
type instance Sel5' (a,b,c,d,e,f,g,h)               = e
type instance Sel5' (a,b,c,d,e,f,g,h,i)             = e
type instance Sel5' (a,b,c,d,e,f,g,h,i,j)           = e
type instance Sel5' (a,b,c,d,e,f,g,h,i,j,k)         = e
type instance Sel5' (a,b,c,d,e,f,g,h,i,j,k,l)       = e
type instance Sel5' (a,b,c,d,e,f,g,h,i,j,k,l,m)     = e
type instance Sel5' (a,b,c,d,e,f,g,h,i,j,k,l,m,n)   = e
type instance Sel5' (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) = e

type family Sel6' a
type instance Sel6' (a,b,c,d,e,f)                   = f
type instance Sel6' (a,b,c,d,e,f,g)                 = f
type instance Sel6' (a,b,c,d,e,f,g,h)               = f
type instance Sel6' (a,b,c,d,e,f,g,h,i)             = f
type instance Sel6' (a,b,c,d,e,f,g,h,i,j)           = f
type instance Sel6' (a,b,c,d,e,f,g,h,i,j,k)         = f
type instance Sel6' (a,b,c,d,e,f,g,h,i,j,k,l)       = f
type instance Sel6' (a,b,c,d,e,f,g,h,i,j,k,l,m)     = f
type instance Sel6' (a,b,c,d,e,f,g,h,i,j,k,l,m,n)   = f
type instance Sel6' (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) = f

type family Sel7' a
type instance Sel7' (a,b,c,d,e,f,g)                 = g
type instance Sel7' (a,b,c,d,e,f,g,h)               = g
type instance Sel7' (a,b,c,d,e,f,g,h,i)             = g
type instance Sel7' (a,b,c,d,e,f,g,h,i,j)           = g
type instance Sel7' (a,b,c,d,e,f,g,h,i,j,k)         = g
type instance Sel7' (a,b,c,d,e,f,g,h,i,j,k,l)       = g
type instance Sel7' (a,b,c,d,e,f,g,h,i,j,k,l,m)     = g
type instance Sel7' (a,b,c,d,e,f,g,h,i,j,k,l,m,n)   = g
type instance Sel7' (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) = g

type family Sel8' a
type instance Sel8' (a,b,c,d,e,f,g,h)               = h
type instance Sel8' (a,b,c,d,e,f,g,h,i)             = h
type instance Sel8' (a,b,c,d,e,f,g,h,i,j)           = h
type instance Sel8' (a,b,c,d,e,f,g,h,i,j,k)         = h
type instance Sel8' (a,b,c,d,e,f,g,h,i,j,k,l)       = h
type instance Sel8' (a,b,c,d,e,f,g,h,i,j,k,l,m)     = h
type instance Sel8' (a,b,c,d,e,f,g,h,i,j,k,l,m,n)   = h
type instance Sel8' (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) = h

type family Sel9' a
type instance Sel9' (a,b,c,d,e,f,g,h,i)             = i
type instance Sel9' (a,b,c,d,e,f,g,h,i,j)           = i
type instance Sel9' (a,b,c,d,e,f,g,h,i,j,k)         = i
type instance Sel9' (a,b,c,d,e,f,g,h,i,j,k,l)       = i
type instance Sel9' (a,b,c,d,e,f,g,h,i,j,k,l,m)     = i
type instance Sel9' (a,b,c,d,e,f,g,h,i,j,k,l,m,n)   = i
type instance Sel9' (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) = i

type family Sel10' a
type instance Sel10' (a,b,c,d,e,f,g,h,i,j)           = j
type instance Sel10' (a,b,c,d,e,f,g,h,i,j,k)         = j
type instance Sel10' (a,b,c,d,e,f,g,h,i,j,k,l)       = j
type instance Sel10' (a,b,c,d,e,f,g,h,i,j,k,l,m)     = j
type instance Sel10' (a,b,c,d,e,f,g,h,i,j,k,l,m,n)   = j
type instance Sel10' (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) = j

type family Sel11' a
type instance Sel11' (a,b,c,d,e,f,g,h,i,j,k)         = k
type instance Sel11' (a,b,c,d,e,f,g,h,i,j,k,l)       = k
type instance Sel11' (a,b,c,d,e,f,g,h,i,j,k,l,m)     = k
type instance Sel11' (a,b,c,d,e,f,g,h,i,j,k,l,m,n)   = k
type instance Sel11' (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) = k

type family Sel12' a
type instance Sel12' (a,b,c,d,e,f,g,h,i,j,k,l)       = l
type instance Sel12' (a,b,c,d,e,f,g,h,i,j,k,l,m)     = l
type instance Sel12' (a,b,c,d,e,f,g,h,i,j,k,l,m,n)   = l
type instance Sel12' (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) = l

type family Sel13' a
type instance Sel13' (a,b,c,d,e,f,g,h,i,j,k,l,m)     = m
type instance Sel13' (a,b,c,d,e,f,g,h,i,j,k,l,m,n)   = m
type instance Sel13' (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) = m

type family Sel14' a
type instance Sel14' (a,b,c,d,e,f,g,h,i,j,k,l,m,n)   = n
type instance Sel14' (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) = n

type family Sel15' a
type instance Sel15' (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) = o

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
    Sel8 :: (Sel8 a b, Sel8' a ~ b) => Select (a :-> Full b)
    Sel9 :: (Sel9 a b, Sel9' a ~ b) => Select (a :-> Full b)
    Sel10 :: (Sel10 a b, Sel10' a ~ b) => Select (a :-> Full b)
    Sel11 :: (Sel11 a b, Sel11' a ~ b) => Select (a :-> Full b)
    Sel12 :: (Sel12 a b, Sel12' a ~ b) => Select (a :-> Full b)
    Sel13 :: (Sel13 a b, Sel13' a ~ b) => Select (a :-> Full b)
    Sel14 :: (Sel14 a b, Sel14' a ~ b) => Select (a :-> Full b)
    Sel15 :: (Sel15 a b, Sel15' a ~ b) => Select (a :-> Full b)

instance Constrained Select
  where
    {-# SPECIALIZE instance Constrained Select #-}
    {-# INLINE exprDict #-}
    type Sat Select = Top
    exprDict = const Dict

instance Semantic Select
  where
    {-# SPECIALIZE instance Semantic Select #-}
    {-# INLINABLE semantics #-}
    semantics Sel1 = Sem "sel1" sel1
    semantics Sel2 = Sem "sel2" sel2
    semantics Sel3 = Sem "sel3" sel3
    semantics Sel4 = Sem "sel4" sel4
    semantics Sel5 = Sem "sel5" sel5
    semantics Sel6 = Sem "sel6" sel6
    semantics Sel7 = Sem "sel7" sel7
    semantics Sel8 = Sem "sel8" sel8
    semantics Sel9 = Sem "sel9" sel9
    semantics Sel10 = Sem "sel10" sel10
    semantics Sel11 = Sem "sel11" sel11
    semantics Sel12 = Sem "sel12" sel12
    semantics Sel13 = Sem "sel13" sel13
    semantics Sel14 = Sem "sel14" sel14
    semantics Sel15 = Sem "sel15" sel15

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
selectPos Sel8 = 8
selectPos Sel9 = 9
selectPos Sel10 = 10
selectPos Sel11 = 11
selectPos Sel12 = 12
selectPos Sel13 = 13
selectPos Sel14 = 14
selectPos Sel15 = 15
