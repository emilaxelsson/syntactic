{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

-- | A simple vector library for NanoFeldspar. The intention of this module is
-- to demonstrate how to add language features without extending the underlying
-- core language. By declaring 'Vector' as syntactic sugar, vector operations
-- can work seamlessly with the functions of the core language.
--
-- An interesting aspect of the 'Vector' interface is that the only operation
-- that produces a core language array (i.e. allocates memory) is 'freezeVector'
-- (which uses 'parallel'). This means that expressions not involving
-- 'freezeVector' are guaranteed to be fused. (Note, however, that
-- 'freezeVector' is introduced by 'desugar', which in turn is used by many
-- other functions.)

module NanoFeldspar.Vector where



import Prelude hiding (length, map, (==), max, min, reverse, sum, unzip, zip, zipWith)

import Language.Syntactic (Syntactic (..), resugar)

import NanoFeldspar.Core



data Vector a
  where
    Indexed :: Data Length -> (Data Index -> a) -> Vector a

instance Syntax a => Syntactic (Vector a)
  where
    {-# SPECIALIZE instance Syntax a => Syntactic (Vector a) #-}
    {-# INLINABLE desugar #-}
    {-# INLINABLE sugar #-}
    type Domain (Vector a)   = FeldDomainAll
    type Internal (Vector a) = [Internal a]
    desugar = desugar . freezeVector . map resugar
    sugar   = map resugar . unfreezeVector . sugar



length :: Vector a -> Data Length
length (Indexed len _) = len

indexed :: Data Length -> (Data Index -> a) -> Vector a
indexed = Indexed

index :: Vector a -> Data Index -> a
index (Indexed _ ixf) = ixf

(!) :: Vector a -> Data Index -> a
Indexed _ ixf ! i = ixf i

infixl 9 !

freezeVector :: Type a => Vector (Data a) -> Data [a]
freezeVector vec = parallel (length vec) (index vec)

unfreezeVector :: Type a => Data [a] -> Vector (Data a)
unfreezeVector arr = Indexed (arrLength arr) (getIx arr)

zip :: Vector a -> Vector b -> Vector (a,b)
zip a b = indexed (length a `min` length b) (\i -> (index a i, index b i))

unzip :: Vector (a,b) -> (Vector a, Vector b)
unzip ab = (indexed len (fst . index ab), indexed len (snd . index ab))
  where
    len = length ab

permute :: (Data Length -> Data Index -> Data Index) -> (Vector a -> Vector a)
permute perm vec = indexed len (index vec . perm len)
  where
    len = length vec

reverse :: Vector a -> Vector a
reverse = permute $ \len i -> len-i-1

(...) :: Data Index -> Data Index -> Vector (Data Index)
l ... h = indexed (h-l+1) (+l)

map :: (a -> b) -> Vector a -> Vector b
map f (Indexed len ixf) = Indexed len (f . ixf)

zipWith :: (a -> b -> c) -> Vector a -> Vector b -> Vector c
zipWith f a b = map (uncurry f) $ zip a b

fold :: Syntax b => (a -> b -> b) -> b -> Vector a -> b
fold f b (Indexed len ixf) = forLoop len b (\i st -> f (ixf i) st)

sum :: (Num a, Syntax a) => Vector a -> a
sum = fold (+) 0

type Matrix a = Vector (Vector (Data a))

-- | Transpose of a matrix. Assumes that the number of rows is > 0.
transpose :: Type a => Matrix a -> Matrix a
transpose a = indexed (length (a!0)) $ \k -> indexed (length a) $ \l -> a ! l ! k
