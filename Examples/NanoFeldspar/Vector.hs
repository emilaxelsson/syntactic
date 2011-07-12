{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module NanoFeldspar.Vector where



import Prelude hiding (length, map, max, min, reverse, sum, unzip, zip, zipWith)
import qualified Prelude

import Language.Syntactic
import Language.Syntactic.Features.Binding.HigherOrder

import NanoFeldspar.Core



data Vector a
  where
    Indexed :: Data Length -> (Data Index -> a) -> Vector a

instance Syntax a =>
    Syntactic (Vector a) (HOLambda FeldDomain :+: Variable :+: FeldDomain)
  where
    type Internal (Vector a) = [Internal a]
    desugar = desugar . freezeVector . map resugar
    sugar   = map resugar . unfreezeVector . sugar



length :: Vector a -> Data Length
length (Indexed len _) = len

indexed :: Data Length -> (Data Index -> a) -> Vector a
indexed = Indexed

index :: Vector a -> Data Index -> a
index (Indexed _ ixf) = ixf

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

sum :: (Type a, Num a) => Vector (Data a) -> Data a
sum = fold (+) 0

