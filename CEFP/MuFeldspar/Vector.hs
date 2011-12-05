{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module MuFeldspar.Vector where



import qualified Prelude

import Language.Syntactic
import Language.Syntactic.Constructs.Binding.HigherOrder

import MuFeldspar.Prelude
import MuFeldspar.Core
import MuFeldspar.Frontend



data Vector a
  where
    Indexed :: {length :: Data Length, index :: Data Index -> a } -> Vector a

instance Syntax a => Syntactic (Vector a) FeldDomainAll
  where
    type Internal (Vector a) = [Internal a]
    desugar = desugar . freezeVector . map resugar
    sugar   = map resugar . unfreezeVector . sugar

instance Functor Vector
  where
    fmap = map



indexed :: Data Length -> (Data Index -> a) -> Vector a
indexed = Indexed

freezeVector :: Type a => Vector (Data a) -> Data [a]
freezeVector vec = parallel (length vec) (index vec)

unfreezeVector :: Type a => Data [a] -> Vector (Data a)
unfreezeVector arr = Indexed (getLength arr) (getIx arr)

take :: Data Length -> Vector a -> Vector a
take n (Indexed l ixf) = indexed (min n l) ixf

drop :: Data Length -> Vector a -> Vector a
drop n (Indexed l ixf) = indexed (max (l-n) 0) (ixf . (+n))

splitAt :: Data Index -> Vector a -> (Vector a, Vector a)
splitAt n vec = (take n vec, drop n vec)

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

(...) :: (Type a, Integral a) => Data a -> Data a -> Vector (Data a)
l ... h = indexed (i2n $ h-l+1) ((+l) . i2n)

replicate :: Data Index -> a -> Vector a
replicate len a = indexed len (const a)

(++) :: Syntax a => Vector a -> Vector a -> Vector a
vec1 ++ vec2 = indexed len ixf
  where
    len = length vec1 + length vec2
    ixf i = i < length vec1 ? (index vec1 i, index vec2 (i-length vec1))

map :: (a -> b) -> Vector a -> Vector b
map f (Indexed len ixf) = indexed len (f . ixf)

zipWith :: (a -> b -> c) -> Vector a -> Vector b -> Vector c
zipWith f a b = map (uncurry f) $ zip a b

fold :: Syntax a => (a -> b -> a) -> a -> Vector b -> a
fold f a (Indexed len ixf) = forLoop len a (\i st -> f st (ixf i))

sum :: (Type a, Num a) => Vector (Data a) -> Data a
sum = fold (+) 0

