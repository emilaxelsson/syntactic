{-# OPTIONS_GHC -fcontext-stack=30 #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}

module MuFeldspar.Frontend where



import Data.Bits (Bits)

import Language.Syntactic
import Language.Syntactic.Constructs.Symbol
import Language.Syntactic.Constructs.Literal
import Language.Syntactic.Constructs.Condition
import Language.Syntactic.Constructs.TupleSyntacticPoly
import Language.Syntactic.Constructs.Binding
import Language.Syntactic.Constructs.Binding.HigherOrder

import MuFeldspar.Core



value :: Syntax a => Internal a -> a
value = sugarSymCtx poly . Literal

false :: Data Bool
false = value False

true :: Data Bool
true = value True

-- | For types containing some kind of \"thunk\", this function can be used to
-- force computation
force :: Syntax a => a -> a
force = resugar

desugarD :: Syntax a => a -> Data (Internal a)
desugarD = resugar

sugarD :: Syntax a => Data (Internal a) -> a
sugarD = resugar

share :: (Syntax a, Syntax b) => a -> (a -> b) -> b
share = sugarSym (letBind poly)

instance (Type a, Num a) => Num (Data a)
  where
    fromInteger = value . fromInteger
    abs         = sugarSym Abs
    signum      = sugarSym Sign
    (+)         = sugarSym Add
    (-)         = sugarSym Sub
    (*)         = sugarSym Mul

div :: (Type a, Integral a) => Data a -> Data a -> Data a
div = sugarSym Div

mod :: (Type a, Integral a) => Data a -> Data a -> Data a
mod = sugarSym Mod

(^) :: (Type a, Integral a) => Data a -> Data a -> Data a
(^) = sugarSym Exp

instance (Type a, Fractional a) => Fractional (Data a)
  where
    fromRational = value . fromRational
    (/)          = sugarSym FDiv

i2n :: (Type a, Integral a, Type b, Num b) => Data a -> Data b
i2n = sugarSym I2N

f2i :: (Type a, Integral a) => Data Float -> Data a
f2i = sugarSym F2I

b2i :: (Type a, Integral a) => Data Bool -> Data a
b2i = sugarSym B2I

complex :: Data Float -> Data Float -> Data Complex
complex = sugarSym Complex

realPart :: Data Complex -> Data Float
realPart = sugarSym RealPart

imagPart :: Data Complex -> Data Float
imagPart = sugarSym ImagPart

mkPolar :: Data Float -> Data Float -> Data Complex
mkPolar = sugarSym MkPolar

magnitude :: Data Complex -> Data Float
magnitude = sugarSym Magnitude

phase :: Data Complex -> Data Float
phase = sugarSym Phase

polar :: Data Complex -> (Data Float, Data Float)
polar a = (magnitude a, phase a)

cis :: Data Float -> Data Complex
cis = mkPolar 1



complement :: (Type a, Bits a) => Data a -> Data a
complement = sugarSym Complement

(.&.) :: (Type a, Bits a) => Data a -> Data a -> Data a
(.&.) = sugarSym BitAnd

(.|.) :: (Type a, Bits a) => Data a -> Data a -> Data a
(.|.) = sugarSym BitOr

xor :: (Type a, Bits a) => Data a -> Data a -> Data a
xor = sugarSym Xor

shiftL :: (Type a, Bits a) => Data a -> Data Index -> Data a
shiftL = sugarSym ShiftL

shiftR :: (Type a, Bits a) => Data a -> Data Index -> Data a
shiftR = sugarSym ShiftR

(<<), (>>) :: (Type a, Bits a) => Data a -> Data Index -> Data a
(<<) = shiftL
(>>) = shiftR

infixl 5 <<, >>

rotateL :: (Type a, Bits a) => Data a -> Data Index -> Data a
rotateL = sugarSym RotateL

rotateR :: (Type a, Bits a) => Data a -> Data Index -> Data a
rotateR = sugarSym RotateR

bitSize :: (Type a, Bits a) => Data a -> Data Index
bitSize = sugarSym BitSize

reverseBits :: (Type a, Bits a) => Data a -> Data a
reverseBits = sugarSym ReverseBits

(==) :: Type a => Data a -> Data a -> Data Bool
(==) = sugarSym Eq

not :: Data Bool -> Data Bool
not = sugarSym Not

(&&) :: Data Bool -> Data Bool -> Data Bool
(&&) = sugarSym And

(||) :: Data Bool -> Data Bool -> Data Bool
(||) = sugarSym Or

(<) :: (Type a, Ord a) => Data a -> Data a -> Data Bool
(<) = sugarSym Less

(<=) :: (Type a, Ord a) => Data a -> Data a -> Data Bool
(<=) = sugarSym LEQ

(>) :: (Type a, Ord a) => Data a -> Data a -> Data Bool
(>) = sugarSym Greater

(>=) :: (Type a, Ord a) => Data a -> Data a -> Data Bool
(>=) = sugarSym GEQ

max :: (Type a, Ord a) => Data a -> Data a -> Data a
max = sugarSym Max

min :: (Type a, Ord a) => Data a -> Data a -> Data a
min = sugarSym Min

(?) :: Syntax a => Data Bool -> (a,a) -> a
cond ? (t,e) = sugarSymCtx poly Condition cond t e



parallel :: Type a => Data Length -> (Data Index -> Data a) -> Data [a]

parallel len ixf
    | getIx :$: arr :$: var0 <- body
    , Just GetIx <- project getIx
    , Just (Variable 0) <- prjCtx poly var0
    = setLength len $ Data arr
  where
    body = unData $ ixf $ Data $ inject (Variable 0 `withContext` poly)
  -- This case is an optimization that's included because it has a great effect
  -- on the size of the generated code.

parallel len ixf = sugarSym Parallel len ixf



sequential :: (Type a, Syntax st) =>
    Data Length -> st -> (Data Index -> st -> (Data a, st)) -> Data [a]
sequential = sugarSym Sequential

forLoop :: Syntax st => Data Length -> st -> (Data Index -> st -> st) -> st
forLoop = sugarSym ForLoop

getLength :: Type a => Data [a] -> Data Length
getLength = sugarSym GetLength



setLength :: Type a => Data Length -> Data [a] -> Data [a]

setLength (desugar -> ((project -> Just GetLength) :$: arr')) arr
    | alphaEq poly (reify poly arr') (reify poly $ unData arr)
    = arr
  -- This case is an optimization that's needed for the optimization of
  -- 'parallel' to work properly.

setLength arr len = sugarSym SetLength arr len



getIx :: Type a => Data [a] -> Data Index -> Data a
getIx = sugarSym GetIx

