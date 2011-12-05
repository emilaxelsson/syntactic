{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module MuFeldspar.Core where



import Data.Bits (Bits)
import qualified Data.Bits as Bits
import Data.Complex hiding (Complex)
import qualified Data.Complex as C
import Data.List
import Data.Typeable

import Language.Syntactic
import Language.Syntactic.Constructs.Symbol
import Language.Syntactic.Constructs.Literal
import Language.Syntactic.Constructs.Condition
import Language.Syntactic.Constructs.Tuple
import Language.Syntactic.Constructs.Binding
import Language.Syntactic.Constructs.Binding.HigherOrder



--------------------------------------------------------------------------------
-- * Types
--------------------------------------------------------------------------------

-- | Set of supported types
class    (Eq a, Show a, Typeable a) => Type a
instance (Eq a, Show a, Typeable a) => Type a

type Length = Int
type Index  = Int



--------------------------------------------------------------------------------
-- * Numeric functions
--------------------------------------------------------------------------------

data NUM a
  where
    Abs  :: (Type a, Num a) => NUM (a :-> Full a)
    Sign :: (Type a, Num a) => NUM (a :-> Full a)
    Add  :: (Type a, Num a) => NUM (a :-> a :-> Full a)
    Sub  :: (Type a, Num a) => NUM (a :-> a :-> Full a)
    Mul  :: (Type a, Num a) => NUM (a :-> a :-> Full a)

instance IsSymbol NUM
  where
    toSym Abs  = Sym "abs" abs
    toSym Sign = Sym "signum" signum
    toSym Add  = Sym "(+)" (+)
    toSym Sub  = Sym "(-)" (-)
    toSym Mul  = Sym "(*)" (*)

instance ExprEq   NUM where exprEq = exprEqSym; exprHash = exprHashSym
instance Render   NUM where renderPart = renderPartSym
instance Eval     NUM where evaluate   = evaluateSym
instance ToTree   NUM
instance EvalBind NUM where evalBindSym = evalBindSymDefault

instance MaybeWitnessSat Poly NUM where maybeWitnessSat _ _ = Just SatWit



--------------------------------------------------------------------------------
-- * Integral functions
--------------------------------------------------------------------------------

data INTEGRAL a
  where
    Div :: (Type a, Integral a) => INTEGRAL (a :-> a :-> Full a)
    Mod :: (Type a, Integral a) => INTEGRAL (a :-> a :-> Full a)
    Exp :: (Type a, Integral a) => INTEGRAL (a :-> a :-> Full a)

instance IsSymbol INTEGRAL
  where
    toSym Div = Sym "div" div
    toSym Mod = Sym "mod" mod
    toSym Exp = Sym "(^)" (^)

instance ExprEq   INTEGRAL where exprEq = exprEqSym; exprHash = exprHashSym
instance Render   INTEGRAL where renderPart = renderPartSym
instance Eval     INTEGRAL where evaluate   = evaluateSym
instance ToTree   INTEGRAL
instance EvalBind INTEGRAL where evalBindSym = evalBindSymDefault

instance MaybeWitnessSat Poly INTEGRAL where maybeWitnessSat _ _ = Just SatWit



--------------------------------------------------------------------------------
-- * Fractional functions
--------------------------------------------------------------------------------

data FRACTIONAL a
  where
    FDiv :: (Type a, Fractional a) => FRACTIONAL (a :-> a :-> Full a)

instance IsSymbol FRACTIONAL
  where
    toSym FDiv = Sym "(/)" (/)

instance ExprEq   FRACTIONAL where exprEq = exprEqSym; exprHash = exprHashSym
instance Render   FRACTIONAL where renderPart = renderPartSym
instance Eval     FRACTIONAL where evaluate   = evaluateSym
instance ToTree   FRACTIONAL
instance EvalBind FRACTIONAL where evalBindSym = evalBindSymDefault

instance MaybeWitnessSat Poly FRACTIONAL where maybeWitnessSat _ _ = Just SatWit



--------------------------------------------------------------------------------
-- * Conversion functions
--------------------------------------------------------------------------------

data Conversion a
  where
    I2N :: (Type a, Integral a, Type b, Num b) => Conversion (a :-> Full b)
    F2I :: (Type a, Integral a)                => Conversion (Float :-> Full a)
    B2I :: (Type a, Integral a)                => Conversion (Bool :-> Full a)

instance IsSymbol Conversion
  where
    toSym I2N = Sym "i2n" (fromInteger.toInteger)
    toSym F2I = Sym "f2i" truncate
    toSym B2I = Sym "b2i" (\b -> if b then 1 else 0)

instance ExprEq   Conversion where exprEq = exprEqSym; exprHash = exprHashSym
instance Render   Conversion where renderPart = renderPartSym
instance Eval     Conversion where evaluate   = evaluateSym
instance ToTree   Conversion
instance EvalBind Conversion where evalBindSym = evalBindSymDefault

instance MaybeWitnessSat Poly Conversion where maybeWitnessSat _ _ = Just SatWit



--------------------------------------------------------------------------------
-- * Complex numbers
--------------------------------------------------------------------------------

type Complex = C.Complex Float

data COMPLEX a
  where
    Complex   :: COMPLEX (Float :-> Float :-> Full Complex)
    RealPart  :: COMPLEX (Complex :-> Full Float)
    ImagPart  :: COMPLEX (Complex :-> Full Float)
    MkPolar   :: COMPLEX (Float :-> Float :-> Full Complex)
    Magnitude :: COMPLEX (Complex :-> Full Float)
    Phase     :: COMPLEX (Complex :-> Full Float)

instance IsSymbol COMPLEX
  where
    toSym Complex   = Sym "complex"   (:+)
    toSym RealPart  = Sym "realPart"  realPart
    toSym ImagPart  = Sym "imagPart"  imagPart
    toSym MkPolar   = Sym "mkPolar"   mkPolar
    toSym Magnitude = Sym "magnitude" magnitude
    toSym Phase     = Sym "phase"     phase

instance ExprEq   COMPLEX where exprEq = exprEqSym; exprHash = exprHashSym
instance Render   COMPLEX where renderPart = renderPartSym
instance Eval     COMPLEX where evaluate   = evaluateSym
instance ToTree   COMPLEX
instance EvalBind COMPLEX where evalBindSym = evalBindSymDefault

instance MaybeWitnessSat Poly COMPLEX where maybeWitnessSat _ _ = Just SatWit



--------------------------------------------------------------------------------
-- * Bit manipulation
--------------------------------------------------------------------------------

data BITS a
  where
    Complement  :: (Type a, Bits a) => BITS (a :-> Full a)
    BitAnd      :: (Type a, Bits a) => BITS (a :-> a :-> Full a)
    BitOr       :: (Type a, Bits a) => BITS (a :-> a :-> Full a)
    Xor         :: (Type a, Bits a) => BITS (a :-> a :-> Full a)
    ShiftL      :: (Type a, Bits a) => BITS (a :-> Index :-> Full a)
    ShiftR      :: (Type a, Bits a) => BITS (a :-> Index :-> Full a)
    RotateL     :: (Type a, Bits a) => BITS (a :-> Index :-> Full a)
    RotateR     :: (Type a, Bits a) => BITS (a :-> Index :-> Full a)
    BitSize     :: (Type a, Bits a) => BITS (a :-> Full Index)
    ReverseBits :: (Type a, Bits a) => BITS (a :-> Full a)

instance IsSymbol BITS
  where
    toSym Complement  = Sym "complement" Bits.complement
    toSym BitAnd      = Sym "(.&.)" (Bits..&.)
    toSym BitOr       = Sym "(.|.)" (Bits..|.)
    toSym Xor         = Sym "xor" Bits.xor
    toSym ShiftL      = Sym "shiftL" Bits.shiftL
    toSym ShiftR      = Sym "shiftR" Bits.shiftR
    toSym RotateL     = Sym "rotateL" Bits.rotateL
    toSym RotateR     = Sym "rotateR" Bits.rotateR
    toSym BitSize     = Sym "bitSize" Bits.bitSize
    toSym ReverseBits = Sym "reverseBits" reverseBits
      where
        reverseBits :: Bits.Bits b => b -> b
        reverseBits b = revLoop b 0 (0 `asTypeOf` b)
          where
            bitSize = Bits.bitSize b
            revLoop b i n
              | i Prelude.>= bitSize = n
              | Bits.testBit b i =
                  revLoop b (i+1) (Bits.setBit n (bitSize - i - 1))
              | otherwise = revLoop b (i+1) n



instance ExprEq   BITS where exprEq = exprEqSym; exprHash = exprHashSym
instance Render   BITS where renderPart = renderPartSym
instance Eval     BITS where evaluate   = evaluateSym
instance ToTree   BITS
instance EvalBind BITS where evalBindSym = evalBindSymDefault

instance MaybeWitnessSat Poly BITS where maybeWitnessSat _ _ = Just SatWit



--------------------------------------------------------------------------------
-- * Logic operations
--------------------------------------------------------------------------------

data Logic a
  where
    Eq  :: Type a => Logic (a :-> a :-> Full Bool)
    Not :: Logic (Bool :-> Full Bool)
    And :: Logic (Bool :-> Bool :-> Full Bool)
    Or  :: Logic (Bool :-> Bool :-> Full Bool)

instance IsSymbol Logic
  where
    toSym Eq    = Sym "(==)" (==)
    toSym Not   = Sym "not" not
    toSym And   = Sym "(&&)" (&&)
    toSym Or    = Sym "(||)" (||)

instance ExprEq   Logic where exprEq = exprEqSym; exprHash = exprHashSym
instance Render   Logic where renderPart = renderPartSym
instance Eval     Logic where evaluate   = evaluateSym
instance ToTree   Logic
instance EvalBind Logic where evalBindSym = evalBindSymDefault

instance MaybeWitnessSat Poly Logic where maybeWitnessSat _ _ = Just SatWit



--------------------------------------------------------------------------------
-- * Functions on ordered types
--------------------------------------------------------------------------------

data ORD a
  where
    Less    :: (Type a, Ord a) => ORD (a :-> a :-> Full Bool)
    LEQ     :: (Type a, Ord a) => ORD (a :-> a :-> Full Bool)
    Greater :: (Type a, Ord a) => ORD (a :-> a :-> Full Bool)
    GEQ     :: (Type a, Ord a) => ORD (a :-> a :-> Full Bool)
    Min     :: (Type a, Ord a) => ORD (a :-> a :-> Full a)
    Max     :: (Type a, Ord a) => ORD (a :-> a :-> Full a)

instance IsSymbol ORD
  where
    toSym Less    = Sym "(<)" (<)
    toSym LEQ     = Sym "(<=)" (<=)
    toSym Greater = Sym "(>)" (>)
    toSym GEQ     = Sym "(>=)" (>=)
    toSym Min     = Sym "min" min
    toSym Max     = Sym "max" max

instance ExprEq   ORD where exprEq = exprEqSym; exprHash = exprHashSym
instance Render   ORD where renderPart = renderPartSym
instance Eval     ORD where evaluate   = evaluateSym
instance ToTree   ORD
instance EvalBind ORD where evalBindSym = evalBindSymDefault

instance MaybeWitnessSat Poly ORD where maybeWitnessSat _ _ = Just SatWit



--------------------------------------------------------------------------------
-- * Array functions
--------------------------------------------------------------------------------

data Array a
  where
    GetLength :: Type a => Array ([a] :-> Full Length)
    SetLength :: Type a => Array (Length :-> [a] :-> Full [a])
    GetIx     :: Type a => Array ([a] :-> Index :-> Full a)

instance IsSymbol Array
  where
    toSym GetLength = Sym "getLength" length
    toSym SetLength = Sym "setLength" take
    toSym GetIx     = Sym "getIx" getIx
      where
        getIx as i
            | (i >= length as) || (i < 0) = error "getIx: index out of bounds"
            | otherwise                   = as !! i

instance ExprEq   Array where exprEq = exprEqSym; exprHash = exprHashSym
instance Render   Array where renderPart = renderPartSym
instance Eval     Array where evaluate   = evaluateSym
instance ToTree   Array
instance EvalBind Array where evalBindSym = evalBindSymDefault

instance MaybeWitnessSat Poly Array where maybeWitnessSat _ _ = Just SatWit



--------------------------------------------------------------------------------
-- * Parallel arrays
--------------------------------------------------------------------------------

data Parallel a
  where
    Parallel :: Type a => Parallel (Length :-> (Index -> a) :-> Full [a])

instance IsSymbol Parallel
  where
    toSym Parallel = Sym "parallel" parallelEval
      where
        parallelEval len ixf = map ixf [0 .. len-1]

instance ExprEq   Parallel where exprEq = exprEqSym; exprHash = exprHashSym
instance Render   Parallel where renderPart = renderPartSym
instance Eval     Parallel where evaluate   = evaluateSym
instance ToTree   Parallel
instance EvalBind Parallel where evalBindSym = evalBindSymDefault

instance MaybeWitnessSat Poly Parallel where maybeWitnessSat _ _ = Just SatWit



--------------------------------------------------------------------------------
-- * Sequential arrays
--------------------------------------------------------------------------------

data Sequential a
  where
    Sequential :: (Type st, Type a) =>
        Sequential (Length :-> st :-> (Index -> st -> (a,st)) :-> Full [a])

instance IsSymbol Sequential
  where
    toSym Sequential = Sym "sequential" sequentialEval
      where
        sequentialEval l init step = snd $ mapAccumL evalStep init [0 .. l-1]
          where
            evalStep st i = (st',a) where (a,st') = step i st

instance ExprEq   Sequential where exprEq = exprEqSym; exprHash = exprHashSym
instance Render   Sequential where renderPart = renderPartSym
instance Eval     Sequential where evaluate   = evaluateSym
instance ToTree   Sequential
instance EvalBind Sequential where evalBindSym = evalBindSymDefault

instance MaybeWitnessSat Poly Sequential where maybeWitnessSat _ _ = Just SatWit



--------------------------------------------------------------------------------
-- * For loops
--------------------------------------------------------------------------------

data ForLoop a
  where
    ForLoop :: Type st =>
        ForLoop (Length :-> st :-> (Index -> st -> st) :-> Full st)

instance IsSymbol ForLoop
  where
    toSym ForLoop = Sym "forLoop" forLoopEval
      where
        forLoopEval len init body = foldl (flip body) init [0 .. len-1]

instance ExprEq   ForLoop where exprEq = exprEqSym; exprHash = exprHashSym
instance Render   ForLoop where renderPart = renderPartSym
instance Eval     ForLoop where evaluate   = evaluateSym
instance ToTree   ForLoop
instance EvalBind ForLoop where evalBindSym = evalBindSymDefault

instance MaybeWitnessSat Poly ForLoop where maybeWitnessSat _ _ = Just SatWit



--------------------------------------------------------------------------------
-- * Feldspar domain
--------------------------------------------------------------------------------

type FeldDomain
    =   Literal Poly
    :+: Condition Poly
    :+: Tuple Poly
    :+: Select Poly
    :+: Let Poly Poly
    :+: NUM
    :+: INTEGRAL
    :+: FRACTIONAL
    :+: Conversion
    :+: COMPLEX
    :+: BITS
    :+: Logic
    :+: ORD
    :+: Array
    :+: Parallel
    :+: Sequential
    :+: ForLoop

type FeldDomainAll = HODomain Poly FeldDomain

newtype Data a = Data { unData :: ASTF FeldDomainAll a }

instance Type a => Syntactic (Data a) FeldDomainAll
  where
    type Internal (Data a) = a
    desugar = unData
    sugar   = Data

-- | Specialization of the 'Syntactic' class for the Feldspar domain
class    (Syntactic a FeldDomainAll, Type (Internal a)) => Syntax a
instance (Syntactic a FeldDomainAll, Type (Internal a)) => Syntax a

instance Type a => Eq (Data a)
  where
    Data a == Data b = alphaEq poly (reify poly a) (reify poly b)

instance Type a => Show (Data a)
  where
    show (Data a) = render $ reify poly a



--------------------------------------------------------------------------------
-- * Back ends
--------------------------------------------------------------------------------

printFeld :: Syntactic a FeldDomainAll => a -> IO ()
printFeld = printExpr . reify poly

drawFeld :: Syntactic a FeldDomainAll => a -> IO ()
drawFeld = drawAST . reify poly

eval :: Syntactic a FeldDomainAll => a -> Internal a
eval = evalBind . reify poly

