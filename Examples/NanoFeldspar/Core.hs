{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- | A minimal Feldspar core language implementation. The intention of this
-- module is to demonstrate how to quickly make a language prototype using
-- syntactic.
--
-- A more realistic implementation would use custom contexts to restrict the
-- types at which constructors operate. Currently, all general constructs (such
-- as 'Literal' and 'Tuple') use a 'SimpleCtx' context, which means that the
-- types are quite unrestricted. A real implementation would also probably use
-- custom types for primitive functions, since the 'Sym' construct is quite
-- unsafe (uses only a 'String' to distinguish between functions).

module NanoFeldspar.Core where



import Data.Typeable

import Language.Syntactic
import Language.Syntactic.Constructs.Symbol
import Language.Syntactic.Constructs.Literal
import Language.Syntactic.Constructs.Condition
import Language.Syntactic.Constructs.Tuple
import Language.Syntactic.Constructs.Binding
import Language.Syntactic.Constructs.Binding.HigherOrder
import Language.Syntactic.Sharing.SimpleCodeMotion



--------------------------------------------------------------------------------
-- * Types
--------------------------------------------------------------------------------

-- | Convenient class alias
class    (Ord a, Show a, Typeable a) => Type a
instance (Ord a, Show a, Typeable a) => Type a

type Length = Int
type Index  = Int



--------------------------------------------------------------------------------
-- * Parallel arrays
--------------------------------------------------------------------------------

data Parallel a
  where
    Parallel :: Type a => Parallel (Length :-> (Index -> a) :-> Full [a])

instance WitnessCons Parallel
  where
    witnessCons Parallel = ConsWit

instance WitnessSat Parallel
  where
    type SatContext Parallel = SimpleCtx
    witnessSat Parallel = SatWit

instance MaybeWitnessSat SimpleCtx Parallel
  where
    maybeWitnessSat = maybeWitnessSatDefault

instance IsSymbol Parallel
  where
    toSym Parallel = Sym "parallel" parallel
      where
        parallel len ixf = map ixf [0 .. len-1]

instance ExprEq   Parallel where exprEq = exprEqSym; exprHash = exprHashSym
instance Render   Parallel where renderPart = renderPartSym
instance Eval     Parallel where evaluate   = evaluateSym
instance ToTree   Parallel
instance EvalBind Parallel where evalBindSym = evalBindSymDefault



--------------------------------------------------------------------------------
-- * For loops
--------------------------------------------------------------------------------

data ForLoop a
  where
    ForLoop :: Type st =>
        ForLoop (Length :-> st :-> (Index -> st -> st) :-> Full st)

instance WitnessCons ForLoop
  where
    witnessCons ForLoop = ConsWit

instance WitnessSat ForLoop
  where
    type SatContext ForLoop = SimpleCtx
    witnessSat ForLoop = SatWit

instance MaybeWitnessSat SimpleCtx ForLoop
  where
    maybeWitnessSat = maybeWitnessSatDefault

instance IsSymbol ForLoop
  where
    toSym ForLoop = Sym "forLoop" forLoop
      where
        forLoop len init body = foldl (flip body) init [0 .. len-1]

instance ExprEq   ForLoop where exprEq = exprEqSym; exprHash = exprHashSym
instance Render   ForLoop where renderPart = renderPartSym
instance Eval     ForLoop where evaluate   = evaluateSym
instance ToTree   ForLoop
instance EvalBind ForLoop where evalBindSym = evalBindSymDefault



--------------------------------------------------------------------------------
-- * Feldspar domain
--------------------------------------------------------------------------------

-- | The Feldspar domain
type FeldDomain
    =   Sym SimpleCtx
    :+: Literal SimpleCtx
    :+: Condition SimpleCtx
    :+: Tuple SimpleCtx
    :+: Select SimpleCtx
    :+: Let SimpleCtx SimpleCtx
    :+: Parallel
    :+: ForLoop

type FeldDomainAll = HODomain SimpleCtx FeldDomain

newtype Data a = Data { unData :: ASTF FeldDomainAll a }

-- | Declaring 'Data' as syntactic sugar
instance Type a => Syntactic (Data a) FeldDomainAll
  where
    type Internal (Data a) = a
    desugar = unData
    sugar   = Data

-- | Specialization of the 'Syntactic' class for the Feldspar domain
class    (Syntactic a FeldDomainAll, Type (Internal a)) => Syntax a
instance (Syntactic a FeldDomainAll, Type (Internal a)) => Syntax a



--------------------------------------------------------------------------------
-- * Back ends
--------------------------------------------------------------------------------

-- | Print the expression
printFeld :: Syntactic a FeldDomainAll => a -> IO ()
printFeld = printExpr . reifySmart simpleCtx

-- | Draw the syntax tree
drawFeld :: Syntactic a FeldDomainAll => a -> IO ()
drawFeld = drawAST . reifySmart simpleCtx

-- | Evaluation
eval :: Syntactic a FeldDomainAll => a -> Internal a
eval = evalBind . reifySmart simpleCtx



--------------------------------------------------------------------------------
-- * Core library
--------------------------------------------------------------------------------

-- | Literal
value :: Syntax a => Internal a -> a
value = sugarSymCtx simpleCtx . Literal

false :: Data Bool
false = value False

true :: Data Bool
true = value True

-- | For types containing some kind of \"thunk\", this function can be used to
-- force computation
force :: Syntax a => a -> a
force = resugar

-- | Share a value using let binding
share :: (Syntax a, Syntax b) => a -> (a -> b) -> b
share = sugarSym (letBind simpleCtx)

-- | Alpha equivalence
instance Type a => Eq (Data a)
  where
    Data a == Data b =
        alphaEq simpleCtx (reify simpleCtx a) (reify simpleCtx b)

instance Type a => Show (Data a)
  where
    show (Data a) = render $ reify simpleCtx a

instance (Type a, Num a) => Num (Data a)
  where
    fromInteger = value . fromInteger
    abs         = sugarSymCtx simpleCtx $ Sym "abs" abs
    signum      = sugarSymCtx simpleCtx $ Sym "signum" signum
    (+)         = sugarSymCtx simpleCtx $ Sym "(+)" (+)
    (-)         = sugarSymCtx simpleCtx $ Sym "(-)" (-)
    (*)         = sugarSymCtx simpleCtx $ Sym "(*)" (*)

(?) :: Syntax a => Data Bool -> (a,a) -> a
cond ? (t,e) = sugarSymCtx simpleCtx Condition cond t e

-- | Parallel array
parallel :: Type a => Data Length -> (Data Index -> Data a) -> Data [a]
parallel = sugarSym Parallel

forLoop :: Syntax st => Data Length -> st -> (Data Index -> st -> st) -> st
forLoop = sugarSym ForLoop

arrLength :: Type a => Data [a] -> Data Length
arrLength = sugarSymCtx simpleCtx $ Sym "arrLength" Prelude.length

-- | Array indexing
getIx :: Type a => Data [a] -> Data Index -> Data a
getIx = sugarSymCtx simpleCtx $ Sym "getIx" eval
  where
    eval as i
        | i >= len || i < 0 = error "getIx: index out of bounds"
        | otherwise         = as !! i
      where
        len = Prelude.length as

not :: Data Bool -> Data Bool
not = sugarSymCtx simpleCtx $ Sym "not" Prelude.not

(==) :: Type a => Data a -> Data a -> Data Bool
(==) = sugarSymCtx simpleCtx $ Sym "(==)" (Prelude.==)

max :: Type a => Data a -> Data a -> Data a
max = sugarSymCtx simpleCtx $ Sym "max" Prelude.max

min :: Type a => Data a -> Data a -> Data a
min = sugarSymCtx simpleCtx $ Sym "min" Prelude.min

