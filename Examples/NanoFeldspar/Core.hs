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
-- custom types for primitive functions, since 'Construct' is quite unsafe (uses
-- only a 'String' to distinguish between functions).

module NanoFeldspar.Core where



import Data.Typeable

import Language.Syntactic
import Language.Syntactic.Interpretation.Semantics
import Language.Syntactic.Constructs.Binding
import Language.Syntactic.Constructs.Binding.HigherOrder
import Language.Syntactic.Constructs.Condition
import Language.Syntactic.Constructs.Construct
import Language.Syntactic.Constructs.Literal
import Language.Syntactic.Constructs.Tuple
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

instance Semantic Parallel
  where
    semantics Parallel = Sem
        { semanticName = "parallel"
        , semanticEval = \len ixf -> map ixf [0 .. len-1]
        }

instance ExprEq   Parallel where exprEq = exprEqSem; exprHash = exprHashSem
instance Render   Parallel where renderPart = renderPartSem
instance Eval     Parallel where evaluate   = evaluateSem
instance ToTree   Parallel
instance EvalBind Parallel where evalBindSym = evalBindSymDefault

instance (AlphaEq dom dom dom env, Parallel :<: dom) =>
    AlphaEq Parallel Parallel dom env
  where
    alphaEqSym = alphaEqSymDefault



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

instance Semantic ForLoop
  where
    semantics ForLoop = Sem
        { semanticName = "forLoop"
        , semanticEval = \len init body -> foldl (flip body) init [0 .. len-1]
        }


instance ExprEq   ForLoop where exprEq = exprEqSem; exprHash = exprHashSem
instance Render   ForLoop where renderPart = renderPartSem
instance Eval     ForLoop where evaluate   = evaluateSem
instance ToTree   ForLoop
instance EvalBind ForLoop where evalBindSym = evalBindSymDefault

instance (AlphaEq dom dom dom env, ForLoop :<: dom) =>
    AlphaEq ForLoop ForLoop dom env
  where
    alphaEqSym = alphaEqSymDefault



--------------------------------------------------------------------------------
-- * Feldspar domain
--------------------------------------------------------------------------------

-- | The Feldspar domain
type FeldDomain
    =   Construct SimpleCtx
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
printFeld = printExpr . reifySmart (const True)

-- | Draw the syntax tree
drawFeld :: Syntactic a FeldDomainAll => a -> IO ()
drawFeld = drawAST . reifySmart (const True)

-- | Evaluation
eval :: Syntactic a FeldDomainAll => a -> Internal a
eval = evalBind . reifySmart (const True)



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
    Data a == Data b = alphaEq (reify a) (reify b)

instance Type a => Show (Data a)
  where
    show (Data a) = render $ reify a

instance (Type a, Num a) => Num (Data a)
  where
    fromInteger = value . fromInteger
    abs         = sugarSymCtx simpleCtx $ Construct "abs" abs
    signum      = sugarSymCtx simpleCtx $ Construct "signum" signum
    (+)         = sugarSymCtx simpleCtx $ Construct "(+)" (+)
    (-)         = sugarSymCtx simpleCtx $ Construct "(-)" (-)
    (*)         = sugarSymCtx simpleCtx $ Construct "(*)" (*)

(?) :: Syntax a => Data Bool -> (a,a) -> a
cond ? (t,e) = sugarSymCtx simpleCtx Condition cond t e

-- | Parallel array
parallel :: Type a => Data Length -> (Data Index -> Data a) -> Data [a]
parallel = sugarSym Parallel

forLoop :: Syntax st => Data Length -> st -> (Data Index -> st -> st) -> st
forLoop = sugarSym ForLoop

arrLength :: Type a => Data [a] -> Data Length
arrLength = sugarSymCtx simpleCtx $ Construct "arrLength" Prelude.length

-- | Array indexing
getIx :: Type a => Data [a] -> Data Index -> Data a
getIx = sugarSymCtx simpleCtx $ Construct "getIx" eval
  where
    eval as i
        | i >= len || i < 0 = error "getIx: index out of bounds"
        | otherwise         = as !! i
      where
        len = Prelude.length as

not :: Data Bool -> Data Bool
not = sugarSymCtx simpleCtx $ Construct "not" Prelude.not

(==) :: Type a => Data a -> Data a -> Data Bool
(==) = sugarSymCtx simpleCtx $ Construct "(==)" (Prelude.==)

max :: Type a => Data a -> Data a -> Data a
max = sugarSymCtx simpleCtx $ Construct "max" Prelude.max

min :: Type a => Data a -> Data a -> Data a
min = sugarSymCtx simpleCtx $ Construct "min" Prelude.min

