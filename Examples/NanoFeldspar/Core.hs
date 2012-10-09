{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
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
import Language.Syntactic.Constructs.Binding
import Language.Syntactic.Constructs.Binding.HigherOrder
import Language.Syntactic.Constructs.Condition
import Language.Syntactic.Constructs.Construct
import Language.Syntactic.Constructs.Literal
import Language.Syntactic.Constructs.Tuple
import Language.Syntactic.Frontend.Tuple
import Language.Syntactic.Sharing.SimpleCodeMotion



--------------------------------------------------------------------------------
-- * Types
--------------------------------------------------------------------------------

-- | Convenient class alias
class    (Ord a, Show a, Typeable a) => Type a
instance (Ord a, Show a, Typeable a) => Type a
  -- TODO Use type synonym instead?

type Length = Int
type Index  = Int



--------------------------------------------------------------------------------
-- * Parallel arrays
--------------------------------------------------------------------------------

data Parallel a
  where
    Parallel :: Type a => Parallel (Length :-> (Index -> a) :-> Full [a])

instance Constrained Parallel
  where
    type Sat Parallel = Type
    exprDict Parallel = Dict

instance Semantic Parallel
  where
    semantics Parallel = Sem
        { semanticName = "parallel"
        , semanticEval = \len ixf -> map ixf [0 .. len-1]
        }

instance Equality Parallel where equal = equalDefault; exprHash = exprHashDefault
instance Render   Parallel where renderArgs = renderArgsDefault
instance Eval     Parallel where evaluate   = evaluateDefault
instance ToTree   Parallel
instance EvalBind Parallel where evalBindSym = evalBindSymDefault

instance AlphaEq dom dom dom env => AlphaEq Parallel Parallel dom env
  where
    alphaEqSym = alphaEqSymDefault



--------------------------------------------------------------------------------
-- * For loops
--------------------------------------------------------------------------------

data ForLoop a
  where
    ForLoop :: Type st =>
        ForLoop (Length :-> st :-> (Index -> st -> st) :-> Full st)

instance Constrained ForLoop
  where
    type Sat ForLoop = Type
    exprDict ForLoop = Dict

instance Semantic ForLoop
  where
    semantics ForLoop = Sem
        { semanticName = "forLoop"
        , semanticEval = \len init body -> foldl (flip body) init [0 .. len-1]
        }


instance Equality ForLoop where equal = equalDefault; exprHash = exprHashDefault
instance Render   ForLoop where renderArgs = renderArgsDefault
instance Eval     ForLoop where evaluate   = evaluateDefault
instance ToTree   ForLoop
instance EvalBind ForLoop where evalBindSym = evalBindSymDefault

instance AlphaEq dom dom dom env => AlphaEq ForLoop ForLoop dom env
  where
    alphaEqSym = alphaEqSymDefault



--------------------------------------------------------------------------------
-- * Feldspar domain
--------------------------------------------------------------------------------

-- | The Feldspar domain
type FeldDomain
    =   Construct
    :+: Literal
    :+: Condition
    :+: Tuple
    :+: Select
    :+: Parallel
    :+: ForLoop

type FeldSyms      = Let :+: (FeldDomain :|| Eq :| Show)
type FeldDomainAll = HODomain FeldSyms Typeable Top

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

-- | A predicate deciding which constructs can be shared. Variables, lambdas and literals are not
-- shared.
canShare :: ASTF (FODomain FeldSyms Typeable Top) a -> Maybe (Dict (Top a))
canShare (prjP (P::P (Variable :|| Top)) -> Just _) = Nothing
canShare (prjP (P::P (CLambda Top))      -> Just _) = Nothing
canShare (prj -> Just (Literal _)) = Nothing
canShare _  = Just Dict

canShareDict :: MkInjDict (FODomain FeldSyms Typeable Top)
canShareDict = mkInjDictFO canShare



--------------------------------------------------------------------------------
-- * Back ends
--------------------------------------------------------------------------------

-- | Print the expression
printFeld :: Syntactic a FeldDomainAll => a -> IO ()
printFeld = printExpr . reifySmart canShareDict
  -- TODO Should not share literals and variables? (See `canShare` in NanoFeldspar.Extra.)

-- | Draw the syntax tree
drawFeld :: Syntactic a FeldDomainAll => a -> IO ()
drawFeld = drawAST . reifySmart canShareDict

-- | Evaluation
eval :: Syntactic a FeldDomainAll => a -> Internal a
eval = evalBind . reifySmart canShareDict



--------------------------------------------------------------------------------
-- * Core library
--------------------------------------------------------------------------------

-- | Literal
value :: Syntax a => Internal a -> a
value = sugarSymC . Literal

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
share = sugarSymC Let

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
    abs         = sugarSymC $ Construct "abs" abs
    signum      = sugarSymC $ Construct "signum" signum
    (+)         = sugarSymC $ Construct "(+)" (+)
    (-)         = sugarSymC $ Construct "(-)" (-)
    (*)         = sugarSymC $ Construct "(*)" (*)

(?) :: Syntax a => Data Bool -> (a,a) -> a
cond ? (t,e) = sugarSymC Condition cond t e

-- | Parallel array
parallel :: Type a => Data Length -> (Data Index -> Data a) -> Data [a]
parallel = sugarSymC Parallel

forLoop :: Syntax st => Data Length -> st -> (Data Index -> st -> st) -> st
forLoop = sugarSymC ForLoop

arrLength :: Type a => Data [a] -> Data Length
arrLength = sugarSymC $ Construct "arrLength" Prelude.length

-- | Array indexing
getIx :: Type a => Data [a] -> Data Index -> Data a
getIx = sugarSymC $ Construct "getIx" eval
  where
    eval as i
        | i >= len || i < 0 = error "getIx: index out of bounds"
        | otherwise         = as !! i
      where
        len = Prelude.length as

not :: Data Bool -> Data Bool
not = sugarSymC $ Construct "not" Prelude.not

(==) :: Type a => Data a -> Data a -> Data Bool
(==) = sugarSymC $ Construct "(==)" (Prelude.==)

max :: Type a => Data a -> Data a -> Data a
max = sugarSymC $ Construct "max" Prelude.max

min :: Type a => Data a -> Data a -> Data a
min = sugarSymC $ Construct "min" Prelude.min

