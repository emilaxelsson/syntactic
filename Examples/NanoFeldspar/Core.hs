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
-- types at which constructors operate. Currently, all general features (such as
-- 'Literal' and 'Tuple') use a 'Poly' context, which means that the types are
-- not restricted. A real implementation would also probably use custom types
-- for primitive functions, since the 'PrimFunc' feature is quite unsafe (uses
-- only a 'String' to distinguish between functions).

module NanoFeldspar.Core where



import Prelude hiding (max, min)
import qualified Prelude
import Data.Typeable

import Language.Syntactic
import Language.Syntactic.Features.Literal
import Language.Syntactic.Features.PrimFunc
import Language.Syntactic.Features.Condition
import Language.Syntactic.Features.Tuple
import Language.Syntactic.Features.Binding
import Language.Syntactic.Features.Binding.HigherOrder



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
    Parallel :: Parallel (Length :-> (Index -> a) :-> Full [a])

instance Render Parallel
  where
    render Parallel = "parallel"

instance ToTree Parallel

instance ExprEq Parallel
  where
    Parallel `exprEq` Parallel = True

instance Eval Parallel
  where
    evaluate Parallel = fromEval $ \len ixf -> Prelude.map ixf [0 .. len-1]



--------------------------------------------------------------------------------
-- * For loops
--------------------------------------------------------------------------------

data ForLoop a
  where
    ForLoop :: ForLoop (Length :-> st :-> (Index -> st -> st) :-> Full st)

instance ExprEq ForLoop
  where
    ForLoop `exprEq` ForLoop = True

instance Render ForLoop
  where
    render ForLoop = "forLoop"

instance ToTree ForLoop

instance Eval ForLoop
  where
    evaluate ForLoop = fromEval $ \len init body -> foldr body init [0 .. len-1]



--------------------------------------------------------------------------------
-- * Feldspar domain
--------------------------------------------------------------------------------

-- | The Feldspar domain
type FeldDomain
    =   Literal Poly
    :+: PrimFunc
    :+: Condition Poly
    :+: Tuple Poly
    :+: Select Poly
    :+: Let Poly Poly
    :+: Parallel
    :+: ForLoop

data Data a = Type a => Data { unData :: HOAST Poly FeldDomain (Full a) }

type FeldDomainAll = HOLambda Poly FeldDomain :+: Variable Poly :+: FeldDomain

-- | Declaring 'Data' as syntactic sugar
instance Type a => Syntactic (Data a) FeldDomainAll
  where
    type Internal (Data a) = a
    desugar = unData
    sugar   = Data

-- | Specialization of the 'Syntactic' class for the Feldspar domain
class
    ( Syntactic a FeldDomainAll
    , Type (Internal a)
    , SyntacticN a (ASTF FeldDomainAll (Internal a))
    ) =>
      Syntax a

instance
    ( Syntactic a FeldDomainAll
    , Type (Internal a)
    , SyntacticN a (ASTF FeldDomainAll (Internal a))
    ) =>
      Syntax a



--------------------------------------------------------------------------------
-- * Back ends
--------------------------------------------------------------------------------

-- | Print the expression
printFeld :: Reifiable Poly a FeldDomain internal => a -> IO ()
printFeld = printExpr . reify

-- | Draw the syntax tree
drawFeld :: Reifiable Poly a FeldDomain internal => a -> IO ()
drawFeld = drawAST . reify

-- | Evaluation
eval :: Reifiable Poly a FeldDomain internal => a -> NAryEval internal
eval = evalLambda . reify



--------------------------------------------------------------------------------
-- * Core library
--------------------------------------------------------------------------------

-- | Literal
value :: Syntax a => Internal a -> a
value = sugar . lit

-- | For types containing some kind of \"thunk\", this function can be used to
-- force computation
force :: Syntax a => a -> a
force = resugar

-- | Share a value using let binding
share :: (Syntax a, Syntax b) => a -> (a -> b) -> b
share a f = sugar $ letBind (desugar a) (desugarN f)

-- | Alpha equivalence
instance Eq (Data a)
  where
    Data a == Data b = reify a `alphaEq` reify b

instance Show (Data a)
  where
    show (Data a) = render $ reify a

instance (Type a, Num a) => Num (Data a)
  where
    fromInteger = value . fromInteger
    abs         = sugarN $ primFunc1 "abs" abs
    signum      = sugarN $ primFunc1 "signum" signum
    (+)         = sugarN $ primFunc2 "(+)" (+)
    (-)         = sugarN $ primFunc2 "(-)" (-)
    (*)         = sugarN $ primFunc2 "(*)" (*)

-- | Parallel array
parallel :: Type a => Data Length -> (Data Index -> Data a) -> Data [a]
parallel len ixf
    =   sugar
    $   inject Parallel
    :$: desugar len
    :$: lambda (desugarN ixf)

forLoop :: Syntax st => Data Length -> st -> (Data Index -> st -> st) -> st
forLoop len init body
    =   sugar
    $   inject ForLoop
    :$: desugar len
    :$: desugar init
    :$: lambdaN (desugarN body)

arrLength :: Type a => Data [a] -> Data Length
arrLength = sugarN $ primFunc1 "arrLength" Prelude.length

-- | Array indexing
getIx :: Type a => Data [a] -> Data Index -> Data a
getIx = sugarN $ primFunc2 "getIx" eval
  where
    eval as i
        | i >= len || i < 0 = error "getIx: index out of bounds"
        | otherwise         = as !! i
      where
        len = Prelude.length as

max :: Type a => Data a -> Data a -> Data a
max = sugarN $ primFunc2 "max" Prelude.max

min :: Type a => Data a -> Data a -> Data a
min = sugarN $ primFunc2 "min" Prelude.min

