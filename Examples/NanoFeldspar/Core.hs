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
-- for primitive functions, since the 'Sym' feature is quite unsafe (uses only
-- a 'String' to distinguish between functions).

module NanoFeldspar.Core where



import Prelude hiding (max, min)
import qualified Prelude
import Data.Typeable

import Language.Syntactic
import Language.Syntactic.Features.Symbol
import Language.Syntactic.Features.Literal
import Language.Syntactic.Features.Condition
import Language.Syntactic.Features.Tuple
import Language.Syntactic.Features.Binding
import Language.Syntactic.Features.Binding.HigherOrder
import Language.Syntactic.Sharing.Graph
import Language.Syntactic.Sharing.ReifyHO



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

instance IsSymbol Parallel
  where
    toSym Parallel = Sym "parallel" parallel
      where
        parallel len ixf = map ixf [0 .. len-1]

instance ExprEq Parallel where exprEq = exprEqFunc; exprHash = exprHashFunc
instance Render Parallel where renderPart = renderPartFunc
instance Eval   Parallel where evaluate   = evaluateFunc
instance ToTree Parallel



--------------------------------------------------------------------------------
-- * For loops
--------------------------------------------------------------------------------

data ForLoop a
  where
    ForLoop :: ForLoop (Length :-> st :-> (Index -> st -> st) :-> Full st)

instance IsSymbol ForLoop
  where
    toSym ForLoop = Sym "forLoop" forLoop
      where
        forLoop len init body = foldl (flip body) init [0 .. len-1]

instance ExprEq ForLoop where exprEq = exprEqFunc; exprHash = exprHashFunc
instance Render ForLoop where renderPart = renderPartFunc
instance Eval   ForLoop where evaluate   = evaluateFunc
instance ToTree ForLoop



--------------------------------------------------------------------------------
-- * Feldspar domain
--------------------------------------------------------------------------------

-- | The Feldspar domain
type FeldDomain
    =   Literal Poly
    :+: Sym
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

-- | A predicate deciding which constructs can be shared. Variables and literals
-- are not shared.
canShare :: HOASTF Poly FeldDomain a -> Maybe (Witness' Poly a)
canShare (prjVariable poly -> Just _) = Nothing
canShare (prjLiteral poly  -> Just _) = Nothing
canShare _                            = Just Witness'

-- | Draw the syntax graph after common sub-expression elimination
drawFeldCSE :: Reifiable Poly a FeldDomain internal => a -> IO ()
drawFeldCSE a = do
    (g,_) <- reifyGraph canShare a
    drawASG
      $ reindexNodesFrom0
      $ inlineSingle
      $ cse
      $ g

-- | Draw the syntax graph after observing sharing
drawFeldObs :: Reifiable Poly a FeldDomain internal => a -> IO ()
drawFeldObs a = do
    (g,_) <- reifyGraph canShare a
    drawASG
      $ reindexNodesFrom0
      $ inlineSingle
      $ g

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
    Data a == Data b = alphaEq poly (reify a) (reify b)

instance Show (Data a)
  where
    show (Data a) = render $ reify a

instance (Type a, Num a) => Num (Data a)
  where
    fromInteger = value . fromInteger
    abs         = sugarN $ sym1 "abs" abs
    signum      = sugarN $ sym1 "signum" signum
    (+)         = sugarN $ sym2 "(+)" (+)
    (-)         = sugarN $ sym2 "(-)" (-)
    (*)         = sugarN $ sym2 "(*)" (*)

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
arrLength = sugarN $ sym1 "arrLength" Prelude.length

-- | Array indexing
getIx :: Type a => Data [a] -> Data Index -> Data a
getIx = sugarN $ sym2 "getIx" eval
  where
    eval as i
        | i >= len || i < 0 = error "getIx: index out of bounds"
        | otherwise         = as !! i
      where
        len = Prelude.length as

max :: Type a => Data a -> Data a -> Data a
max = sugarN $ sym2 "max" Prelude.max

min :: Type a => Data a -> Data a -> Data a
min = sugarN $ sym2 "min" Prelude.min

