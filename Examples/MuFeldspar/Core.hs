{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module MuFeldspar.Core where



import Prelude hiding (max, min)
import qualified Prelude
import Data.Typeable

import Language.Syntactic
import Language.Syntactic.Features.Literal
import Language.Syntactic.Features.PrimFunc
import Language.Syntactic.Features.Condition
import Language.Syntactic.Features.Tuple
import Language.Syntactic.Features.TupleSyntactic
import Language.Syntactic.Features.Binding
import Language.Syntactic.Features.Binding.HigherOrder



--------------------------------------------------------------------------------
-- * Types
--------------------------------------------------------------------------------

-- | Convenient class alias
class    (Eq a, Show a, Typeable a) => Type a
instance (Eq a, Show a, Typeable a) => Type a

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

type FeldDomain
    =   Literal
    :+: PrimFunc
    :+: Condition
    :+: Tuple
    :+: Select
    :+: Let
    :+: Parallel
    :+: ForLoop

data Data a = Type a => Data { unData :: HOAST FeldDomain (Full a) }

instance Type a =>
    Syntactic (Data a) (HOLambda FeldDomain :+: Variable :+: FeldDomain)
  where
    type Internal (Data a) = a
    desugar = unData
    sugar   = Data

-- | Specialization of the 'Syntactic' class for the Feldspar domain
class
    ( Syntactic a (HOLambda FeldDomain :+: Variable :+: FeldDomain)
    , Type (Internal a)
    , SyntacticN a
        (ASTF (HOLambda FeldDomain :+: Variable :+: FeldDomain) (Internal a))
    ) =>
      Syntax a

instance
    ( Syntactic a (HOLambda FeldDomain :+: Variable :+: FeldDomain)
    , Type (Internal a)
    , SyntacticN a
        (ASTF (HOLambda FeldDomain :+: Variable :+: FeldDomain) (Internal a))
    ) =>
      Syntax a



--------------------------------------------------------------------------------
-- * Back ends
--------------------------------------------------------------------------------

printFeld :: Reifiable a FeldDomain internal => a -> IO ()
printFeld = printExpr . reify

drawFeld :: Reifiable a FeldDomain internal => a -> IO ()
drawFeld = drawAST . reify

eval :: Reifiable a FeldDomain internal => a -> NAryEval internal
eval = evalLambda . reify



--------------------------------------------------------------------------------
-- * Core library
--------------------------------------------------------------------------------

value :: Syntax a => Internal a -> a
value = sugar . lit

-- | For types containing some kind of \"thunk\", this function can be used to
-- force computation
force :: Syntax a => a -> a
force = resugar

leT :: (Syntax a, Syntax b) => a -> (a -> b) -> b
leT a f = sugar $ let_ (desugar a) (desugarN f)

instance Eq (Data a)
  where
    Data a == Data b = reifyHOAST a `eqLambda` reifyHOAST b

instance Show (Data a)
  where
    show (Data a) = render $ reifyHOAST a

instance (Type a, Num a) => Num (Data a)
  where
    fromInteger = value . fromInteger
    abs         = sugarN $ primFunc1 "abs" abs
    signum      = sugarN $ primFunc1 "signum" signum
    (+)         = sugarN $ primFunc2 "(+)" (+)
    (-)         = sugarN $ primFunc2 "(-)" (-)
    (*)         = sugarN $ primFunc2 "(*)" (*)

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

getIx :: Type a => Data [a] -> Data Index -> Data a
getIx = sugarN $ primFunc2 "getIx" eval
  where
    eval as i
        | i >= len || i < 0 = error "getIx: index out of bounds"
        | otherwise         = as !! i
      where
        len = Prelude.length as

max :: (Type a, Ord a) => Data a -> Data a -> Data a
max = sugarN $ primFunc2 "max" Prelude.max

min :: (Type a, Ord a) => Data a -> Data a -> Data a
min = sugarN $ primFunc2 "min" Prelude.min

