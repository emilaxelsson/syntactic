{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module MuFeldspar.Core where



import Prelude hiding (max, min)
import qualified Prelude

import Data.Typeable

import Language.Syntactic.Features.Binding
import Language.Syntactic.Features.Binding.HigherOrder



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
    evaluate Parallel = consEval $ \len ixf -> Prelude.map ixf [0 .. len-1]



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
    evaluate ForLoop = consEval $ \len init body -> foldr body init [0 .. len-1]



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

type Data a = HOAST FeldDomain (Full a)

-- | Specialization of the 'Syntactic' class for the Feldspar domain
class
    ( Syntactic a (HOLambda FeldDomain :+: Variable :+: FeldDomain)
    , Type (Internal a)
    ) =>
      Syntax a

instance
    ( Syntactic a (HOLambda FeldDomain :+: Variable :+: FeldDomain)
    , Type (Internal a)
    ) =>
      Syntax a



--------------------------------------------------------------------------------
-- * Core library
--------------------------------------------------------------------------------

reifyFeld :: Syntax a =>
    a -> AST (Lambda :+: Variable :+: FeldDomain) (Full (Internal a))
reifyFeld = reify . desugar

eval :: Syntax a => a -> Internal a
eval = evalLambda . reifyFeld

-- | For types containing some kind of \"thunk\", this function can be used to
-- force computation
force :: Syntax a => a -> a
force = resugar

-- TODO Hacks to make the 'Num' instance work:
instance ExprEq (HOLambda a) where exprEq = undefined
instance Render (HOLambda a) where render = undefined
instance ExprEq Variable     where exprEq = undefined

instance (Type a, Num a) => Num (Data a)
  where
    fromInteger = lit . fromInteger
    abs         = primFunc "abs" abs
    signum      = primFunc "signum" signum
    (+)         = primFunc2 "(+)" (+)
    (-)         = primFunc2 "(-)" (-)
    (*)         = primFunc2 "(*)" (*)

parallel :: Type a => Data Length -> (Data Index -> Data a) -> Data [a]
parallel len ixf = inject Parallel :$: len :$: lambda ixf

forLoopCore :: Type st =>
     Data Length -> Data st -> (Data Index -> Data st -> Data st) -> Data st
forLoopCore len init body = inject ForLoop :$: len :$: init :$: lambdaN body

forLoop :: Syntax st => Data Length -> st -> (Data Index -> st -> st) -> st
forLoop len init body = sugar $ forLoopCore len (desugar init) body'
  where
    body' i = desugar . body i . sugar

arrLength :: Type a => Data [a] -> Data Length
arrLength = primFunc "arrLength" Prelude.length

getIx :: Type a => Data [a] -> Data Index -> Data a
getIx arr ix = primFunc2 "getIx" eval arr ix
  where
    eval as i
        | i >= len || i < 0 = error "getIx: index out of bounds"
        | otherwise         = as !! i
      where
        len = Prelude.length as

max :: (Type a, Ord a) => Data a -> Data a -> Data a
max = primFunc2 "max" Prelude.max

min :: (Type a, Ord a) => Data a -> Data a -> Data a
min = primFunc2 "min" Prelude.min

