-- | Literal expressions

module Language.Syntactic.Constructs.Literal where



import Data.Typeable

import Data.Hash

import Language.Syntactic



data Literal sig
  where
    Literal :: (Eq a, Show a, Typeable a) => a -> Literal (Full a)

instance Constrained Literal
  where
    type Sat Literal = Eq :/\: Show :/\: Typeable :/\: Top
    exprDict (Literal _) = Dict

instance Equality Literal
  where
    Literal a `equal` Literal b = case cast a of
        Just a' -> a'==b
        Nothing -> False

    exprHash (Literal a) = hash (show a)

instance Render Literal
  where
    renderSym (Literal a) = show a

instance StringTree Literal

instance Eval Literal
  where
    evaluate (Literal a) = a

