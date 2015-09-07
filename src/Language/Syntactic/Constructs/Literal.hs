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
    {-# SPECIALIZE instance Constrained Literal #-}
    {-# INLINABLE exprDict #-}
    type Sat Literal = Eq :/\: Show :/\: Typeable :/\: Top
    exprDict (Literal _) = Dict

instance Equality Literal
  where
    {-# SPECIALIZE instance Equality Literal #-}
    {-# INLINABLE equal #-}
    {-# INLINABLE exprHash #-}
    Literal a `equal` Literal b = case cast a of
        Just a' -> a'==b
        Nothing -> False

    exprHash (Literal a) = hash (show a)

instance Render Literal
  where
    {-# SPECIALIZE instance Render Literal #-}
    {-# INLINABLE renderSym #-}
    renderSym (Literal a) = show a

instance StringTree Literal where
  {-# SPECIALIZE instance StringTree Literal #-}

instance Eval Literal
  where
    {-# SPECIALIZE instance Eval Literal #-}
    {-# INLINABLE evaluate #-}
    evaluate (Literal a) = a
