{-# LANGUAGE PolyKinds #-}

module Data.PolyProxy where



-- | Kind-polymorphic proxy type
data P a where P :: P a
  -- Using one letter to remove line noise

