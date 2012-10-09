{-# LANGUAGE PolyKinds #-}

-- TODO PolyKinds can be enabled globally in GHC 7.6. In 7.4, additional annotations are needed.

module Data.PolyProxy where



-- | Kind-polymorphic proxy type
data P a where P :: P a
  -- Using one letter to remove line noise

