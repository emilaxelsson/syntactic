{-# LANGUAGE TemplateHaskell #-}

-- | Conversion between tuples and nested pairs

module Data.NestTuple where



import Data.NestTuple.TH



-- | Tuples that can be converted to/from nested pairs
class Nestable tup
  where
    -- | Representation as nested pairs
    type Nested tup
    -- | Convert to nested pairs
    nest :: tup -> Nested tup
    -- | Convert from nested pairs
    unnest :: Nested tup -> tup

mkNestableInstances 15

