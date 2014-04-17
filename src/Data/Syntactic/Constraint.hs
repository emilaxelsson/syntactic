{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- TODO Only `InjectC` should be used overlapped. Move to separate module?

-- | Type-constrained syntax trees

module Data.Syntactic.Constraint where



import Data.Typeable

import Data.Constraint
import Data.Proxy

import Data.Syntactic.Syntax
import Data.Syntactic.Interpretation



--------------------------------------------------------------------------------
-- * Misc.
--------------------------------------------------------------------------------

