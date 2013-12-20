{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- | This module is only to limit the scope of the @OverlappingInstances@ flag

module Data.Syntactic.TypeUniverse.Sub where



import Data.Syntactic
import Data.Syntactic.TypeUniverse.TypeUniverse



-- | Sub-universe relation
--
-- In general, a universe @ts@ is a sub-universe of $ts'$ if @ts'@ has the form
--
-- > t1 :+: t2 :+: ... :+: ts
class SubUniverse tsSub tsSup
  where
    -- | Cast a type representation to a larger universe
    weakenUniverse :: TypeRep tsSub a -> TypeRep tsSup a

instance SubUniverse ts ts
  where
    weakenUniverse = id

instance (SubUniverse tsSub tsSup', tsSup ~ (t :+: tsSup')) => SubUniverse tsSub tsSup
  where
    weakenUniverse = sugar . mapAST InjR . desugar . weakenUniverse

