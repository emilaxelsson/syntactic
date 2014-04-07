-- | Type universes and dynamic types
--
-- This module uses Data Types à la Carte to provide open universes. A simpler closed implementation
-- is found in @extras/TypeUniverseClosed.hs@.
--
-- Example 1 (dynamic types):
--
-- > type MyUniverse = IntType :+: BoolType
-- >
-- > hlist :: [Dynamic MyUniverse]
-- > hlist = [toDyn True, toDyn (1 :: Int)]
--
-- > *Main> hlist
-- > [True,1]
--
-- Note that if we were using "Data.Dynamic", it would just print
--
-- > [<<Bool>>,<<Int>>]
--
-- Example 2 (dynamically typed addition):
--
-- > addDyn :: (TypeEq ts ts, PWitness Num ts ts) => Dynamic ts -> Dynamic ts -> Maybe (Dynamic ts)
-- > addDyn (Dyn ta a) (Dyn tb b) = do
-- >     Dict <- typeEq ta tb
-- >     Dict <- pwit pNum ta
-- >     return (Dyn ta (a+b))
--
-- "Data.Dynamic" could only do this monomorphically, for one 'Num' type at a time.

module Data.Syntactic.TypeUniverse
    ( module Data.Constraint
    , module Data.Syntactic.TypeUniverse.TypeUniverse
    , module Data.Syntactic.TypeUniverse.Sub
    ) where



import Data.Constraint (Dict (..))

import Data.Syntactic.TypeUniverse.TypeUniverse
import Data.Syntactic.TypeUniverse.Sub

