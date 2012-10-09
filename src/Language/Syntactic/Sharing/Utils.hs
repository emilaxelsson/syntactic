-- | Some utility functions used by the other modules

module Language.Syntactic.Sharing.Utils where



import Data.Array
import Data.List



--------------------------------------------------------------------------------
-- * Difference lists
--------------------------------------------------------------------------------

-- | Difference list
type DList a = [a] -> [a]

-- | Empty list
empty :: DList a
empty = id

-- | Singleton list
single :: a -> DList a
single = (:)

fromDList :: DList a -> [a]
fromDList = ($ [])



--------------------------------------------------------------------------------
-- * Misc.
--------------------------------------------------------------------------------

-- | Given a list @is@ of unique natural numbers, returns a function that maps
-- each number in @is@ to a unique number in the range @[0 .. length is-1]@. The
-- complexity is O(@maximum is@).
reindex :: (Integral a, Ix a) => [a] -> a -> a
reindex is = (tab!)
  where
    tab = array (0, maximum is) $ zip is [0..]

-- | Count the number of occurrences of each element in the list. The result is
-- an array mapping each element to its number of occurrences.
count :: Ix a
    => (a,a)  -- ^ Upper and lower bound on the elements to be counted
    -> [a]    -- ^ Elements to be counted
    -> Array a Int
count bnds as = accumArray (+) 0 bnds [(n,1) | n <- as]

-- | Partitions the list such that two elements are in the same sub-list if and
-- only if they satisfy the equivalence check. The complexity is O(n^2).
fullPartition :: (a -> a -> Bool) -> [a] -> [[a]]
fullPartition eq []     = []
fullPartition eq (a:as) = (a:as1) : fullPartition eq as2
  where
    (as1,as2) = partition (eq a) as

