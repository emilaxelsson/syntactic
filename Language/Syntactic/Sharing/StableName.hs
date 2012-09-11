module Language.Syntactic.Sharing.StableName where



import Control.Monad.IO.Class
import Data.IntMap as Map
import Data.IORef
import System.Mem.StableName
import Unsafe.Coerce

import Language.Syntactic
import Language.Syntactic.Sharing.Graph



-- | 'StableName' of a @(c (Full a))@ with hidden result type
data StName c
  where
    StName :: StableName (c (Full a)) -> StName c

instance Eq (StName c)
  where
    StName a == StName b = a == unsafeCoerce b
      -- This is "probably" safe according to
      -- <http://www.haskell.org/pipermail/glasgow-haskell-users/2012-August/022758.html>

      -- TODO In future, use `eqStableName`. It should be in GHC 7.8.1.

hash :: StName c -> Int
hash (StName st) = hashStableName st

-- | A hash table from 'StName' to 'NodeId' (with 'hash' as the hashing
-- function). I.e. it is assumed that the 'StName's at each entry all have the
-- same hash, and that this number is equal to the entry's key.
type History c = IntMap [(StName c, NodeId)]

-- | Lookup a name in the history
lookHistory :: History c -> StName c -> Maybe NodeId
lookHistory hist st = case Map.lookup (hash st) hist of
    Nothing   -> Nothing
    Just list -> Prelude.lookup st list

-- | Insert the name into the history
remember :: StName c -> NodeId -> History c -> History c
remember st n hist = insertWith (++) (hash st) [(st,n)] hist

-- | Return a fresh identifier from the given supply
fresh :: (Enum a, MonadIO m) => IORef a -> m a
fresh aRef = do
    a <- liftIO $ readIORef aRef
    liftIO $ writeIORef aRef (succ a)
    return a

