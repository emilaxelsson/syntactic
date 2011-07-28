module Language.Syntactic.Sharing.StableName where



import Control.Monad.IO.Class
import Data.IntMap as Map
import Data.IORef
import Data.Typeable
import System.Mem.StableName
import Unsafe.Coerce

import Language.Syntactic
import Language.Syntactic.Sharing.Graph



-- | 'StableName' of a (@c (`Full` a)@) with hidden result type
data StName c
  where
    StName :: Typeable a => StableName (c (Full a)) -> StName c

stCast :: forall a b c . (Typeable a, Typeable b) =>
    StableName (c (Full a)) -> Maybe (StableName (c (Full b)))
stCast a
    | ta==tb    = Just (unsafeCoerce a)
    | otherwise = Nothing
  where
    ta = typeOf (undefined :: a)
    tb = typeOf (undefined :: b)

instance Eq (StName c)
  where
    StName st1 == StName st2 = case stCast st1 of
        Just st1' -> st1'==st2
        _         -> False

hash :: StName c -> Int
hash (StName st) = hashStableName st



-- 'History' implements a hash table from 'StName' to 'NodeId' (with 'hash' as
-- the hashing function). I.e. it is assumed that the 'StName's at each entry
-- all have the same 'hash', and that this number is equal to the entry's key.
type History c = IntMap [(StName c, NodeId)]

lookHistory :: History c -> StName c -> Maybe NodeId
lookHistory hist st = case Map.lookup (hash st) hist of
    Nothing   -> Nothing
    Just list -> Prelude.lookup st list

remember :: StName c -> NodeId -> History c -> History c
remember st n hist = insertWith (++) (hash st) [(st,n)] hist

-- | Return a fresh identifier from the given supply
fresh :: (Enum a, MonadIO m) => IORef a -> m a
fresh aRef = do
    a <- liftIO $ readIORef aRef
    liftIO $ writeIORef aRef (succ a)
    return a

