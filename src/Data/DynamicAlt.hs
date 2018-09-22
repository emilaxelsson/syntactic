-- | An alternative to "Data.Dynamic" with a different constraint on 'toDyn'

module Data.DynamicAlt where



import Data.Dynamic ()
import Data.Typeable
import GHC.Exts
import Unsafe.Coerce

import Data.PolyProxy



data Dynamic = Dynamic TypeRep Any

toDyn :: forall a b . Typeable (a -> b) => P (a -> b) -> a -> Dynamic
toDyn _ a = case splitTyConApp $ typeOf (undefined :: a -> b) of
    (_,[ta,_]) -> Dynamic ta (unsafeCoerce a)

fromDyn :: Typeable a => Dynamic -> Maybe a
fromDyn (Dynamic t a)
    | b <- unsafeCoerce a
    , t == typeOf b
    = Just b
fromDyn _ = Nothing

