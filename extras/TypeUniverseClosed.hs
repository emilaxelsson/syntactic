-- | Typed type reification, type-level reasoning and dynamic types
--
-- This module is meant as a reference for understanding the "Data.Syntactic.TypeUniverse" module.

module TypeUniverseClosed where



import Data.Constraint



-- | Typed representation of types (reification of type @a@)
data TypeRep a
  where
    BoolType  :: TypeRep Bool
    IntType   :: TypeRep Int
    FloatType :: TypeRep Float
    ListType  :: TypeRep a -> TypeRep [a]

-- | Type reification
class Typeable a
  where
    -- | Reifies type @a@
    typeRep :: TypeRep a

instance Typeable Bool              where typeRep = BoolType
instance Typeable Int               where typeRep = IntType
instance Typeable Float             where typeRep = FloatType
instance Typeable a => Typeable [a] where typeRep = ListType typeRep

typeEq :: TypeRep a -> TypeRep b -> Maybe (Dict (a ~ b))
typeEq BoolType      BoolType      = Just Dict
typeEq IntType       IntType       = Just Dict
typeEq FloatType     FloatType     = Just Dict
typeEq (ListType t1) (ListType t2) = do Dict <- typeEq t1 t2; return Dict
typeEq _ _ = Nothing

hasTypeable :: TypeRep a -> Dict (Typeable a)
hasTypeable BoolType  = Dict
hasTypeable IntType   = Dict
hasTypeable FloatType = Dict
hasTypeable (ListType t) | Dict <- hasTypeable t = Dict

hasEq :: TypeRep a -> Dict (Eq a)
hasEq BoolType  = Dict
hasEq IntType   = Dict
hasEq FloatType = Dict
hasEq (ListType t) | Dict <- hasEq t = Dict

hasShow :: TypeRep a -> Dict (Show a)
hasShow BoolType  = Dict
hasShow IntType   = Dict
hasShow FloatType = Dict
hasShow (ListType t) | Dict <- hasShow t = Dict

hasNum :: TypeRep a -> Maybe (Dict (Num a))
hasNum BoolType     = Nothing
hasNum IntType      = Just Dict
hasNum FloatType    = Just Dict
hasNum (ListType t) = Nothing

-- | Safe cast (does not use @unsafeCoerce@ underneath)
cast :: forall a b . (Typeable a, Typeable b) => a -> Maybe b
cast a = do
    Dict <- typeEq (typeRep :: TypeRep a) (typeRep :: TypeRep b)
    return a

typeOf :: Typeable a => a -> TypeRep a
typeOf _ = typeRep

data Dynamic
  where
    Dyn :: TypeRep a -> a -> Dynamic

toDyn :: Typeable a => a -> Dynamic
toDyn = Dyn typeRep

fromDyn :: Typeable a => Dynamic -> Maybe a
fromDyn (Dyn t a) | Dict <- hasTypeable t = cast a

instance Eq Dynamic
  where
    Dyn ta a == Dyn tb b
        | Just Dict <- typeEq ta tb
        , Dict      <- hasEq ta
        = a == b
    _ == _ = False

instance Show Dynamic
  where
    show (Dyn t a) | Dict <- hasShow t = show a

