{-# LANGUAGE UndecidableInstances #-}

module Data.Syntactic.TypeUniverse.TypeUniverse where



import Data.Constraint
import Data.Proxy

import Data.Syntactic.Syntax
import Data.Syntactic.Traversal
import Data.Syntactic.Sugar
import Data.Syntactic.Interpretation.Render



-- | 'Full'-indexed type representation
type TR = AST

-- | This class provides reification of type @a@ in a type universe @ts@. It can also be seen as a
-- statement that the type @a@ is in the set @ts@.
class Typeable ts a
  where
    typeRep' :: TR ts (Full a)

-- | Reified type @a@ in a type universe @ts@
--
-- This type can also be seen as a witness that @a@ is in the set @ts@ (i.e. @`Typeable` ts a@); see
-- 'witTypeable'.
newtype TypeRep ts a = TypeRep { unTypeRep :: TR ts (Full a) }
  -- The newtype is mainly because 'TR' cannot be partially applied

instance Render ts => Show (TypeRep ts a)
  where
    show = render . desugar

instance Syntactic (TypeRep ts a)
  where
    type Domain (TypeRep ts a)   = ts
    type Internal (TypeRep ts a) = a
    desugar = unTypeRep
    sugar   = TypeRep

-- | Reification of type @a@ in a type universe @ts@
typeRep :: Typeable ts a => TypeRep ts a
typeRep = TypeRep typeRep'

-- | Equality on type representations
class TypeEq t ts
  where
    typeEqSym
        :: (t sig1, Args (AST ts) sig1)
        -> (t sig2, Args (AST ts) sig2)
        -> Maybe (Dict (DenResult sig1 ~ DenResult sig2))

instance (TypeEq t1 ts, TypeEq t2 ts) => TypeEq (t1 :+: t2) ts
  where
    typeEqSym (InjL t1, as1) (InjL t2, as2) = typeEqSym (t1,as1) (t2,as2)
    typeEqSym (InjR t1, as1) (InjR t2, as2) = typeEqSym (t1,as1) (t2,as2)
    typeEqSym _ _ = Nothing

instance TypeEq ts ts => TypeEq (AST ts) ts
  where
    typeEqSym (Sym t1, as1)   (Sym t2, as2)   = typeEqSym (t1,as1) (t2,as2)
    typeEqSym (s1 :$ a1, as1) (s2 :$ a2, as2) = typeEqSym (s1, a1 :* as1) (s2, a2 :* as2)

-- | Equality on type representations
typeEq :: forall ts a b . TypeEq ts ts => TypeRep ts a -> TypeRep ts b -> Maybe (Dict (a ~ b))
typeEq (TypeRep s1) (TypeRep s2) = typeEqSym (s1, Nil :: Args (AST ts) (Full a)) (s2, Nil)

-- | Witness a type constraint for a reified type
class Witness p t ts
  where
    witSym :: t sig -> Args (AST ts) sig -> Dict (p (DenResult sig))

instance (Witness p t1 ts, Witness p t2 ts) => Witness p (t1 :+: t2) ts
  where
    witSym (InjL s) as = witSym s as
    witSym (InjR s) as = witSym s as

instance Witness p ts ts => Witness p (AST ts) ts
  where
    witSym (Sym s)  as = witSym s as
    witSym (s :$ a) as = witSym s (a :* as)

-- | Partially witness a type constraint for a reified type
class PWitness p t ts
  where
    pwitSym :: t sig -> Args (AST ts) sig -> Maybe (Dict (p (DenResult sig)))
    pwitSym _ _ = Nothing

instance (PWitness p t1 ts, PWitness p t2 ts) => PWitness p (t1 :+: t2) ts
  where
    pwitSym (InjL s) as = pwitSym s as
    pwitSym (InjR s) as = pwitSym s as

instance PWitness p ts ts => PWitness p (AST ts) ts
  where
    pwitSym (Sym s)  as = pwitSym s as
    pwitSym (s :$ a) as = pwitSym s (a :* as)

-- | Default implementation of 'pwitSym' for types that have a 'Witness' instance
pwitSymDefault :: Witness p t ts => t sig -> Args (AST ts) sig -> Maybe (Dict (p (DenResult sig)))
pwitSymDefault t = Just . witSym t

-- | Witness a type constraint for a reified type
wit :: forall p ts a . Witness p ts ts => Proxy p -> TypeRep ts a -> Dict (p a)
wit _ (TypeRep a) = witSym a (Nil :: Args (AST ts) (Full a))

-- | Partially witness a type constraint for a reified type
pwit :: forall p ts a . PWitness p ts ts => Proxy p -> TypeRep ts a -> Maybe (Dict (p a))
pwit _ (TypeRep a) = pwitSym a (Nil :: Args (AST ts) (Full a))



----------------------------------------------------------------------------------------------------
-- * Dynamic types
----------------------------------------------------------------------------------------------------

-- | Safe cast (does not use @unsafeCoerce@)
cast :: forall ts a b . (Typeable ts a, Typeable ts b, TypeEq ts ts) => Proxy ts -> a -> Maybe b
cast _ a = do
    Dict <- typeEq (typeRep :: TypeRep ts a) (typeRep :: TypeRep ts b)
    return a

-- | Safe generalized cast (does not use @unsafeCoerce@ underneath)
gcast :: forall ts a b c . (Typeable ts a, Typeable ts b, TypeEq ts ts) =>
    Proxy ts -> c a -> Maybe (c b)
gcast _ a = do
    Dict <- typeEq (typeRep :: TypeRep ts a) (typeRep :: TypeRep ts b)
    return a

-- | Dynamic type parameterized on a type universe
data Dynamic ts
  where
    Dyn :: TypeRep ts a -> a -> Dynamic ts

toDyn :: Typeable ts a => a -> Dynamic ts
toDyn = Dyn typeRep

fromDyn :: forall ts a . (Typeable ts a, TypeEq ts ts) => Dynamic ts -> Maybe a
fromDyn (Dyn t a) = do
    Dict <- typeEq t (typeRep :: TypeRep ts a)
    return a

instance (TypeEq ts ts, Witness Eq ts ts) => Eq (Dynamic ts)
  where
    Dyn ta a == Dyn tb b
        | Just Dict <- typeEq ta tb
        , Dict      <- wit pEq ta
        = a == b
    _ == _ = False

instance Witness Show ts ts => Show (Dynamic ts)
  where
    show (Dyn t a) | Dict <- wit pShow t = show a



----------------------------------------------------------------------------------------------------
-- * Specific types/classes
----------------------------------------------------------------------------------------------------

-- | The universal class
class    Any a
instance Any a

witTypeable :: Witness (Typeable ts) ts ts => TypeRep ts a -> Dict (Typeable ts a)
witTypeable = wit Proxy

pwitTypeable :: PWitness (Typeable ts) ts ts => TypeRep ts a -> Maybe (Dict (Typeable ts a))
pwitTypeable = pwit Proxy

pAny :: Proxy Any
pAny = Proxy

pEq :: Proxy Eq
pEq = Proxy

pOrd :: Proxy Ord
pOrd = Proxy

pShow :: Proxy Show
pShow = Proxy

pNum :: Proxy Num
pNum = Proxy

data BoolType  a where BoolType  :: BoolType  (Full Bool)
data CharType  a where CharType  :: CharType  (Full Char)
data IntType   a where IntType   :: IntType   (Full Int)
data FloatType a where FloatType :: FloatType (Full Float)
data ListType  a where ListType  :: ListType   (a :-> Full [a])
data FunType   a where FunType   :: FunType   (a :-> b :-> Full (a -> b))

instance Render BoolType  where renderSym BoolType  = "Bool"
instance Render CharType  where renderSym CharType  = "Char"
instance Render IntType   where renderSym IntType   = "Int"
instance Render FloatType where renderSym FloatType = "Float"

instance Render ListType
  where
    renderSym ListType = "[]"
    renderArgs [a] ListType = "[" ++ a ++ "]"

instance Render FunType
  where
    renderSym FunType = "(->)"
    renderArgs [a,b] FunType = a ++ " -> " ++ b

boolType :: (Syntactic a, BoolType :<: Domain a, Internal a ~ Bool) => a
boolType = sugarSym BoolType

charType :: (Syntactic a, CharType :<: Domain a, Internal a ~ Char) => a
charType = sugarSym CharType

intType :: (Syntactic a, IntType :<: Domain a, Internal a ~ Int) => a
intType = sugarSym IntType

floatType :: (Syntactic a, FloatType :<: Domain a, Internal a ~ Float) => a
floatType = sugarSym FloatType

listType
    :: ( Syntactic list
       , Syntactic elem
       , Domain list ~ Domain elem
       , ListType :<: Domain list
       , Internal list ~ [Internal elem]
       , elem ~ c e
       , list ~ c l
           -- These last equalities are used to help type inference by forcing the representations
           -- to use the same type constructor (e.g. 'TR' or 'TypeRep')
       )
    => elem -> list
listType = sugarSym ListType

funType
    :: ( Syntactic fun
       , Syntactic a
       , Syntactic b
       , Domain fun ~ Domain a
       , Domain fun ~ Domain b
       , FunType :<: Domain fun
       , Internal fun ~ (Internal a -> Internal b)
       , a   ~ c x
       , b   ~ c y
       , fun ~ c z
       )
    => a -> b -> fun
funType = sugarSym FunType

instance (BoolType  :<: ts)                               => Typeable ts Bool     where typeRep' = boolType
instance (CharType  :<: ts)                               => Typeable ts Char     where typeRep' = charType
instance (IntType   :<: ts)                               => Typeable ts Int      where typeRep' = intType
instance (FloatType :<: ts)                               => Typeable ts Float    where typeRep' = floatType
instance (ListType  :<: ts, Typeable ts a)                => Typeable ts [a]      where typeRep' = listType typeRep'
instance (FunType   :<: ts, Typeable ts a, Typeable ts b) => Typeable ts (a -> b) where typeRep' = funType typeRep' typeRep'

instance TypeEq BoolType  ts where typeEqSym (BoolType, Nil)  (BoolType, Nil)  = Just Dict
instance TypeEq CharType  ts where typeEqSym (CharType, Nil)  (CharType, Nil)  = Just Dict
instance TypeEq IntType   ts where typeEqSym (IntType, Nil)   (IntType, Nil)   = Just Dict
instance TypeEq FloatType ts where typeEqSym (FloatType, Nil) (FloatType, Nil) = Just Dict

instance TypeEq ts ts => TypeEq ListType ts
  where
    typeEqSym (ListType, a :* Nil) (ListType, b :* Nil) = do
        Dict <- typeEq (TypeRep a) (TypeRep b)
        return Dict

instance TypeEq ts ts => TypeEq FunType ts
  where
    typeEqSym (FunType, a1 :* b1 :* Nil) (FunType, a2 :* b2 :* Nil) = do
        Dict <- typeEq (TypeRep a1) (TypeRep a2)
        Dict <- typeEq (TypeRep b1) (TypeRep b2)
        return Dict

instance (BoolType  :<: ts) => Witness (Typeable ts) BoolType  ts where witSym BoolType  Nil = Dict
instance (CharType  :<: ts) => Witness (Typeable ts) CharType  ts where witSym CharType  Nil = Dict
instance (IntType   :<: ts) => Witness (Typeable ts) IntType   ts where witSym IntType   Nil = Dict
instance (FloatType :<: ts) => Witness (Typeable ts) FloatType ts where witSym FloatType Nil = Dict

instance (ListType :<: ts, Witness (Typeable ts) ts ts) => Witness (Typeable ts) ListType ts
  where
    witSym ListType (a :* Nil)
        | Dict <- witTypeable (TypeRep a) = Dict

instance (FunType :<: ts, Witness (Typeable ts) ts ts) => Witness (Typeable ts) FunType ts
  where
    witSym FunType (a :* b :* Nil)
        | Dict <- witTypeable (TypeRep a)
        , Dict <- witTypeable (TypeRep b)
        = Dict

instance (BoolType  :<: ts)                               => PWitness (Typeable ts) BoolType  ts where pwitSym = pwitSymDefault
instance (CharType  :<: ts)                               => PWitness (Typeable ts) CharType  ts where pwitSym = pwitSymDefault
instance (IntType   :<: ts)                               => PWitness (Typeable ts) IntType   ts where pwitSym = pwitSymDefault
instance (FloatType :<: ts)                               => PWitness (Typeable ts) FloatType ts where pwitSym = pwitSymDefault
instance (ListType  :<: ts, PWitness (Typeable ts) ts ts) => PWitness (Typeable ts) ListType  ts where pwitSym ListType (a :* Nil) = do Dict <- pwitTypeable (TypeRep a); return Dict
instance (FunType   :<: ts, PWitness (Typeable ts) ts ts) => PWitness (Typeable ts) FunType   ts where pwitSym FunType (a :* b :* Nil) = do Dict <- pwitTypeable (TypeRep a); Dict <- pwitTypeable (TypeRep b); return Dict

instance Witness Any BoolType  ts where witSym _ _ = Dict
instance Witness Any CharType  ts where witSym _ _ = Dict
instance Witness Any IntType   ts where witSym _ _ = Dict
instance Witness Any FloatType ts where witSym _ _ = Dict
instance Witness Any ListType  ts where witSym _ _ = Dict
instance Witness Any FunType   ts where witSym _ _ = Dict

instance PWitness Any BoolType  ts where pwitSym _ _ = Just Dict
instance PWitness Any CharType  ts where pwitSym _ _ = Just Dict
instance PWitness Any IntType   ts where pwitSym _ _ = Just Dict
instance PWitness Any FloatType ts where pwitSym _ _ = Just Dict
instance PWitness Any ListType  ts where pwitSym _ _ = Just Dict
instance PWitness Any FunType   ts where pwitSym _ _ = Just Dict

instance                     Witness Eq BoolType  ts where witSym BoolType  Nil = Dict
instance                     Witness Eq CharType  ts where witSym CharType  Nil = Dict
instance                     Witness Eq IntType   ts where witSym IntType   Nil = Dict
instance                     Witness Eq FloatType ts where witSym FloatType Nil = Dict
instance Witness Eq ts ts => Witness Eq ListType  ts where witSym ListType (a :* Nil) | Dict <- wit pEq (TypeRep a) = Dict

instance                      PWitness Eq BoolType  ts where pwitSym = pwitSymDefault
instance                      PWitness Eq CharType  ts where pwitSym = pwitSymDefault
instance                      PWitness Eq IntType   ts where pwitSym = pwitSymDefault
instance                      PWitness Eq FloatType ts where pwitSym = pwitSymDefault
instance PWitness Eq ts ts => PWitness Eq ListType  ts where pwitSym ListType (a :* Nil) = do Dict <- pwit pEq (TypeRep a); return Dict
instance PWitness Eq FunType ts

instance                      Witness Ord BoolType  ts where witSym BoolType  Nil = Dict
instance                      Witness Ord CharType  ts where witSym CharType  Nil = Dict
instance                      Witness Ord IntType   ts where witSym IntType   Nil = Dict
instance                      Witness Ord FloatType ts where witSym FloatType Nil = Dict
instance Witness Ord ts ts => Witness Ord ListType  ts where witSym ListType (a :* Nil) | Dict <- wit pOrd (TypeRep a) = Dict

instance                       PWitness Ord BoolType  ts where pwitSym = pwitSymDefault
instance                       PWitness Ord CharType  ts where pwitSym = pwitSymDefault
instance                       PWitness Ord IntType   ts where pwitSym = pwitSymDefault
instance                       PWitness Ord FloatType ts where pwitSym = pwitSymDefault
instance PWitness Ord ts ts => PWitness Ord ListType  ts where pwitSym ListType (a :* Nil) = do Dict <- pwit pOrd (TypeRep a); return Dict
instance PWitness Ord FunType ts

instance                       Witness Show BoolType  ts where witSym BoolType  Nil = Dict
instance                       Witness Show CharType  ts where witSym CharType  Nil = Dict
instance                       Witness Show IntType   ts where witSym IntType   Nil = Dict
instance                       Witness Show FloatType ts where witSym FloatType Nil = Dict
instance Witness Show ts ts => Witness Show ListType  ts where witSym ListType (a :* Nil) | Dict <- wit pShow (TypeRep a) = Dict

instance                        PWitness Show BoolType  ts where pwitSym = pwitSymDefault
instance                        PWitness Show CharType  ts where pwitSym = pwitSymDefault
instance                        PWitness Show IntType   ts where pwitSym = pwitSymDefault
instance                        PWitness Show FloatType ts where pwitSym = pwitSymDefault
instance PWitness Show ts ts => PWitness Show ListType  ts where pwitSym ListType (a :* Nil) = do Dict <- pwit pShow (TypeRep a); return Dict
instance PWitness Show FunType ts

instance Witness Num IntType   ts where witSym IntType   Nil = Dict
instance Witness Num FloatType ts where witSym FloatType Nil = Dict

instance PWitness Num BoolType  ts
instance PWitness Num CharType  ts
instance PWitness Num IntType   ts where pwitSym = pwitSymDefault
instance PWitness Num FloatType ts where pwitSym = pwitSymDefault
instance PWitness Num ListType  ts
instance PWitness Num FunType   ts

