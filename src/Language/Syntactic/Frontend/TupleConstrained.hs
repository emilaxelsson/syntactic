{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Constrained 'Syntactic' instances for Haskell tuples

module Language.Syntactic.Frontend.TupleConstrained
    ( TupleSat
    ) where



import Data.Constraint
import Data.Tuple.Curry

import Language.Syntactic
import Language.Syntactic.Constructs.Tuple



-- | Type-level function computing the predicate attached to 'Tuple' or 'Select'
-- (whichever appears first) in a domain.
class TupleSat (dom :: * -> *) (p :: * -> Constraint) | dom -> p

instance TupleSat (Tuple :|| p) p
instance TupleSat ((Tuple :|| p) :+: dom2) p

instance TupleSat (Select :|| p) p
instance TupleSat ((Select :|| p) :+: dom2) p

instance TupleSat dom p => TupleSat (dom :| q) p
instance TupleSat dom p => TupleSat (dom :|| q) p
instance TupleSat dom2 p => TupleSat (dom1 :+: dom2) p



sugarSymC' :: forall sym dom sig b c p
    .  ( TupleSat dom p
       , p (DenResult sig)
       , InjectC (sym :|| p) (AST dom) (DenResult sig)
       , ApplySym sig b dom
       , SyntacticN c b
       )
    => sym sig -> c
sugarSymC' s = sugarSymC (C' s :: (sym :|| p) sig)



instance
    ( Syntactic a dom
    , Syntactic b dom
    , TupleSat dom p
    , p (Internal a, Internal b)
    , p (Internal a)
    , p (Internal b)
    , InjectC (Tuple :|| p) dom
        ( Internal a
        , Internal b
        )
    , InjectC (Select :|| p) dom (Internal a)
    , InjectC (Select :|| p) dom (Internal b)
    ) =>
      Syntactic (a,b) dom
  where
    type Internal (a,b) =
        ( Internal a
        , Internal b
        )

    desugar = uncurryN $ sugarSymC' Tup2
    sugar a =
        ( sugarSymC' Sel1 a
        , sugarSymC' Sel2 a
        )

instance
    ( Syntactic a dom
    , Syntactic b dom
    , Syntactic c dom
    , TupleSat dom p
    , p ( Internal a
        , Internal b
        , Internal c
        )
    , p (Internal a)
    , p (Internal b)
    , p (Internal c)
    , InjectC (Tuple :|| p) dom
        ( Internal a
        , Internal b
        , Internal c
        )
    , InjectC (Select :|| p) dom (Internal a)
    , InjectC (Select :|| p) dom (Internal b)
    , InjectC (Select :|| p) dom (Internal c)
    ) =>
      Syntactic (a,b,c) dom
  where
    type Internal (a,b,c) =
        ( Internal a
        , Internal b
        , Internal c
        )

    desugar = uncurryN $ sugarSymC' Tup3
    sugar a =
        ( sugarSymC' Sel1 a
        , sugarSymC' Sel2 a
        , sugarSymC' Sel3 a
        )

instance
    ( Syntactic a dom
    , Syntactic b dom
    , Syntactic c dom
    , Syntactic d dom
    , TupleSat dom p
    , p ( Internal a
        , Internal b
        , Internal c
        , Internal d
        )
    , p (Internal a)
    , p (Internal b)
    , p (Internal c)
    , p (Internal d)
    , InjectC (Tuple :|| p) dom
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        )
    , InjectC (Select :|| p) dom (Internal a)
    , InjectC (Select :|| p) dom (Internal b)
    , InjectC (Select :|| p) dom (Internal c)
    , InjectC (Select :|| p) dom (Internal d)
    ) =>
      Syntactic (a,b,c,d) dom
  where
    type Internal (a,b,c,d) =
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        )

    desugar = uncurryN $ sugarSymC' Tup4
    sugar a =
        ( sugarSymC' Sel1 a
        , sugarSymC' Sel2 a
        , sugarSymC' Sel3 a
        , sugarSymC' Sel4 a
        )

instance
    ( Syntactic a dom
    , Syntactic b dom
    , Syntactic c dom
    , Syntactic d dom
    , Syntactic e dom
    , TupleSat dom p
    , p ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        )
    , p (Internal a)
    , p (Internal b)
    , p (Internal c)
    , p (Internal d)
    , p (Internal e)
    , InjectC (Tuple :|| p) dom
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        )
    , InjectC (Select :|| p) dom (Internal a)
    , InjectC (Select :|| p) dom (Internal b)
    , InjectC (Select :|| p) dom (Internal c)
    , InjectC (Select :|| p) dom (Internal d)
    , InjectC (Select :|| p) dom (Internal e)
    ) =>
      Syntactic (a,b,c,d,e) dom
  where
    type Internal (a,b,c,d,e) =
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        )

    desugar = uncurryN $ sugarSymC' Tup5
    sugar a =
        ( sugarSymC' Sel1 a
        , sugarSymC' Sel2 a
        , sugarSymC' Sel3 a
        , sugarSymC' Sel4 a
        , sugarSymC' Sel5 a
        )

instance
    ( Syntactic a dom
    , Syntactic b dom
    , Syntactic c dom
    , Syntactic d dom
    , Syntactic e dom
    , Syntactic f dom
    , TupleSat dom p
    , p ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        )
    , p (Internal a)
    , p (Internal b)
    , p (Internal c)
    , p (Internal d)
    , p (Internal e)
    , p (Internal f)
    , InjectC (Tuple :|| p) dom
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        )
    , InjectC (Select :|| p) dom (Internal a)
    , InjectC (Select :|| p) dom (Internal b)
    , InjectC (Select :|| p) dom (Internal c)
    , InjectC (Select :|| p) dom (Internal d)
    , InjectC (Select :|| p) dom (Internal e)
    , InjectC (Select :|| p) dom (Internal f)
    ) =>
      Syntactic (a,b,c,d,e,f) dom
  where
    type Internal (a,b,c,d,e,f) =
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        )

    desugar = uncurryN $ sugarSymC' Tup6
    sugar a =
        ( sugarSymC' Sel1 a
        , sugarSymC' Sel2 a
        , sugarSymC' Sel3 a
        , sugarSymC' Sel4 a
        , sugarSymC' Sel5 a
        , sugarSymC' Sel6 a
        )

instance
    ( Syntactic a dom
    , Syntactic b dom
    , Syntactic c dom
    , Syntactic d dom
    , Syntactic e dom
    , Syntactic f dom
    , Syntactic g dom
    , TupleSat dom p
    , p ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        )
    , p (Internal a)
    , p (Internal b)
    , p (Internal c)
    , p (Internal d)
    , p (Internal e)
    , p (Internal f)
    , p (Internal g)
    , InjectC (Tuple :|| p) dom
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        )
    , InjectC (Select :|| p) dom (Internal a)
    , InjectC (Select :|| p) dom (Internal b)
    , InjectC (Select :|| p) dom (Internal c)
    , InjectC (Select :|| p) dom (Internal d)
    , InjectC (Select :|| p) dom (Internal e)
    , InjectC (Select :|| p) dom (Internal f)
    , InjectC (Select :|| p) dom (Internal g)
    ) =>
      Syntactic (a,b,c,d,e,f,g) dom
  where
    type Internal (a,b,c,d,e,f,g) =
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        )

    desugar = uncurryN $ sugarSymC' Tup7
    sugar a =
        ( sugarSymC' Sel1 a
        , sugarSymC' Sel2 a
        , sugarSymC' Sel3 a
        , sugarSymC' Sel4 a
        , sugarSymC' Sel5 a
        , sugarSymC' Sel6 a
        , sugarSymC' Sel7 a
        )

