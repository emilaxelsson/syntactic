{-# LANGUAGE UndecidableInstances #-}

-- | 'Syntactic' instances for Haskell tuples

module Language.Syntactic.Frontend.Tuple where



import Language.Syntactic
import Language.Syntactic.Constructs.Tuple
import Data.Tuple.Curry



instance
    ( Syntactic a dom
    , Syntactic b dom
    , InjectC Tuple dom
        ( Internal a
        , Internal b
        )
    , InjectC Select dom (Internal a)
    , InjectC Select dom (Internal b)
    ) =>
      Syntactic (a,b) dom
  where
    type Internal (a,b) =
        ( Internal a
        , Internal b
        )

    desugar = uncurryN $ sugarSymC Tup2
    sugar a =
        ( sugarSymC Sel1 a
        , sugarSymC Sel2 a
        )

instance
    ( Syntactic a dom
    , Syntactic b dom
    , Syntactic c dom
    , InjectC Tuple dom
        ( Internal a
        , Internal b
        , Internal c
        )
    , InjectC Select dom (Internal a)
    , InjectC Select dom (Internal b)
    , InjectC Select dom (Internal c)
    ) =>
      Syntactic (a,b,c) dom
  where
    type Internal (a,b,c) =
        ( Internal a
        , Internal b
        , Internal c
        )

    desugar = uncurryN $ sugarSymC Tup3
    sugar a =
        ( sugarSymC Sel1 a
        , sugarSymC Sel2 a
        , sugarSymC Sel3 a
        )

instance
    ( Syntactic a dom
    , Syntactic b dom
    , Syntactic c dom
    , Syntactic d dom
    , InjectC Tuple dom
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        )
    , InjectC Select dom (Internal a)
    , InjectC Select dom (Internal b)
    , InjectC Select dom (Internal c)
    , InjectC Select dom (Internal d)
    ) =>
      Syntactic (a,b,c,d) dom
  where
    type Internal (a,b,c,d) =
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        )

    desugar = uncurryN $ sugarSymC Tup4
    sugar a =
        ( sugarSymC Sel1 a
        , sugarSymC Sel2 a
        , sugarSymC Sel3 a
        , sugarSymC Sel4 a
        )

instance
    ( Syntactic a dom
    , Syntactic b dom
    , Syntactic c dom
    , Syntactic d dom
    , Syntactic e dom
    , InjectC Tuple dom
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        )
    , InjectC Select dom (Internal a)
    , InjectC Select dom (Internal b)
    , InjectC Select dom (Internal c)
    , InjectC Select dom (Internal d)
    , InjectC Select dom (Internal e)
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

    desugar = uncurryN $ sugarSymC Tup5
    sugar a =
        ( sugarSymC Sel1 a
        , sugarSymC Sel2 a
        , sugarSymC Sel3 a
        , sugarSymC Sel4 a
        , sugarSymC Sel5 a
        )

instance
    ( Syntactic a dom
    , Syntactic b dom
    , Syntactic c dom
    , Syntactic d dom
    , Syntactic e dom
    , Syntactic f dom
    , InjectC Tuple dom
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        )
    , InjectC Select dom (Internal a)
    , InjectC Select dom (Internal b)
    , InjectC Select dom (Internal c)
    , InjectC Select dom (Internal d)
    , InjectC Select dom (Internal e)
    , InjectC Select dom (Internal f)
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

    desugar = uncurryN $ sugarSymC Tup6
    sugar a =
        ( sugarSymC Sel1 a
        , sugarSymC Sel2 a
        , sugarSymC Sel3 a
        , sugarSymC Sel4 a
        , sugarSymC Sel5 a
        , sugarSymC Sel6 a
        )

instance
    ( Syntactic a dom
    , Syntactic b dom
    , Syntactic c dom
    , Syntactic d dom
    , Syntactic e dom
    , Syntactic f dom
    , Syntactic g dom
    , InjectC Tuple dom
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        )
    , InjectC Select dom (Internal a)
    , InjectC Select dom (Internal b)
    , InjectC Select dom (Internal c)
    , InjectC Select dom (Internal d)
    , InjectC Select dom (Internal e)
    , InjectC Select dom (Internal f)
    , InjectC Select dom (Internal g)
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

    desugar = uncurryN $ sugarSymC Tup7
    sugar a =
        ( sugarSymC Sel1 a
        , sugarSymC Sel2 a
        , sugarSymC Sel3 a
        , sugarSymC Sel4 a
        , sugarSymC Sel5 a
        , sugarSymC Sel6 a
        , sugarSymC Sel7 a
        )

