{-# LANGUAGE UndecidableInstances #-}

-- | 'Syntactic' instances for tuples with 'Poly' context
module Language.Syntactic.Features.TupleSyntacticPoly where



import Data.Proxy

import Language.Syntactic.Syntax
import Language.Syntactic.Features.Tuple



instance
    ( Syntactic a dom
    , Syntactic b dom
    , Tuple  Poly :<: dom
    , Select Poly :<: dom
    ) =>
      Syntactic (a,b) dom
  where
    type Internal (a,b) =
        ( Internal a
        , Internal b
        )

    desugar = desugarTup2 poly
    sugar   = sugarTup2 poly

instance
    ( Syntactic a dom
    , Syntactic b dom
    , Syntactic c dom
    , Tuple  Poly :<: dom
    , Select Poly :<: dom
    ) =>
      Syntactic (a,b,c) dom
  where
    type Internal (a,b,c) =
        ( Internal a
        , Internal b
        , Internal c
        )

    desugar = desugarTup3 poly
    sugar   = sugarTup3 poly

instance
    ( Syntactic a dom
    , Syntactic b dom
    , Syntactic c dom
    , Syntactic d dom
    , Tuple  Poly :<: dom
    , Select Poly :<: dom
    ) =>
      Syntactic (a,b,c,d) dom
  where
    type Internal (a,b,c,d) =
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        )

    desugar = desugarTup4 poly
    sugar   = sugarTup4 poly

instance
    ( Syntactic a dom
    , Syntactic b dom
    , Syntactic c dom
    , Syntactic d dom
    , Syntactic e dom
    , Tuple  Poly :<: dom
    , Select Poly :<: dom
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

    desugar = desugarTup5 poly
    sugar   = sugarTup5 poly

instance
    ( Syntactic a dom
    , Syntactic b dom
    , Syntactic c dom
    , Syntactic d dom
    , Syntactic e dom
    , Syntactic f dom
    , Tuple  Poly :<: dom
    , Select Poly :<: dom
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

    desugar = desugarTup6 poly
    sugar   = sugarTup6 poly

instance
    ( Syntactic a dom
    , Syntactic b dom
    , Syntactic c dom
    , Syntactic d dom
    , Syntactic e dom
    , Syntactic f dom
    , Syntactic g dom
    , Tuple  Poly :<: dom
    , Select Poly :<: dom
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

    desugar = desugarTup7 poly
    sugar   = sugarTup7 poly

