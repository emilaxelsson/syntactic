{-# LANGUAGE UndecidableInstances #-}

-- | Construction and selection of tuples

module Language.Syntactic.Features.Tuple where



import Data.Hash
import Data.Tuple.Select

import Language.Syntactic.Syntax
import Language.Syntactic.Analysis.Equality
import Language.Syntactic.Analysis.Render
import Language.Syntactic.Analysis.Evaluation
import Language.Syntactic.Analysis.Hash



-- | Expressions for constructing tuples
data Tuple a
  where
    Tup2 :: Tuple (a :-> b :-> Full (a,b))
    Tup3 :: Tuple (a :-> b :-> c :-> Full (a,b,c))
    Tup4 :: Tuple (a :-> b :-> c :-> d :-> Full (a,b,c,d))
    Tup5 :: Tuple (a :-> b :-> c :-> d :-> e :-> Full (a,b,c,d,e))
    Tup6 :: Tuple (a :-> b :-> c :-> d :-> e :-> f :-> Full (a,b,c,d,e,f))
    Tup7 :: Tuple (a :-> b :-> c :-> d :-> e :-> f :-> g :-> Full (a,b,c,d,e,f,g))

instance ExprEq Tuple
  where
    Tup2 `exprEq` Tup2 = True
    Tup3 `exprEq` Tup3 = True
    Tup4 `exprEq` Tup4 = True
    Tup5 `exprEq` Tup5 = True
    Tup6 `exprEq` Tup6 = True
    Tup7 `exprEq` Tup7 = True
    exprEq _ _ = False

instance Render Tuple
  where
    render Tup2 = "tup2"
    render Tup3 = "tup3"
    render Tup4 = "tup4"
    render Tup5 = "tup5"
    render Tup6 = "tup6"
    render Tup7 = "tup7"

instance ToTree Tuple

instance Eval Tuple
  where
    evaluate Tup2 = consEval (,)
    evaluate Tup3 = consEval (,,)
    evaluate Tup4 = consEval (,,,)
    evaluate Tup5 = consEval (,,,,)
    evaluate Tup6 = consEval (,,,,,)
    evaluate Tup7 = consEval (,,,,,,)

instance ExprHash Tuple
  where
    exprHash Tup2 = hashInt 0
    exprHash Tup3 = hashInt 1
    exprHash Tup4 = hashInt 2
    exprHash Tup5 = hashInt 3
    exprHash Tup6 = hashInt 4
    exprHash Tup7 = hashInt 5

-- | Expressions for selecting elements of a tuple
data Select a
  where
    Sel1 :: Sel1 a b => Select (a :-> Full b)
    Sel2 :: Sel2 a b => Select (a :-> Full b)
    Sel3 :: Sel3 a b => Select (a :-> Full b)
    Sel4 :: Sel4 a b => Select (a :-> Full b)
    Sel5 :: Sel5 a b => Select (a :-> Full b)
    Sel6 :: Sel6 a b => Select (a :-> Full b)
    Sel7 :: Sel7 a b => Select (a :-> Full b)

instance ExprEq Select
  where
    Sel1 `exprEq` Sel1 = True
    Sel2 `exprEq` Sel2 = True
    Sel3 `exprEq` Sel3 = True
    Sel4 `exprEq` Sel4 = True
    Sel5 `exprEq` Sel5 = True
    Sel6 `exprEq` Sel6 = True
    Sel7 `exprEq` Sel7 = True
    exprEq _ _ = False

instance Eval Select
  where
    evaluate Sel1 = consEval sel1
    evaluate Sel2 = consEval sel2
    evaluate Sel3 = consEval sel3
    evaluate Sel4 = consEval sel4
    evaluate Sel5 = consEval sel5
    evaluate Sel6 = consEval sel6
    evaluate Sel7 = consEval sel7

instance Render Select
  where
    render Sel1 = "sel1"
    render Sel2 = "sel2"
    render Sel3 = "sel3"
    render Sel4 = "sel4"
    render Sel5 = "sel5"
    render Sel6 = "sel6"
    render Sel7 = "sel7"

instance ToTree Select

instance ExprHash Select
  where
    exprHash Sel1 = hashInt 0
    exprHash Sel2 = hashInt 1
    exprHash Sel3 = hashInt 2
    exprHash Sel4 = hashInt 3
    exprHash Sel5 = hashInt 4
    exprHash Sel6 = hashInt 5
    exprHash Sel7 = hashInt 6

-- | Return the selected position, e.g.
--
-- > selectPos (Sel3 :: Select ((Int,Int,Int,Int) -> Int)) = 3
selectPos :: Select a -> Int
selectPos Sel1 = 1
selectPos Sel2 = 2
selectPos Sel3 = 3
selectPos Sel4 = 4
selectPos Sel5 = 5
selectPos Sel6 = 6
selectPos Sel7 = 7



instance
    ( Syntactic a expr
    , Syntactic b expr
    , Tuple  :<: expr
    , Select :<: expr
    ) =>
      Syntactic (a,b) expr
  where
    type Internal (a,b) =
        ( Internal a
        , Internal b
        )

    desugar (a,b) = inject Tup2
        :$: desugar a
        :$: desugar b

    sugar a =
        ( sugar $ inject Sel1 :$: a
        , sugar $ inject Sel2 :$: a
        )

instance
    ( Syntactic a expr
    , Syntactic b expr
    , Syntactic c expr
    , Tuple  :<: expr
    , Select :<: expr
    ) =>
      Syntactic (a,b,c) expr
  where
    type Internal (a,b,c) =
        ( Internal a
        , Internal b
        , Internal c
        )

    desugar (a,b,c) = inject Tup3
        :$: desugar a
        :$: desugar b
        :$: desugar c

    sugar a =
        ( sugar $ inject Sel1 :$: a
        , sugar $ inject Sel2 :$: a
        , sugar $ inject Sel3 :$: a
        )

instance
    ( Syntactic a expr
    , Syntactic b expr
    , Syntactic c expr
    , Syntactic d expr
    , Tuple  :<: expr
    , Select :<: expr
    ) =>
      Syntactic (a,b,c,d) expr
  where
    type Internal (a,b,c,d) =
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        )

    desugar (a,b,c,d) = inject Tup4
        :$: desugar a
        :$: desugar b
        :$: desugar c
        :$: desugar d

    sugar a =
        ( sugar $ inject Sel1 :$: a
        , sugar $ inject Sel2 :$: a
        , sugar $ inject Sel3 :$: a
        , sugar $ inject Sel4 :$: a
        )

instance
    ( Syntactic a expr
    , Syntactic b expr
    , Syntactic c expr
    , Syntactic d expr
    , Syntactic e expr
    , Tuple  :<: expr
    , Select :<: expr
    ) =>
      Syntactic (a,b,c,d,e) expr
  where
    type Internal (a,b,c,d,e) =
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        )

    desugar (a,b,c,d,e) = inject Tup5
        :$: desugar a
        :$: desugar b
        :$: desugar c
        :$: desugar d
        :$: desugar e

    sugar a =
        ( sugar $ inject Sel1 :$: a
        , sugar $ inject Sel2 :$: a
        , sugar $ inject Sel3 :$: a
        , sugar $ inject Sel4 :$: a
        , sugar $ inject Sel5 :$: a
        )

instance
    ( Syntactic a expr
    , Syntactic b expr
    , Syntactic c expr
    , Syntactic d expr
    , Syntactic e expr
    , Syntactic f expr
    , Tuple  :<: expr
    , Select :<: expr
    ) =>
      Syntactic (a,b,c,d,e,f) expr
  where
    type Internal (a,b,c,d,e,f) =
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        )

    desugar (a,b,c,d,e,f) = inject Tup6
        :$: desugar a
        :$: desugar b
        :$: desugar c
        :$: desugar d
        :$: desugar e
        :$: desugar f

    sugar a =
        ( sugar $ inject Sel1 :$: a
        , sugar $ inject Sel2 :$: a
        , sugar $ inject Sel3 :$: a
        , sugar $ inject Sel4 :$: a
        , sugar $ inject Sel5 :$: a
        , sugar $ inject Sel6 :$: a
        )

instance
    ( Syntactic a expr
    , Syntactic b expr
    , Syntactic c expr
    , Syntactic d expr
    , Syntactic e expr
    , Syntactic f expr
    , Syntactic g expr
    , Tuple  :<: expr
    , Select :<: expr
    ) =>
      Syntactic (a,b,c,d,e,f,g) expr
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

    desugar (a,b,c,d,e,f,g) = inject Tup7
        :$: desugar a
        :$: desugar b
        :$: desugar c
        :$: desugar d
        :$: desugar e
        :$: desugar f
        :$: desugar g

    sugar a =
        ( sugar $ inject Sel1 :$: a
        , sugar $ inject Sel2 :$: a
        , sugar $ inject Sel3 :$: a
        , sugar $ inject Sel4 :$: a
        , sugar $ inject Sel5 :$: a
        , sugar $ inject Sel6 :$: a
        , sugar $ inject Sel7 :$: a
        )

