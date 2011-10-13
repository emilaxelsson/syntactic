{-# LANGUAGE UndecidableInstances #-}

-- | 'Syntactic' instances for tuples with 'SimpleCtx' context
module Language.Syntactic.Constructs.TupleSyntacticSimple where



import Language.Syntactic.Syntax
import Language.Syntactic.Constructs.Tuple



instance
    ( Syntactic a dom, Eq (Internal a), Show (Internal a)
    , Syntactic b dom, Eq (Internal b), Show (Internal b)
    , Tuple  SimpleCtx :<: dom
    , Select SimpleCtx :<: dom
    ) =>
      Syntactic (a,b) dom
  where
    type Internal (a,b) =
        ( Internal a
        , Internal b
        )

    desugar = desugarTup2 simpleCtx
    sugar   = sugarTup2 simpleCtx

instance
    ( Syntactic a dom, Eq (Internal a), Show (Internal a)
    , Syntactic b dom, Eq (Internal b), Show (Internal b)
    , Syntactic c dom, Eq (Internal c), Show (Internal c)
    , Tuple  SimpleCtx :<: dom
    , Select SimpleCtx :<: dom
    ) =>
      Syntactic (a,b,c) dom
  where
    type Internal (a,b,c) =
        ( Internal a
        , Internal b
        , Internal c
        )

    desugar = desugarTup3 simpleCtx
    sugar   = sugarTup3 simpleCtx

instance
    ( Syntactic a dom, Eq (Internal a), Show (Internal a)
    , Syntactic b dom, Eq (Internal b), Show (Internal b)
    , Syntactic c dom, Eq (Internal c), Show (Internal c)
    , Syntactic d dom, Eq (Internal d), Show (Internal d)
    , Tuple  SimpleCtx :<: dom
    , Select SimpleCtx :<: dom
    ) =>
      Syntactic (a,b,c,d) dom
  where
    type Internal (a,b,c,d) =
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        )

    desugar = desugarTup4 simpleCtx
    sugar   = sugarTup4 simpleCtx

instance
    ( Syntactic a dom, Eq (Internal a), Show (Internal a)
    , Syntactic b dom, Eq (Internal b), Show (Internal b)
    , Syntactic c dom, Eq (Internal c), Show (Internal c)
    , Syntactic d dom, Eq (Internal d), Show (Internal d)
    , Syntactic e dom, Eq (Internal e), Show (Internal e)
    , Tuple  SimpleCtx :<: dom
    , Select SimpleCtx :<: dom
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

    desugar = desugarTup5 simpleCtx
    sugar   = sugarTup5 simpleCtx

instance
    ( Syntactic a dom, Eq (Internal a), Show (Internal a)
    , Syntactic b dom, Eq (Internal b), Show (Internal b)
    , Syntactic c dom, Eq (Internal c), Show (Internal c)
    , Syntactic d dom, Eq (Internal d), Show (Internal d)
    , Syntactic e dom, Eq (Internal e), Show (Internal e)
    , Syntactic f dom, Eq (Internal f), Show (Internal f)
    , Tuple  SimpleCtx :<: dom
    , Select SimpleCtx :<: dom
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

    desugar = desugarTup6 simpleCtx
    sugar   = sugarTup6 simpleCtx

instance
    ( Syntactic a dom, Eq (Internal a), Show (Internal a)
    , Syntactic b dom, Eq (Internal b), Show (Internal b)
    , Syntactic c dom, Eq (Internal c), Show (Internal c)
    , Syntactic d dom, Eq (Internal d), Show (Internal d)
    , Syntactic e dom, Eq (Internal e), Show (Internal e)
    , Syntactic f dom, Eq (Internal f), Show (Internal f)
    , Syntactic g dom, Eq (Internal g), Show (Internal g)
    , Tuple  SimpleCtx :<: dom
    , Select SimpleCtx :<: dom
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

    desugar = desugarTup7 simpleCtx
    sugar   = sugarTup7 simpleCtx

