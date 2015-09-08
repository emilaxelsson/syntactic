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

instance TupleSat (Tuple :|| p) p where
  {-# SPECIALIZE instance TupleSat (Tuple :|| p) p #-}
instance TupleSat ((Tuple :|| p) :+: dom2) p where
  {-# SPECIALIZE instance TupleSat ((Tuple :|| p) :+: dom2) p #-}

instance TupleSat (Select :|| p) p where
  {-# SPECIALIZE instance TupleSat (Select :|| p) p #-}
instance TupleSat ((Select :|| p) :+: dom2) p where
  {-# SPECIALIZE instance TupleSat ((Select :|| p) :+: dom2) p #-}

instance TupleSat dom p => TupleSat (dom :| q) p where
  {-# SPECIALIZE instance TupleSat dom p => TupleSat (dom :| q) p #-}
instance TupleSat dom p => TupleSat (dom :|| q) p where
  {-# SPECIALIZE instance TupleSat dom p => TupleSat (dom :|| q) p #-}
instance TupleSat dom2 p => TupleSat (dom1 :+: dom2) p where
  {-# SPECIALIZE instance TupleSat dom2 p => TupleSat (dom1 :+: dom2) p #-}



sugarSymC' :: forall sym dom sig b c p
    .  ( TupleSat dom p
       , p (DenResult sig)
       , InjectC (sym :|| p) (AST dom) (DenResult sig)
       , ApplySym sig b dom
       , SyntacticN c b
       )
    => sym sig -> c
sugarSymC' s = sugarSymC (C' s :: (sym :|| p) sig)
{-# INLINABLE sugarSymC' #-}



instance
    ( Syntactic a, Domain a ~ dom
    , Syntactic b, Domain b ~ dom
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
      Syntactic (a,b)
  where
    {-# SPECIALIZE instance ( Syntactic a, Domain a ~ dom
                            , Syntactic b, Domain b ~ dom
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
                            ) => Syntactic (a,b) #-}
    {-# INLINABLE desugar #-}
    {-# INLINABLE sugar #-}
    type Domain (a,b) = Domain a
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
    ( Syntactic a, Domain a ~ dom
    , Syntactic b, Domain b ~ dom
    , Syntactic c, Domain c ~ dom
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
      Syntactic (a,b,c)
  where
    {-# SPECIALIZE instance ( Syntactic a, Domain a ~ dom
                            , Syntactic b, Domain b ~ dom
                            , Syntactic c, Domain c ~ dom
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
                            ) => Syntactic (a,b,c) #-}
    {-# INLINABLE desugar #-}
    {-# INLINABLE sugar #-}
    type Domain (a,b,c) = Domain a
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
    ( Syntactic a, Domain a ~ dom
    , Syntactic b, Domain b ~ dom
    , Syntactic c, Domain c ~ dom
    , Syntactic d, Domain d ~ dom
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
      Syntactic (a,b,c,d)
  where
    {-# SPECIALIZE instance ( Syntactic a, Domain a ~ dom
                            , Syntactic b, Domain b ~ dom
                            , Syntactic c, Domain c ~ dom
                            , Syntactic d, Domain d ~ dom
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
                            ) => Syntactic (a,b,c,d) #-}
    {-# INLINABLE desugar #-}
    {-# INLINABLE sugar #-}
    type Domain (a,b,c,d) = Domain a
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
    ( Syntactic a, Domain a ~ dom
    , Syntactic b, Domain b ~ dom
    , Syntactic c, Domain c ~ dom
    , Syntactic d, Domain d ~ dom
    , Syntactic e, Domain e ~ dom
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
      Syntactic (a,b,c,d,e)
  where
    {-# SPECIALIZE instance ( Syntactic a, Domain a ~ dom
                            , Syntactic b, Domain b ~ dom
                            , Syntactic c, Domain c ~ dom
                            , Syntactic d, Domain d ~ dom
                            , Syntactic e, Domain e ~ dom
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
                            ) => Syntactic (a,b,c,d,e) #-}
    {-# INLINABLE desugar #-}
    {-# INLINABLE sugar #-}
    type Domain (a,b,c,d,e) = Domain a
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
    ( Syntactic a, Domain a ~ dom
    , Syntactic b, Domain b ~ dom
    , Syntactic c, Domain c ~ dom
    , Syntactic d, Domain d ~ dom
    , Syntactic e, Domain e ~ dom
    , Syntactic f, Domain f ~ dom
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
      Syntactic (a,b,c,d,e,f)
  where
    {-# SPECIALIZE instance ( Syntactic a, Domain a ~ dom
                            , Syntactic b, Domain b ~ dom
                            , Syntactic c, Domain c ~ dom
                            , Syntactic d, Domain d ~ dom
                            , Syntactic e, Domain e ~ dom
                            , Syntactic f, Domain f ~ dom
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
                            ) => Syntactic (a,b,c,d,e,f) #-}
    {-# INLINABLE desugar #-}
    {-# INLINABLE sugar #-}
    type Domain (a,b,c,d,e,f) = Domain a
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
    ( Syntactic a, Domain a ~ dom
    , Syntactic b, Domain b ~ dom
    , Syntactic c, Domain c ~ dom
    , Syntactic d, Domain d ~ dom
    , Syntactic e, Domain e ~ dom
    , Syntactic f, Domain f ~ dom
    , Syntactic g, Domain g ~ dom
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
      Syntactic (a,b,c,d,e,f,g)
  where
    {-# SPECIALIZE instance ( Syntactic a, Domain a ~ dom
                            , Syntactic b, Domain b ~ dom
                            , Syntactic c, Domain c ~ dom
                            , Syntactic d, Domain d ~ dom
                            , Syntactic e, Domain e ~ dom
                            , Syntactic f, Domain f ~ dom
                            , Syntactic g, Domain g ~ dom
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
                            ) => Syntactic (a,b,c,d,e,f,g) #-}
    {-# INLINABLE desugar #-}
    {-# INLINABLE sugar #-}
    type Domain (a,b,c,d,e,f,g) = Domain a
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


instance
    ( Syntactic a, Domain a ~ dom
    , Syntactic b, Domain b ~ dom
    , Syntactic c, Domain c ~ dom
    , Syntactic d, Domain d ~ dom
    , Syntactic e, Domain e ~ dom
    , Syntactic f, Domain f ~ dom
    , Syntactic g, Domain g ~ dom
    , Syntactic h, Domain h ~ dom
    , TupleSat dom p
    , p ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        , Internal h
        )
    , p (Internal a)
    , p (Internal b)
    , p (Internal c)
    , p (Internal d)
    , p (Internal e)
    , p (Internal f)
    , p (Internal g)
    , p (Internal h)
    , InjectC (Tuple :|| p) dom
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        , Internal h
        )
    , InjectC (Select :|| p) dom (Internal a)
    , InjectC (Select :|| p) dom (Internal b)
    , InjectC (Select :|| p) dom (Internal c)
    , InjectC (Select :|| p) dom (Internal d)
    , InjectC (Select :|| p) dom (Internal e)
    , InjectC (Select :|| p) dom (Internal f)
    , InjectC (Select :|| p) dom (Internal g)
    , InjectC (Select :|| p) dom (Internal h)
    ) =>
      Syntactic (a,b,c,d,e,f,g,h)
  where
    {-# SPECIALIZE instance ( Syntactic a, Domain a ~ dom
                            , Syntactic b, Domain b ~ dom
                            , Syntactic c, Domain c ~ dom
                            , Syntactic d, Domain d ~ dom
                            , Syntactic e, Domain e ~ dom
                            , Syntactic f, Domain f ~ dom
                            , Syntactic g, Domain g ~ dom
                            , Syntactic h, Domain h ~ dom
                            , TupleSat dom p
                            , p ( Internal a
                                , Internal b
                                , Internal c
                                , Internal d
                                , Internal e
                                , Internal f
                                , Internal g
                                , Internal h
                                )
                            , p (Internal a)
                            , p (Internal b)
                            , p (Internal c)
                            , p (Internal d)
                            , p (Internal e)
                            , p (Internal f)
                            , p (Internal g)
                            , p (Internal h)
                            , InjectC (Tuple :|| p) dom
                                ( Internal a
                                , Internal b
                                , Internal c
                                , Internal d
                                , Internal e
                                , Internal f
                                , Internal g
                                , Internal h
                                )
                            , InjectC (Select :|| p) dom (Internal a)
                            , InjectC (Select :|| p) dom (Internal b)
                            , InjectC (Select :|| p) dom (Internal c)
                            , InjectC (Select :|| p) dom (Internal d)
                            , InjectC (Select :|| p) dom (Internal e)
                            , InjectC (Select :|| p) dom (Internal f)
                            , InjectC (Select :|| p) dom (Internal g)
                            , InjectC (Select :|| p) dom (Internal h)
                            ) => Syntactic (a,b,c,d,e,f,g,h) #-}
    {-# INLINABLE desugar #-}
    {-# INLINABLE sugar #-}
    type Domain (a,b,c,d,e,f,g,h) = Domain a
    type Internal (a,b,c,d,e,f,g,h) =
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        , Internal h
        )

    desugar = uncurryN $ sugarSymC' Tup8
    sugar a =
        ( sugarSymC' Sel1 a
        , sugarSymC' Sel2 a
        , sugarSymC' Sel3 a
        , sugarSymC' Sel4 a
        , sugarSymC' Sel5 a
        , sugarSymC' Sel6 a
        , sugarSymC' Sel7 a
        , sugarSymC' Sel8 a
        )


instance
    ( Syntactic a, Domain a ~ dom
    , Syntactic b, Domain b ~ dom
    , Syntactic c, Domain c ~ dom
    , Syntactic d, Domain d ~ dom
    , Syntactic e, Domain e ~ dom
    , Syntactic f, Domain f ~ dom
    , Syntactic g, Domain g ~ dom
    , Syntactic h, Domain h ~ dom
    , Syntactic i, Domain i ~ dom
    , TupleSat dom p
    , p ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        , Internal h
        , Internal i
        )
    , p (Internal a)
    , p (Internal b)
    , p (Internal c)
    , p (Internal d)
    , p (Internal e)
    , p (Internal f)
    , p (Internal g)
    , p (Internal h)
    , p (Internal i)
    , InjectC (Tuple :|| p) dom
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        , Internal h
        , Internal i
        )
    , InjectC (Select :|| p) dom (Internal a)
    , InjectC (Select :|| p) dom (Internal b)
    , InjectC (Select :|| p) dom (Internal c)
    , InjectC (Select :|| p) dom (Internal d)
    , InjectC (Select :|| p) dom (Internal e)
    , InjectC (Select :|| p) dom (Internal f)
    , InjectC (Select :|| p) dom (Internal g)
    , InjectC (Select :|| p) dom (Internal h)
    , InjectC (Select :|| p) dom (Internal i)
    ) =>
      Syntactic (a,b,c,d,e,f,g,h,i)
  where
    {-# SPECIALIZE instance ( Syntactic a, Domain a ~ dom
                            , Syntactic b, Domain b ~ dom
                            , Syntactic c, Domain c ~ dom
                            , Syntactic d, Domain d ~ dom
                            , Syntactic e, Domain e ~ dom
                            , Syntactic f, Domain f ~ dom
                            , Syntactic g, Domain g ~ dom
                            , Syntactic h, Domain h ~ dom
                            , Syntactic i, Domain i ~ dom
                            , TupleSat dom p
                            , p ( Internal a
                                , Internal b
                                , Internal c
                                , Internal d
                                , Internal e
                                , Internal f
                                , Internal g
                                , Internal h
                                , Internal i
                                )
                            , p (Internal a)
                            , p (Internal b)
                            , p (Internal c)
                            , p (Internal d)
                            , p (Internal e)
                            , p (Internal f)
                            , p (Internal g)
                            , p (Internal h)
                            , p (Internal i)
                            , InjectC (Tuple :|| p) dom
                                ( Internal a
                                , Internal b
                                , Internal c
                                , Internal d
                                , Internal e
                                , Internal f
                                , Internal g
                                , Internal h
                                , Internal i
                                )
                            , InjectC (Select :|| p) dom (Internal a)
                            , InjectC (Select :|| p) dom (Internal b)
                            , InjectC (Select :|| p) dom (Internal c)
                            , InjectC (Select :|| p) dom (Internal d)
                            , InjectC (Select :|| p) dom (Internal e)
                            , InjectC (Select :|| p) dom (Internal f)
                            , InjectC (Select :|| p) dom (Internal g)
                            , InjectC (Select :|| p) dom (Internal h)
                            , InjectC (Select :|| p) dom (Internal i)
                            ) => Syntactic (a,b,c,d,e,f,g,h,i) #-}
    {-# INLINABLE desugar #-}
    {-# INLINABLE sugar #-}
    type Domain (a,b,c,d,e,f,g,h,i) = Domain a
    type Internal (a,b,c,d,e,f,g,h,i) =
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        , Internal h
        , Internal i
        )

    desugar = uncurryN $ sugarSymC' Tup9
    sugar a =
        ( sugarSymC' Sel1 a
        , sugarSymC' Sel2 a
        , sugarSymC' Sel3 a
        , sugarSymC' Sel4 a
        , sugarSymC' Sel5 a
        , sugarSymC' Sel6 a
        , sugarSymC' Sel7 a
        , sugarSymC' Sel8 a
        , sugarSymC' Sel9 a
        )


instance
    ( Syntactic a, Domain a ~ dom
    , Syntactic b, Domain b ~ dom
    , Syntactic c, Domain c ~ dom
    , Syntactic d, Domain d ~ dom
    , Syntactic e, Domain e ~ dom
    , Syntactic f, Domain f ~ dom
    , Syntactic g, Domain g ~ dom
    , Syntactic h, Domain h ~ dom
    , Syntactic i, Domain i ~ dom
    , Syntactic j, Domain j ~ dom
    , TupleSat dom p
    , p ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        , Internal h
        , Internal i
        , Internal j
        )
    , p (Internal a)
    , p (Internal b)
    , p (Internal c)
    , p (Internal d)
    , p (Internal e)
    , p (Internal f)
    , p (Internal g)
    , p (Internal h)
    , p (Internal i)
    , p (Internal j)
    , InjectC (Tuple :|| p) dom
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        , Internal h
        , Internal i
        , Internal j
        )
    , InjectC (Select :|| p) dom (Internal a)
    , InjectC (Select :|| p) dom (Internal b)
    , InjectC (Select :|| p) dom (Internal c)
    , InjectC (Select :|| p) dom (Internal d)
    , InjectC (Select :|| p) dom (Internal e)
    , InjectC (Select :|| p) dom (Internal f)
    , InjectC (Select :|| p) dom (Internal g)
    , InjectC (Select :|| p) dom (Internal h)
    , InjectC (Select :|| p) dom (Internal i)
    , InjectC (Select :|| p) dom (Internal j)
    ) =>
      Syntactic (a,b,c,d,e,f,g,h,i,j)
  where
    {-# SPECIALIZE instance ( Syntactic a, Domain a ~ dom
                            , Syntactic b, Domain b ~ dom
                            , Syntactic c, Domain c ~ dom
                            , Syntactic d, Domain d ~ dom
                            , Syntactic e, Domain e ~ dom
                            , Syntactic f, Domain f ~ dom
                            , Syntactic g, Domain g ~ dom
                            , Syntactic h, Domain h ~ dom
                            , Syntactic i, Domain i ~ dom
                            , Syntactic j, Domain j ~ dom
                            , TupleSat dom p
                            , p ( Internal a
                                , Internal b
                                , Internal c
                                , Internal d
                                , Internal e
                                , Internal f
                                , Internal g
                                , Internal h
                                , Internal i
                                , Internal j
                                )
                            , p (Internal a)
                            , p (Internal b)
                            , p (Internal c)
                            , p (Internal d)
                            , p (Internal e)
                            , p (Internal f)
                            , p (Internal g)
                            , p (Internal h)
                            , p (Internal i)
                            , p (Internal j)
                            , InjectC (Tuple :|| p) dom
                                ( Internal a
                                , Internal b
                                , Internal c
                                , Internal d
                                , Internal e
                                , Internal f
                                , Internal g
                                , Internal h
                                , Internal i
                                , Internal j
                                )
                            , InjectC (Select :|| p) dom (Internal a)
                            , InjectC (Select :|| p) dom (Internal b)
                            , InjectC (Select :|| p) dom (Internal c)
                            , InjectC (Select :|| p) dom (Internal d)
                            , InjectC (Select :|| p) dom (Internal e)
                            , InjectC (Select :|| p) dom (Internal f)
                            , InjectC (Select :|| p) dom (Internal g)
                            , InjectC (Select :|| p) dom (Internal h)
                            , InjectC (Select :|| p) dom (Internal i)
                            , InjectC (Select :|| p) dom (Internal j)
                            ) => Syntactic (a,b,c,d,e,f,g,h,i,j) #-}
    {-# INLINABLE desugar #-}
    {-# INLINABLE sugar #-}
    type Domain (a,b,c,d,e,f,g,h,i,j) = Domain a
    type Internal (a,b,c,d,e,f,g,h,i,j) =
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        , Internal h
        , Internal i
        , Internal j
        )

    desugar = uncurryN $ sugarSymC' Tup10
    sugar a =
        ( sugarSymC' Sel1 a
        , sugarSymC' Sel2 a
        , sugarSymC' Sel3 a
        , sugarSymC' Sel4 a
        , sugarSymC' Sel5 a
        , sugarSymC' Sel6 a
        , sugarSymC' Sel7 a
        , sugarSymC' Sel8 a
        , sugarSymC' Sel9 a
        , sugarSymC' Sel10 a
        )


instance
    ( Syntactic a, Domain a ~ dom
    , Syntactic b, Domain b ~ dom
    , Syntactic c, Domain c ~ dom
    , Syntactic d, Domain d ~ dom
    , Syntactic e, Domain e ~ dom
    , Syntactic f, Domain f ~ dom
    , Syntactic g, Domain g ~ dom
    , Syntactic h, Domain h ~ dom
    , Syntactic i, Domain i ~ dom
    , Syntactic j, Domain j ~ dom
    , Syntactic k, Domain k ~ dom
    , TupleSat dom p
    , p ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        , Internal h
        , Internal i
        , Internal j
        , Internal k
        )
    , p (Internal a)
    , p (Internal b)
    , p (Internal c)
    , p (Internal d)
    , p (Internal e)
    , p (Internal f)
    , p (Internal g)
    , p (Internal h)
    , p (Internal i)
    , p (Internal j)
    , p (Internal k)
    , InjectC (Tuple :|| p) dom
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        , Internal h
        , Internal i
        , Internal j
        , Internal k
        )
    , InjectC (Select :|| p) dom (Internal a)
    , InjectC (Select :|| p) dom (Internal b)
    , InjectC (Select :|| p) dom (Internal c)
    , InjectC (Select :|| p) dom (Internal d)
    , InjectC (Select :|| p) dom (Internal e)
    , InjectC (Select :|| p) dom (Internal f)
    , InjectC (Select :|| p) dom (Internal g)
    , InjectC (Select :|| p) dom (Internal h)
    , InjectC (Select :|| p) dom (Internal i)
    , InjectC (Select :|| p) dom (Internal j)
    , InjectC (Select :|| p) dom (Internal k)
    ) =>
      Syntactic (a,b,c,d,e,f,g,h,i,j,k)
  where
    {-# SPECIALIZE instance ( Syntactic a, Domain a ~ dom
                            , Syntactic b, Domain b ~ dom
                            , Syntactic c, Domain c ~ dom
                            , Syntactic d, Domain d ~ dom
                            , Syntactic e, Domain e ~ dom
                            , Syntactic f, Domain f ~ dom
                            , Syntactic g, Domain g ~ dom
                            , Syntactic h, Domain h ~ dom
                            , Syntactic i, Domain i ~ dom
                            , Syntactic j, Domain j ~ dom
                            , Syntactic k, Domain k ~ dom
                            , TupleSat dom p
                            , p ( Internal a
                                , Internal b
                                , Internal c
                                , Internal d
                                , Internal e
                                , Internal f
                                , Internal g
                                , Internal h
                                , Internal i
                                , Internal j
                                , Internal k
                                )
                            , p (Internal a)
                            , p (Internal b)
                            , p (Internal c)
                            , p (Internal d)
                            , p (Internal e)
                            , p (Internal f)
                            , p (Internal g)
                            , p (Internal h)
                            , p (Internal i)
                            , p (Internal j)
                            , p (Internal k)
                            , InjectC (Tuple :|| p) dom
                                ( Internal a
                                , Internal b
                                , Internal c
                                , Internal d
                                , Internal e
                                , Internal f
                                , Internal g
                                , Internal h
                                , Internal i
                                , Internal j
                                , Internal k
                                )
                            , InjectC (Select :|| p) dom (Internal a)
                            , InjectC (Select :|| p) dom (Internal b)
                            , InjectC (Select :|| p) dom (Internal c)
                            , InjectC (Select :|| p) dom (Internal d)
                            , InjectC (Select :|| p) dom (Internal e)
                            , InjectC (Select :|| p) dom (Internal f)
                            , InjectC (Select :|| p) dom (Internal g)
                            , InjectC (Select :|| p) dom (Internal h)
                            , InjectC (Select :|| p) dom (Internal i)
                            , InjectC (Select :|| p) dom (Internal j)
                            , InjectC (Select :|| p) dom (Internal k)
                            ) => Syntactic (a,b,c,d,e,f,g,h,i,j,k) #-}
    {-# INLINABLE desugar #-}
    {-# INLINABLE sugar #-}
    type Domain (a,b,c,d,e,f,g,h,i,j,k) = Domain a
    type Internal (a,b,c,d,e,f,g,h,i,j,k) =
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        , Internal h
        , Internal i
        , Internal j
        , Internal k
        )

    desugar = uncurryN $ sugarSymC' Tup11
    sugar a =
        ( sugarSymC' Sel1 a
        , sugarSymC' Sel2 a
        , sugarSymC' Sel3 a
        , sugarSymC' Sel4 a
        , sugarSymC' Sel5 a
        , sugarSymC' Sel6 a
        , sugarSymC' Sel7 a
        , sugarSymC' Sel8 a
        , sugarSymC' Sel9 a
        , sugarSymC' Sel10 a
        , sugarSymC' Sel11 a
        )


instance
    ( Syntactic a, Domain a ~ dom
    , Syntactic b, Domain b ~ dom
    , Syntactic c, Domain c ~ dom
    , Syntactic d, Domain d ~ dom
    , Syntactic e, Domain e ~ dom
    , Syntactic f, Domain f ~ dom
    , Syntactic g, Domain g ~ dom
    , Syntactic h, Domain h ~ dom
    , Syntactic i, Domain i ~ dom
    , Syntactic j, Domain j ~ dom
    , Syntactic k, Domain k ~ dom
    , Syntactic l, Domain l ~ dom
    , TupleSat dom p
    , p ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        , Internal h
        , Internal i
        , Internal j
        , Internal k
        , Internal l
        )
    , p (Internal a)
    , p (Internal b)
    , p (Internal c)
    , p (Internal d)
    , p (Internal e)
    , p (Internal f)
    , p (Internal g)
    , p (Internal h)
    , p (Internal i)
    , p (Internal j)
    , p (Internal k)
    , p (Internal l)
    , InjectC (Tuple :|| p) dom
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        , Internal h
        , Internal i
        , Internal j
        , Internal k
        , Internal l
        )
    , InjectC (Select :|| p) dom (Internal a)
    , InjectC (Select :|| p) dom (Internal b)
    , InjectC (Select :|| p) dom (Internal c)
    , InjectC (Select :|| p) dom (Internal d)
    , InjectC (Select :|| p) dom (Internal e)
    , InjectC (Select :|| p) dom (Internal f)
    , InjectC (Select :|| p) dom (Internal g)
    , InjectC (Select :|| p) dom (Internal h)
    , InjectC (Select :|| p) dom (Internal i)
    , InjectC (Select :|| p) dom (Internal j)
    , InjectC (Select :|| p) dom (Internal k)
    , InjectC (Select :|| p) dom (Internal l)
    ) =>
      Syntactic (a,b,c,d,e,f,g,h,i,j,k,l)
  where
    {-# SPECIALIZE instance ( Syntactic a, Domain a ~ dom
                            , Syntactic b, Domain b ~ dom
                            , Syntactic c, Domain c ~ dom
                            , Syntactic d, Domain d ~ dom
                            , Syntactic e, Domain e ~ dom
                            , Syntactic f, Domain f ~ dom
                            , Syntactic g, Domain g ~ dom
                            , Syntactic h, Domain h ~ dom
                            , Syntactic i, Domain i ~ dom
                            , Syntactic j, Domain j ~ dom
                            , Syntactic k, Domain k ~ dom
                            , Syntactic l, Domain l ~ dom
                            , TupleSat dom p
                            , p ( Internal a
                                , Internal b
                                , Internal c
                                , Internal d
                                , Internal e
                                , Internal f
                                , Internal g
                                , Internal h
                                , Internal i
                                , Internal j
                                , Internal k
                                , Internal l
                                )
                            , p (Internal a)
                            , p (Internal b)
                            , p (Internal c)
                            , p (Internal d)
                            , p (Internal e)
                            , p (Internal f)
                            , p (Internal g)
                            , p (Internal h)
                            , p (Internal i)
                            , p (Internal j)
                            , p (Internal k)
                            , p (Internal l)
                            , InjectC (Tuple :|| p) dom
                                ( Internal a
                                , Internal b
                                , Internal c
                                , Internal d
                                , Internal e
                                , Internal f
                                , Internal g
                                , Internal h
                                , Internal i
                                , Internal j
                                , Internal k
                                , Internal l
                                )
                            , InjectC (Select :|| p) dom (Internal a)
                            , InjectC (Select :|| p) dom (Internal b)
                            , InjectC (Select :|| p) dom (Internal c)
                            , InjectC (Select :|| p) dom (Internal d)
                            , InjectC (Select :|| p) dom (Internal e)
                            , InjectC (Select :|| p) dom (Internal f)
                            , InjectC (Select :|| p) dom (Internal g)
                            , InjectC (Select :|| p) dom (Internal h)
                            , InjectC (Select :|| p) dom (Internal i)
                            , InjectC (Select :|| p) dom (Internal j)
                            , InjectC (Select :|| p) dom (Internal k)
                            , InjectC (Select :|| p) dom (Internal l)
                            ) => Syntactic (a,b,c,d,e,f,g,h,i,j,k,l) #-}
    {-# INLINABLE desugar #-}
    {-# INLINABLE sugar #-}
    type Domain (a,b,c,d,e,f,g,h,i,j,k,l) = Domain a
    type Internal (a,b,c,d,e,f,g,h,i,j,k,l) =
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        , Internal h
        , Internal i
        , Internal j
        , Internal k
        , Internal l
        )

    desugar = uncurryN $ sugarSymC' Tup12
    sugar a =
        ( sugarSymC' Sel1 a
        , sugarSymC' Sel2 a
        , sugarSymC' Sel3 a
        , sugarSymC' Sel4 a
        , sugarSymC' Sel5 a
        , sugarSymC' Sel6 a
        , sugarSymC' Sel7 a
        , sugarSymC' Sel8 a
        , sugarSymC' Sel9 a
        , sugarSymC' Sel10 a
        , sugarSymC' Sel11 a
        , sugarSymC' Sel12 a
        )


instance
    ( Syntactic a, Domain a ~ dom
    , Syntactic b, Domain b ~ dom
    , Syntactic c, Domain c ~ dom
    , Syntactic d, Domain d ~ dom
    , Syntactic e, Domain e ~ dom
    , Syntactic f, Domain f ~ dom
    , Syntactic g, Domain g ~ dom
    , Syntactic h, Domain h ~ dom
    , Syntactic i, Domain i ~ dom
    , Syntactic j, Domain j ~ dom
    , Syntactic k, Domain k ~ dom
    , Syntactic l, Domain l ~ dom
    , Syntactic m, Domain m ~ dom
    , TupleSat dom p
    , p ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        , Internal h
        , Internal i
        , Internal j
        , Internal k
        , Internal l
        , Internal m
        )
    , p (Internal a)
    , p (Internal b)
    , p (Internal c)
    , p (Internal d)
    , p (Internal e)
    , p (Internal f)
    , p (Internal g)
    , p (Internal h)
    , p (Internal i)
    , p (Internal j)
    , p (Internal k)
    , p (Internal l)
    , p (Internal m)
    , InjectC (Tuple :|| p) dom
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        , Internal h
        , Internal i
        , Internal j
        , Internal k
        , Internal l
        , Internal m
        )
    , InjectC (Select :|| p) dom (Internal a)
    , InjectC (Select :|| p) dom (Internal b)
    , InjectC (Select :|| p) dom (Internal c)
    , InjectC (Select :|| p) dom (Internal d)
    , InjectC (Select :|| p) dom (Internal e)
    , InjectC (Select :|| p) dom (Internal f)
    , InjectC (Select :|| p) dom (Internal g)
    , InjectC (Select :|| p) dom (Internal h)
    , InjectC (Select :|| p) dom (Internal i)
    , InjectC (Select :|| p) dom (Internal j)
    , InjectC (Select :|| p) dom (Internal k)
    , InjectC (Select :|| p) dom (Internal l)
    , InjectC (Select :|| p) dom (Internal m)
    ) =>
      Syntactic (a,b,c,d,e,f,g,h,i,j,k,l,m)
  where
    {-# SPECIALIZE instance ( Syntactic a, Domain a ~ dom
                            , Syntactic b, Domain b ~ dom
                            , Syntactic c, Domain c ~ dom
                            , Syntactic d, Domain d ~ dom
                            , Syntactic e, Domain e ~ dom
                            , Syntactic f, Domain f ~ dom
                            , Syntactic g, Domain g ~ dom
                            , Syntactic h, Domain h ~ dom
                            , Syntactic i, Domain i ~ dom
                            , Syntactic j, Domain j ~ dom
                            , Syntactic k, Domain k ~ dom
                            , Syntactic l, Domain l ~ dom
                            , Syntactic m, Domain m ~ dom
                            , TupleSat dom p
                            , p ( Internal a
                                , Internal b
                                , Internal c
                                , Internal d
                                , Internal e
                                , Internal f
                                , Internal g
                                , Internal h
                                , Internal i
                                , Internal j
                                , Internal k
                                , Internal l
                                , Internal m
                                )
                            , p (Internal a)
                            , p (Internal b)
                            , p (Internal c)
                            , p (Internal d)
                            , p (Internal e)
                            , p (Internal f)
                            , p (Internal g)
                            , p (Internal h)
                            , p (Internal i)
                            , p (Internal j)
                            , p (Internal k)
                            , p (Internal l)
                            , p (Internal m)
                            , InjectC (Tuple :|| p) dom
                                ( Internal a
                                , Internal b
                                , Internal c
                                , Internal d
                                , Internal e
                                , Internal f
                                , Internal g
                                , Internal h
                                , Internal i
                                , Internal j
                                , Internal k
                                , Internal l
                                , Internal m
                                )
                            , InjectC (Select :|| p) dom (Internal a)
                            , InjectC (Select :|| p) dom (Internal b)
                            , InjectC (Select :|| p) dom (Internal c)
                            , InjectC (Select :|| p) dom (Internal d)
                            , InjectC (Select :|| p) dom (Internal e)
                            , InjectC (Select :|| p) dom (Internal f)
                            , InjectC (Select :|| p) dom (Internal g)
                            , InjectC (Select :|| p) dom (Internal h)
                            , InjectC (Select :|| p) dom (Internal i)
                            , InjectC (Select :|| p) dom (Internal j)
                            , InjectC (Select :|| p) dom (Internal k)
                            , InjectC (Select :|| p) dom (Internal l)
                            , InjectC (Select :|| p) dom (Internal m)
                            ) => Syntactic (a,b,c,d,e,f,g,h,i,j,k,l,m) #-}
    {-# INLINABLE desugar #-}
    {-# INLINABLE sugar #-}
    type Domain (a,b,c,d,e,f,g,h,i,j,k,l,m) = Domain a
    type Internal (a,b,c,d,e,f,g,h,i,j,k,l,m) =
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        , Internal h
        , Internal i
        , Internal j
        , Internal k
        , Internal l
        , Internal m
        )

    desugar = uncurryN $ sugarSymC' Tup13
    sugar a =
        ( sugarSymC' Sel1 a
        , sugarSymC' Sel2 a
        , sugarSymC' Sel3 a
        , sugarSymC' Sel4 a
        , sugarSymC' Sel5 a
        , sugarSymC' Sel6 a
        , sugarSymC' Sel7 a
        , sugarSymC' Sel8 a
        , sugarSymC' Sel9 a
        , sugarSymC' Sel10 a
        , sugarSymC' Sel11 a
        , sugarSymC' Sel12 a
        , sugarSymC' Sel13 a
        )


instance
    ( Syntactic a, Domain a ~ dom
    , Syntactic b, Domain b ~ dom
    , Syntactic c, Domain c ~ dom
    , Syntactic d, Domain d ~ dom
    , Syntactic e, Domain e ~ dom
    , Syntactic f, Domain f ~ dom
    , Syntactic g, Domain g ~ dom
    , Syntactic h, Domain h ~ dom
    , Syntactic i, Domain i ~ dom
    , Syntactic j, Domain j ~ dom
    , Syntactic k, Domain k ~ dom
    , Syntactic l, Domain l ~ dom
    , Syntactic m, Domain m ~ dom
    , Syntactic n, Domain n ~ dom
    , TupleSat dom p
    , p ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        , Internal h
        , Internal i
        , Internal j
        , Internal k
        , Internal l
        , Internal m
        , Internal n
        )
    , p (Internal a)
    , p (Internal b)
    , p (Internal c)
    , p (Internal d)
    , p (Internal e)
    , p (Internal f)
    , p (Internal g)
    , p (Internal h)
    , p (Internal i)
    , p (Internal j)
    , p (Internal k)
    , p (Internal l)
    , p (Internal m)
    , p (Internal n)
    , InjectC (Tuple :|| p) dom
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        , Internal h
        , Internal i
        , Internal j
        , Internal k
        , Internal l
        , Internal m
        , Internal n
        )
    , InjectC (Select :|| p) dom (Internal a)
    , InjectC (Select :|| p) dom (Internal b)
    , InjectC (Select :|| p) dom (Internal c)
    , InjectC (Select :|| p) dom (Internal d)
    , InjectC (Select :|| p) dom (Internal e)
    , InjectC (Select :|| p) dom (Internal f)
    , InjectC (Select :|| p) dom (Internal g)
    , InjectC (Select :|| p) dom (Internal h)
    , InjectC (Select :|| p) dom (Internal i)
    , InjectC (Select :|| p) dom (Internal j)
    , InjectC (Select :|| p) dom (Internal k)
    , InjectC (Select :|| p) dom (Internal l)
    , InjectC (Select :|| p) dom (Internal m)
    , InjectC (Select :|| p) dom (Internal n)
    ) =>
      Syntactic (a,b,c,d,e,f,g,h,i,j,k,l,m,n)
  where
    {-# SPECIALIZE instance ( Syntactic a, Domain a ~ dom
                            , Syntactic b, Domain b ~ dom
                            , Syntactic c, Domain c ~ dom
                            , Syntactic d, Domain d ~ dom
                            , Syntactic e, Domain e ~ dom
                            , Syntactic f, Domain f ~ dom
                            , Syntactic g, Domain g ~ dom
                            , Syntactic h, Domain h ~ dom
                            , Syntactic i, Domain i ~ dom
                            , Syntactic j, Domain j ~ dom
                            , Syntactic k, Domain k ~ dom
                            , Syntactic l, Domain l ~ dom
                            , Syntactic m, Domain m ~ dom
                            , Syntactic n, Domain n ~ dom
                            , TupleSat dom p
                            , p ( Internal a
                                , Internal b
                                , Internal c
                                , Internal d
                                , Internal e
                                , Internal f
                                , Internal g
                                , Internal h
                                , Internal i
                                , Internal j
                                , Internal k
                                , Internal l
                                , Internal m
                                , Internal n
                                )
                            , p (Internal a)
                            , p (Internal b)
                            , p (Internal c)
                            , p (Internal d)
                            , p (Internal e)
                            , p (Internal f)
                            , p (Internal g)
                            , p (Internal h)
                            , p (Internal i)
                            , p (Internal j)
                            , p (Internal k)
                            , p (Internal l)
                            , p (Internal m)
                            , p (Internal n)
                            , InjectC (Tuple :|| p) dom
                                ( Internal a
                                , Internal b
                                , Internal c
                                , Internal d
                                , Internal e
                                , Internal f
                                , Internal g
                                , Internal h
                                , Internal i
                                , Internal j
                                , Internal k
                                , Internal l
                                , Internal m
                                , Internal n
                                )
                            , InjectC (Select :|| p) dom (Internal a)
                            , InjectC (Select :|| p) dom (Internal b)
                            , InjectC (Select :|| p) dom (Internal c)
                            , InjectC (Select :|| p) dom (Internal d)
                            , InjectC (Select :|| p) dom (Internal e)
                            , InjectC (Select :|| p) dom (Internal f)
                            , InjectC (Select :|| p) dom (Internal g)
                            , InjectC (Select :|| p) dom (Internal h)
                            , InjectC (Select :|| p) dom (Internal i)
                            , InjectC (Select :|| p) dom (Internal j)
                            , InjectC (Select :|| p) dom (Internal k)
                            , InjectC (Select :|| p) dom (Internal l)
                            , InjectC (Select :|| p) dom (Internal m)
                            , InjectC (Select :|| p) dom (Internal n)
                            ) => Syntactic (a,b,c,d,e,f,g,h,i,j,k,l,m,n) #-}
    {-# INLINABLE desugar #-}
    {-# INLINABLE sugar #-}
    type Domain (a,b,c,d,e,f,g,h,i,j,k,l,m,n) = Domain a
    type Internal (a,b,c,d,e,f,g,h,i,j,k,l,m,n) =
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        , Internal h
        , Internal i
        , Internal j
        , Internal k
        , Internal l
        , Internal m
        , Internal n
        )

    desugar = uncurryN $ sugarSymC' Tup14
    sugar a =
        ( sugarSymC' Sel1 a
        , sugarSymC' Sel2 a
        , sugarSymC' Sel3 a
        , sugarSymC' Sel4 a
        , sugarSymC' Sel5 a
        , sugarSymC' Sel6 a
        , sugarSymC' Sel7 a
        , sugarSymC' Sel8 a
        , sugarSymC' Sel9 a
        , sugarSymC' Sel10 a
        , sugarSymC' Sel11 a
        , sugarSymC' Sel12 a
        , sugarSymC' Sel13 a
        , sugarSymC' Sel14 a
        )


instance
    ( Syntactic a, Domain a ~ dom
    , Syntactic b, Domain b ~ dom
    , Syntactic c, Domain c ~ dom
    , Syntactic d, Domain d ~ dom
    , Syntactic e, Domain e ~ dom
    , Syntactic f, Domain f ~ dom
    , Syntactic g, Domain g ~ dom
    , Syntactic h, Domain h ~ dom
    , Syntactic i, Domain i ~ dom
    , Syntactic j, Domain j ~ dom
    , Syntactic k, Domain k ~ dom
    , Syntactic l, Domain l ~ dom
    , Syntactic m, Domain m ~ dom
    , Syntactic n, Domain n ~ dom
    , Syntactic o, Domain o ~ dom
    , TupleSat dom p
    , p ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        , Internal h
        , Internal i
        , Internal j
        , Internal k
        , Internal l
        , Internal m
        , Internal n
        , Internal o
        )
    , p (Internal a)
    , p (Internal b)
    , p (Internal c)
    , p (Internal d)
    , p (Internal e)
    , p (Internal f)
    , p (Internal g)
    , p (Internal h)
    , p (Internal i)
    , p (Internal j)
    , p (Internal k)
    , p (Internal l)
    , p (Internal m)
    , p (Internal n)
    , p (Internal o)
    , InjectC (Tuple :|| p) dom
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        , Internal h
        , Internal i
        , Internal j
        , Internal k
        , Internal l
        , Internal m
        , Internal n
        , Internal o
        )
    , InjectC (Select :|| p) dom (Internal a)
    , InjectC (Select :|| p) dom (Internal b)
    , InjectC (Select :|| p) dom (Internal c)
    , InjectC (Select :|| p) dom (Internal d)
    , InjectC (Select :|| p) dom (Internal e)
    , InjectC (Select :|| p) dom (Internal f)
    , InjectC (Select :|| p) dom (Internal g)
    , InjectC (Select :|| p) dom (Internal h)
    , InjectC (Select :|| p) dom (Internal i)
    , InjectC (Select :|| p) dom (Internal j)
    , InjectC (Select :|| p) dom (Internal k)
    , InjectC (Select :|| p) dom (Internal l)
    , InjectC (Select :|| p) dom (Internal m)
    , InjectC (Select :|| p) dom (Internal n)
    , InjectC (Select :|| p) dom (Internal o)
    ) =>
      Syntactic (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o)
  where
    {-# SPECIALIZE instance ( Syntactic a, Domain a ~ dom
                            , Syntactic b, Domain b ~ dom
                            , Syntactic c, Domain c ~ dom
                            , Syntactic d, Domain d ~ dom
                            , Syntactic e, Domain e ~ dom
                            , Syntactic f, Domain f ~ dom
                            , Syntactic g, Domain g ~ dom
                            , Syntactic h, Domain h ~ dom
                            , Syntactic i, Domain i ~ dom
                            , Syntactic j, Domain j ~ dom
                            , Syntactic k, Domain k ~ dom
                            , Syntactic l, Domain l ~ dom
                            , Syntactic m, Domain m ~ dom
                            , Syntactic n, Domain n ~ dom
                            , Syntactic o, Domain o ~ dom
                            , TupleSat dom p
                            , p ( Internal a
                                , Internal b
                                , Internal c
                                , Internal d
                                , Internal e
                                , Internal f
                                , Internal g
                                , Internal h
                                , Internal i
                                , Internal j
                                , Internal k
                                , Internal l
                                , Internal m
                                , Internal n
                                , Internal o
                                )
                            , p (Internal a)
                            , p (Internal b)
                            , p (Internal c)
                            , p (Internal d)
                            , p (Internal e)
                            , p (Internal f)
                            , p (Internal g)
                            , p (Internal h)
                            , p (Internal i)
                            , p (Internal j)
                            , p (Internal k)
                            , p (Internal l)
                            , p (Internal m)
                            , p (Internal n)
                            , p (Internal o)
                            , InjectC (Tuple :|| p) dom
                                ( Internal a
                                , Internal b
                                , Internal c
                                , Internal d
                                , Internal e
                                , Internal f
                                , Internal g
                                , Internal h
                                , Internal i
                                , Internal j
                                , Internal k
                                , Internal l
                                , Internal m
                                , Internal n
                                , Internal o
                                )
                            , InjectC (Select :|| p) dom (Internal a)
                            , InjectC (Select :|| p) dom (Internal b)
                            , InjectC (Select :|| p) dom (Internal c)
                            , InjectC (Select :|| p) dom (Internal d)
                            , InjectC (Select :|| p) dom (Internal e)
                            , InjectC (Select :|| p) dom (Internal f)
                            , InjectC (Select :|| p) dom (Internal g)
                            , InjectC (Select :|| p) dom (Internal h)
                            , InjectC (Select :|| p) dom (Internal i)
                            , InjectC (Select :|| p) dom (Internal j)
                            , InjectC (Select :|| p) dom (Internal k)
                            , InjectC (Select :|| p) dom (Internal l)
                            , InjectC (Select :|| p) dom (Internal m)
                            , InjectC (Select :|| p) dom (Internal n)
                            , InjectC (Select :|| p) dom (Internal o)
                            ) => Syntactic (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) #-}
    {-# INLINABLE desugar #-}
    {-# INLINABLE sugar #-}
    type Domain (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) = Domain a
    type Internal (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) =
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        , Internal h
        , Internal i
        , Internal j
        , Internal k
        , Internal l
        , Internal m
        , Internal n
        , Internal o
        )

    desugar = uncurryN $ sugarSymC' Tup15
    sugar a =
        ( sugarSymC' Sel1 a
        , sugarSymC' Sel2 a
        , sugarSymC' Sel3 a
        , sugarSymC' Sel4 a
        , sugarSymC' Sel5 a
        , sugarSymC' Sel6 a
        , sugarSymC' Sel7 a
        , sugarSymC' Sel8 a
        , sugarSymC' Sel9 a
        , sugarSymC' Sel10 a
        , sugarSymC' Sel11 a
        , sugarSymC' Sel12 a
        , sugarSymC' Sel13 a
        , sugarSymC' Sel14 a
        , sugarSymC' Sel15 a
        )
