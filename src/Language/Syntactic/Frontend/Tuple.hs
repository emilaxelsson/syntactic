{-# LANGUAGE UndecidableInstances #-}

-- | 'Syntactic' instances for Haskell tuples

module Language.Syntactic.Frontend.Tuple where



import Language.Syntactic
import Language.Syntactic.Constructs.Tuple
import Data.Tuple.Curry



instance
    ( Syntactic a, Domain a ~ dom
    , Syntactic b, Domain b ~ dom
    , InjectC Tuple dom
        ( Internal a
        , Internal b
        )
    , InjectC Select dom (Internal a)
    , InjectC Select dom (Internal b)
    ) =>
      Syntactic (a,b)
  where
    type Domain (a,b) = Domain a
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
    ( Syntactic a, Domain a ~ dom
    , Syntactic b, Domain b ~ dom
    , Syntactic c, Domain c ~ dom
    , InjectC Tuple dom
        ( Internal a
        , Internal b
        , Internal c
        )
    , InjectC Select dom (Internal a)
    , InjectC Select dom (Internal b)
    , InjectC Select dom (Internal c)
    ) =>
      Syntactic (a,b,c)
  where
    type Domain (a,b,c) = Domain a
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
    ( Syntactic a, Domain a ~ dom
    , Syntactic b, Domain b ~ dom
    , Syntactic c, Domain c ~ dom
    , Syntactic d, Domain d ~ dom
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
      Syntactic (a,b,c,d)
  where
    type Domain (a,b,c,d) = Domain a
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
    ( Syntactic a, Domain a ~ dom
    , Syntactic b, Domain b ~ dom
    , Syntactic c, Domain c ~ dom
    , Syntactic d, Domain d ~ dom
    , Syntactic e, Domain e ~ dom
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
      Syntactic (a,b,c,d,e)
  where
    type Domain (a,b,c,d,e) = Domain a
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
    ( Syntactic a, Domain a ~ dom
    , Syntactic b, Domain b ~ dom
    , Syntactic c, Domain c ~ dom
    , Syntactic d, Domain d ~ dom
    , Syntactic e, Domain e ~ dom
    , Syntactic f, Domain f ~ dom
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
      Syntactic (a,b,c,d,e,f)
  where
    type Domain (a,b,c,d,e,f) = Domain a
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
    ( Syntactic a, Domain a ~ dom
    , Syntactic b, Domain b ~ dom
    , Syntactic c, Domain c ~ dom
    , Syntactic d, Domain d ~ dom
    , Syntactic e, Domain e ~ dom
    , Syntactic f, Domain f ~ dom
    , Syntactic g, Domain g ~ dom
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
      Syntactic (a,b,c,d,e,f,g)
  where
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

instance
    ( Syntactic a, Domain a ~ dom
    , Syntactic b, Domain b ~ dom
    , Syntactic c, Domain c ~ dom
    , Syntactic d, Domain d ~ dom
    , Syntactic e, Domain e ~ dom
    , Syntactic f, Domain f ~ dom
    , Syntactic g, Domain g ~ dom
    , Syntactic h, Domain h ~ dom
    , InjectC Tuple dom
        ( Internal a
        , Internal b
        , Internal c
        , Internal d
        , Internal e
        , Internal f
        , Internal g
        , Internal h
        )
    , InjectC Select dom (Internal a)
    , InjectC Select dom (Internal b)
    , InjectC Select dom (Internal c)
    , InjectC Select dom (Internal d)
    , InjectC Select dom (Internal e)
    , InjectC Select dom (Internal f)
    , InjectC Select dom (Internal g)
    , InjectC Select dom (Internal h)
    ) =>
      Syntactic (a,b,c,d,e,f,g,h)
  where
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

    desugar = uncurryN $ sugarSymC Tup8
    sugar a =
        ( sugarSymC Sel1 a
        , sugarSymC Sel2 a
        , sugarSymC Sel3 a
        , sugarSymC Sel4 a
        , sugarSymC Sel5 a
        , sugarSymC Sel6 a
        , sugarSymC Sel7 a
        , sugarSymC Sel8 a
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
    , InjectC Tuple dom
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
    , InjectC Select dom (Internal a)
    , InjectC Select dom (Internal b)
    , InjectC Select dom (Internal c)
    , InjectC Select dom (Internal d)
    , InjectC Select dom (Internal e)
    , InjectC Select dom (Internal f)
    , InjectC Select dom (Internal g)
    , InjectC Select dom (Internal h)
    , InjectC Select dom (Internal i)
    ) =>
      Syntactic (a,b,c,d,e,f,g,h,i)
  where
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

    desugar = uncurryN $ sugarSymC Tup9
    sugar a =
        ( sugarSymC Sel1 a
        , sugarSymC Sel2 a
        , sugarSymC Sel3 a
        , sugarSymC Sel4 a
        , sugarSymC Sel5 a
        , sugarSymC Sel6 a
        , sugarSymC Sel7 a
        , sugarSymC Sel8 a
        , sugarSymC Sel9 a
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
    , InjectC Tuple dom
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
    , InjectC Select dom (Internal a)
    , InjectC Select dom (Internal b)
    , InjectC Select dom (Internal c)
    , InjectC Select dom (Internal d)
    , InjectC Select dom (Internal e)
    , InjectC Select dom (Internal f)
    , InjectC Select dom (Internal g)
    , InjectC Select dom (Internal h)
    , InjectC Select dom (Internal i)
    , InjectC Select dom (Internal j)
    ) =>
      Syntactic (a,b,c,d,e,f,g,h,i,j)
  where
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

    desugar = uncurryN $ sugarSymC Tup10
    sugar a =
        ( sugarSymC Sel1 a
        , sugarSymC Sel2 a
        , sugarSymC Sel3 a
        , sugarSymC Sel4 a
        , sugarSymC Sel5 a
        , sugarSymC Sel6 a
        , sugarSymC Sel7 a
        , sugarSymC Sel8 a
        , sugarSymC Sel9 a
        , sugarSymC Sel10 a
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
    , InjectC Tuple dom
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
    , InjectC Select dom (Internal a)
    , InjectC Select dom (Internal b)
    , InjectC Select dom (Internal c)
    , InjectC Select dom (Internal d)
    , InjectC Select dom (Internal e)
    , InjectC Select dom (Internal f)
    , InjectC Select dom (Internal g)
    , InjectC Select dom (Internal h)
    , InjectC Select dom (Internal i)
    , InjectC Select dom (Internal j)
    , InjectC Select dom (Internal k)
    ) =>
      Syntactic (a,b,c,d,e,f,g,h,i,j,k)
  where
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

    desugar = uncurryN $ sugarSymC Tup11
    sugar a =
        ( sugarSymC Sel1 a
        , sugarSymC Sel2 a
        , sugarSymC Sel3 a
        , sugarSymC Sel4 a
        , sugarSymC Sel5 a
        , sugarSymC Sel6 a
        , sugarSymC Sel7 a
        , sugarSymC Sel8 a
        , sugarSymC Sel9 a
        , sugarSymC Sel10 a
        , sugarSymC Sel11 a
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
    , InjectC Tuple dom
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
    , InjectC Select dom (Internal a)
    , InjectC Select dom (Internal b)
    , InjectC Select dom (Internal c)
    , InjectC Select dom (Internal d)
    , InjectC Select dom (Internal e)
    , InjectC Select dom (Internal f)
    , InjectC Select dom (Internal g)
    , InjectC Select dom (Internal h)
    , InjectC Select dom (Internal i)
    , InjectC Select dom (Internal j)
    , InjectC Select dom (Internal k)
    , InjectC Select dom (Internal l)
    ) =>
      Syntactic (a,b,c,d,e,f,g,h,i,j,k,l)
  where
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

    desugar = uncurryN $ sugarSymC Tup12
    sugar a =
        ( sugarSymC Sel1 a
        , sugarSymC Sel2 a
        , sugarSymC Sel3 a
        , sugarSymC Sel4 a
        , sugarSymC Sel5 a
        , sugarSymC Sel6 a
        , sugarSymC Sel7 a
        , sugarSymC Sel8 a
        , sugarSymC Sel9 a
        , sugarSymC Sel10 a
        , sugarSymC Sel11 a
        , sugarSymC Sel12 a
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
    , InjectC Tuple dom
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
    , InjectC Select dom (Internal a)
    , InjectC Select dom (Internal b)
    , InjectC Select dom (Internal c)
    , InjectC Select dom (Internal d)
    , InjectC Select dom (Internal e)
    , InjectC Select dom (Internal f)
    , InjectC Select dom (Internal g)
    , InjectC Select dom (Internal h)
    , InjectC Select dom (Internal i)
    , InjectC Select dom (Internal j)
    , InjectC Select dom (Internal k)
    , InjectC Select dom (Internal l)
    , InjectC Select dom (Internal m)
    ) =>
      Syntactic (a,b,c,d,e,f,g,h,i,j,k,l,m)
  where
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

    desugar = uncurryN $ sugarSymC Tup13
    sugar a =
        ( sugarSymC Sel1 a
        , sugarSymC Sel2 a
        , sugarSymC Sel3 a
        , sugarSymC Sel4 a
        , sugarSymC Sel5 a
        , sugarSymC Sel6 a
        , sugarSymC Sel7 a
        , sugarSymC Sel8 a
        , sugarSymC Sel9 a
        , sugarSymC Sel10 a
        , sugarSymC Sel11 a
        , sugarSymC Sel12 a
        , sugarSymC Sel13 a
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
    , InjectC Tuple dom
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
    , InjectC Select dom (Internal a)
    , InjectC Select dom (Internal b)
    , InjectC Select dom (Internal c)
    , InjectC Select dom (Internal d)
    , InjectC Select dom (Internal e)
    , InjectC Select dom (Internal f)
    , InjectC Select dom (Internal g)
    , InjectC Select dom (Internal h)
    , InjectC Select dom (Internal i)
    , InjectC Select dom (Internal j)
    , InjectC Select dom (Internal k)
    , InjectC Select dom (Internal l)
    , InjectC Select dom (Internal m)
    , InjectC Select dom (Internal n)
    ) =>
      Syntactic (a,b,c,d,e,f,g,h,i,j,k,l,m,n)
  where
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

    desugar = uncurryN $ sugarSymC Tup14
    sugar a =
        ( sugarSymC Sel1 a
        , sugarSymC Sel2 a
        , sugarSymC Sel3 a
        , sugarSymC Sel4 a
        , sugarSymC Sel5 a
        , sugarSymC Sel6 a
        , sugarSymC Sel7 a
        , sugarSymC Sel8 a
        , sugarSymC Sel9 a
        , sugarSymC Sel10 a
        , sugarSymC Sel11 a
        , sugarSymC Sel12 a
        , sugarSymC Sel13 a
        , sugarSymC Sel14 a
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
    , InjectC Tuple dom
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
    , InjectC Select dom (Internal a)
    , InjectC Select dom (Internal b)
    , InjectC Select dom (Internal c)
    , InjectC Select dom (Internal d)
    , InjectC Select dom (Internal e)
    , InjectC Select dom (Internal f)
    , InjectC Select dom (Internal g)
    , InjectC Select dom (Internal h)
    , InjectC Select dom (Internal i)
    , InjectC Select dom (Internal j)
    , InjectC Select dom (Internal k)
    , InjectC Select dom (Internal l)
    , InjectC Select dom (Internal m)
    , InjectC Select dom (Internal n)
    , InjectC Select dom (Internal o)
    ) =>
      Syntactic (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o)
  where
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

    desugar = uncurryN $ sugarSymC Tup15
    sugar a =
        ( sugarSymC Sel1 a
        , sugarSymC Sel2 a
        , sugarSymC Sel3 a
        , sugarSymC Sel4 a
        , sugarSymC Sel5 a
        , sugarSymC Sel6 a
        , sugarSymC Sel7 a
        , sugarSymC Sel8 a
        , sugarSymC Sel9 a
        , sugarSymC Sel10 a
        , sugarSymC Sel11 a
        , sugarSymC Sel12 a
        , sugarSymC Sel13 a
        , sugarSymC Sel14 a
        , sugarSymC Sel15 a
        )
