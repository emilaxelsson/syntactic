{-# LANGUAGE UndecidableInstances #-}

-- | 'Syntactic' instances for tuples and 'Typed' symbol domains

module Language.Syntactic.Sugar.TupleT where



import Data.Typeable

import Language.Syntactic
import Language.Syntactic.Functional.Tuple



instance
    ( Syntactic a
    , Syntactic b
    , Typeable (Internal a)
    , Typeable (Internal b)
    , Domain a ~ Typed sym
    , Domain a ~ Domain b
    , Tuple :<: sym
    ) =>
      Syntactic (a,b)
  where
    type Domain (a,b)   = Domain a
    type Internal (a,b) = (Internal a, Internal b)
    desugar (a,b) = sugarSymT Tup2 a b
    sugar ab      = (sugarSymT Sel1 ab, sugarSymT Sel2 ab)

instance
    ( Syntactic a
    , Syntactic b
    , Syntactic c
    , Typeable (Internal a)
    , Typeable (Internal b)
    , Typeable (Internal c)
    , Domain a ~ Typed sym
    , Domain a ~ Domain b
    , Domain a ~ Domain c
    , Tuple :<: sym
    ) =>
      Syntactic (a,b,c)
  where
    type Domain (a,b,c)   = Domain a
    type Internal (a,b,c) = (Internal a, Internal b, Internal c)
    desugar (a,b,c) = sugarSymT Tup3 a b c
    sugar abc       = (sugarSymT Sel1 abc, sugarSymT Sel2 abc, sugarSymT Sel3 abc)

instance
    ( Syntactic a
    , Syntactic b
    , Syntactic c
    , Syntactic d
    , Typeable (Internal a)
    , Typeable (Internal b)
    , Typeable (Internal c)
    , Typeable (Internal d)
    , Domain a ~ Typed sym
    , Domain a ~ Domain b
    , Domain a ~ Domain c
    , Domain a ~ Domain d
    , Tuple :<: sym
    ) =>
      Syntactic (a,b,c,d)
  where
    type Domain (a,b,c,d)   = Domain a
    type Internal (a,b,c,d) = (Internal a, Internal b, Internal c, Internal d)
    desugar (a,b,c,d) = sugarSymT Tup4 a b c d
    sugar abcd        = (sugarSymT Sel1 abcd, sugarSymT Sel2 abcd, sugarSymT Sel3 abcd, sugarSymT Sel4 abcd)

