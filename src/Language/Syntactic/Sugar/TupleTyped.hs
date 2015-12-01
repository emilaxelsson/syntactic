{-# LANGUAGE UndecidableInstances #-}

-- | 'Syntactic' instances for tuples and 'Typed' symbol domains

module Language.Syntactic.Sugar.TupleTyped where



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
    desugar (a,b) = sugarSymTyped Tup2 a b
    sugar ab      = (sugarSymTyped Sel1 ab, sugarSymTyped Sel2 ab)

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
    desugar (a,b,c) = sugarSymTyped Tup3 a b c
    sugar abc       = (sugarSymTyped Sel1 abc, sugarSymTyped Sel2 abc, sugarSymTyped Sel3 abc)

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
    desugar (a,b,c,d) = sugarSymTyped Tup4 a b c d
    sugar abcd        = (sugarSymTyped Sel1 abcd, sugarSymTyped Sel2 abcd, sugarSymTyped Sel3 abcd, sugarSymTyped Sel4 abcd)

