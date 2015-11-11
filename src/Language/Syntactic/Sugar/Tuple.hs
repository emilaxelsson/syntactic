{-# LANGUAGE UndecidableInstances #-}

-- | 'Syntactic' instances for tuples

module Language.Syntactic.Sugar.Tuple where



import Language.Syntactic
import Language.Syntactic.Functional.Tuple



instance
    ( Syntactic a
    , Syntactic b
    , Domain a ~ Domain b
    , Tuple :<: Domain a
    ) =>
      Syntactic (a,b)
  where
    type Domain (a,b)   = Domain a
    type Internal (a,b) = (Internal a, Internal b)
    desugar (a,b) = sugarSym Tup2 a b
    sugar ab      = (sugarSym Sel1 ab, sugarSym Sel2 ab)

instance
    ( Syntactic a
    , Syntactic b
    , Syntactic c
    , Domain a ~ Domain b
    , Domain a ~ Domain c
    , Tuple :<: Domain a
    ) =>
      Syntactic (a,b,c)
  where
    type Domain (a,b,c)   = Domain a
    type Internal (a,b,c) = (Internal a, Internal b, Internal c)
    desugar (a,b,c) = sugarSym Tup3 a b c
    sugar abc       = (sugarSym Sel1 abc, sugarSym Sel2 abc, sugarSym Sel3 abc)

instance
    ( Syntactic a
    , Syntactic b
    , Syntactic c
    , Syntactic d
    , Domain a ~ Domain b
    , Domain a ~ Domain c
    , Domain a ~ Domain d
    , Tuple :<: Domain a
    ) =>
      Syntactic (a,b,c,d)
  where
    type Domain (a,b,c,d)   = Domain a
    type Internal (a,b,c,d) = (Internal a, Internal b, Internal c, Internal d)
    desugar (a,b,c,d) = sugarSym Tup4 a b c d
    sugar abcd        = (sugarSym Sel1 abcd, sugarSym Sel2 abcd, sugarSym Sel3 abcd, sugarSym Sel4 abcd)

