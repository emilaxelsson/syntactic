{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

-- | 'Syntactic' instances for tuples

module Language.Syntactic.Sugar.Tuple where



import Language.Syntactic
import Language.Syntactic.Functional.Tuple
import Language.Syntactic.Functional.Tuple.TH



instance
    ( Syntactic a
    , Syntactic b
    , Tuple :<: Domain a
    , Domain a ~ Domain b
    ) =>
      Syntactic (a,b)
  where
    type Domain (a,b)   = Domain a
    type Internal (a,b) = (Internal a, Internal b)
    desugar (a,b) = inj Pair :$ desugar a :$ desugar b
    sugar ab      = (sugar $ inj Fst :$ ab, sugar $ inj Snd :$ ab)

-- `desugar` and `sugar` can be seen as applying the eta-rule for pairs.
-- <https://mail.haskell.org/pipermail/haskell-cafe/2016-April/123639.html>

deriveSyntacticForTuples (const []) id [] 15

