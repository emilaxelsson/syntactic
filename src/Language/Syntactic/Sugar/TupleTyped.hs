{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

-- | 'Syntactic' instances for tuples and 'Typed' symbol domains

module Language.Syntactic.Sugar.TupleTyped where



import Data.Typeable
import Language.Haskell.TH

#if __GLASGOW_HASKELL__ < 710
import Data.Orphans ()
#endif

import Language.Syntactic
import Language.Syntactic.TH
import Language.Syntactic.Functional.Tuple
import Language.Syntactic.Functional.Tuple.TH



instance
    ( Syntactic a
    , Syntactic b
    , Typeable (Internal a)
    , Typeable (Internal b)
    , Tuple :<: sym
    , Domain a ~ Typed sym
    , Domain a ~ Domain b
    ) =>
      Syntactic (a,b)
  where
    type Domain (a,b)   = Domain a
    type Internal (a,b) = (Internal a, Internal b)
    desugar (a,b) = Sym (Typed $ inj Pair) :$ desugar a :$ desugar b
    sugar ab      = (sugar $ Sym (Typed $ inj Fst) :$ ab, sugar $ Sym (Typed $ inj Snd) :$ ab)

deriveSyntacticForTuples
    (return . classPred ''Typeable ConT . return)
    (AppT (ConT ''Typed))
    []
#if __GLASGOW_HASKELL__ < 708
    7
#else
    15
#endif

