{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

-- | 'Syntactic' instances for tuples and 'Typed' symbol domains

module Language.Syntactic.Sugar.TupleTyped where



import Data.Typeable
import Language.Haskell.TH

import Data.Orphans ()

import Language.Syntactic
import Language.Syntactic.Functional.Tuple



deriveSyntacticForTuples
    (return . classPred ''Typeable . return)
    (AppT (ConT ''Typed))
    (\s -> AppE (ConE 'Typed) (AppE (VarE 'inj) s))
#if __GLASGOW_HASKELL__ < 708
    7
#else
    15
#endif

