{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

-- | 'Syntactic' instances for tuples

module Language.Syntactic.Sugar.Tuple where



import Language.Haskell.TH

import Language.Syntactic
import Language.Syntactic.Functional.Tuple
import Language.Syntactic.Functional.Tuple.TH



deriveSyntacticForTuples (const []) id (AppE (VarE 'inj)) 15

