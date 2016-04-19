{-# LANGUAGE TemplateHaskell #-}

-- | Construction and elimination of tuples

module Language.Syntactic.Functional.Tuple where



import Language.Syntactic
import Language.Syntactic.TH
import Language.Syntactic.Functional



data Tuple a
  where
    Pair :: Tuple (a :-> b :-> Full (a,b))
    Fst  :: Tuple ((a,b) :-> Full a)
    Snd  :: Tuple ((a,b) :-> Full b)

deriveSymbol    ''Tuple
deriveEquality  ''Tuple
deriveRender id ''Tuple

instance StringTree Tuple

instance Eval Tuple
  where
    evalSym Pair = (,)
    evalSym Fst  = fst
    evalSym Snd  = snd

instance EvalEnv Tuple env

