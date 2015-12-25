{-# LANGUAGE TemplateHaskell #-}

-- | Construction and elimination of tuples

module Language.Syntactic.Functional.Tuple
  ( module Language.Syntactic.Functional.Tuple
    -- * Template Haskell
  , eqPred
  , classPred
  , mkSelectClassPlusInstances
  , deriveSyntacticForTuples
  ) where



import Language.Syntactic
import Language.Syntactic.TH
import Language.Syntactic.Functional
import Language.Syntactic.Functional.Tuple.TH



--------------------------------------------------------------------------------
-- * Generic tuple projection
--------------------------------------------------------------------------------

mkSelectClassPlusInstances 15



--------------------------------------------------------------------------------
-- * Symbols
--------------------------------------------------------------------------------

-- | Construction and elimination of tuples
mkTupleSym "Tuple" "Tup" "Sel" 15

deriveSymbol    ''Tuple
deriveEquality  ''Tuple
deriveRender id ''Tuple

instance StringTree Tuple

instance Eval Tuple
  where
    evalSym Tup2  = (,)
    evalSym Tup3  = (,,)
    evalSym Tup4  = (,,,)
    evalSym Tup5  = (,,,,)
    evalSym Tup6  = (,,,,,)
    evalSym Tup7  = (,,,,,,)
    evalSym Tup8  = (,,,,,,,)
    evalSym Tup9  = (,,,,,,,,)
    evalSym Tup10 = (,,,,,,,,,)
    evalSym Tup11 = (,,,,,,,,,,)
    evalSym Tup12 = (,,,,,,,,,,,)
    evalSym Tup13 = (,,,,,,,,,,,,)
    evalSym Tup14 = (,,,,,,,,,,,,,)
    evalSym Tup15 = (,,,,,,,,,,,,,,)
    evalSym Sel1  = select1
    evalSym Sel2  = select2
    evalSym Sel3  = select3
    evalSym Sel4  = select4
    evalSym Sel5  = select5
    evalSym Sel6  = select6
    evalSym Sel7  = select7
    evalSym Sel8  = select8
    evalSym Sel9  = select9
    evalSym Sel10 = select10
    evalSym Sel11 = select11
    evalSym Sel12 = select12
    evalSym Sel13 = select13
    evalSym Sel14 = select14
    evalSym Sel15 = select15
  -- It would be possible to generate this instance, but the gain would be
  -- small, and it's very hard to get it wrong anyway.

instance EvalEnv Tuple env

