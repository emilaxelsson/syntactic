-- | The basic parts of the syntactic library

module Language.Syntactic
    ( module Data.PolyProxy
    , module Language.Syntactic.Syntax
    , module Language.Syntactic.Traversal
    , module Language.Syntactic.Constraint
    , module Language.Syntactic.Sugar
    , module Language.Syntactic.Interpretation.Equality
    , module Language.Syntactic.Interpretation.Render
    , module Language.Syntactic.Interpretation.Evaluation
    , module Language.Syntactic.Interpretation.Semantics
    , module Data.Constraint
    ) where



import Data.PolyProxy
import Language.Syntactic.Syntax
import Language.Syntactic.Traversal
import Language.Syntactic.Constraint
import Language.Syntactic.Sugar
import Language.Syntactic.Interpretation.Equality
import Language.Syntactic.Interpretation.Render
import Language.Syntactic.Interpretation.Evaluation
import Language.Syntactic.Interpretation.Semantics

import Data.Constraint (Constraint, Dict (..))

