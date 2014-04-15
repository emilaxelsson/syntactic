-- | The basic parts of the syntactic library

module Data.Syntactic
    ( module Data.Syntactic.Syntax
    , module Data.Syntactic.Traversal
    , module Data.Syntactic.Constraint
    , module Data.Syntactic.Sugar
    , module Data.Syntactic.Interpretation.Equality
    , module Data.Syntactic.Interpretation.Render
    , module Data.Syntactic.Interpretation.Evaluation
    , module Data.Syntactic.Interpretation.Semantics
    , module Data.Syntactic.Decoration
    , module Data.Constraint
    ) where



import Data.Syntactic.Syntax
import Data.Syntactic.Traversal
import Data.Syntactic.Constraint
import Data.Syntactic.Sugar
import Data.Syntactic.Interpretation.Equality
import Data.Syntactic.Interpretation.Render
import Data.Syntactic.Interpretation.Evaluation
import Data.Syntactic.Interpretation.Semantics
import Data.Syntactic.Decoration

import Data.Constraint (Constraint, Dict (..))

