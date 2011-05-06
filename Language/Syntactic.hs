-- | The syntactic library
--
-- The basic functionality is provided by the module
-- "Language.Syntactic.Syntax".

module Language.Syntactic
    ( module Language.Syntactic.Syntax
    , module Language.Syntactic.Analysis.Equality
    , module Language.Syntactic.Analysis.Render
    , module Language.Syntactic.Analysis.Evaluation
    , module Language.Syntactic.Analysis.Hash
    , module Language.Syntactic.Features.Literal
    , module Language.Syntactic.Features.PrimFunc
    , module Language.Syntactic.Features.Condition
    , module Language.Syntactic.Features.Tuple
    , module Language.Syntactic.Features.Annotate
    ) where



import Language.Syntactic.Syntax
import Language.Syntactic.Analysis.Equality
import Language.Syntactic.Analysis.Render
import Language.Syntactic.Analysis.Evaluation
import Language.Syntactic.Analysis.Hash
import Language.Syntactic.Features.Literal
import Language.Syntactic.Features.PrimFunc
import Language.Syntactic.Features.Condition
import Language.Syntactic.Features.Tuple
import Language.Syntactic.Features.Annotate

