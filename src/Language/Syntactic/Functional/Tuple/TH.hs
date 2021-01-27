{-# LANGUAGE TemplateHaskell #-}

-- | Generate 'Syntactic' instances for tuples

module Language.Syntactic.Functional.Tuple.TH
  ( deriveSyntacticForTuples
  ) where



import Language.Haskell.TH

import Data.NestTuple
import Data.NestTuple.TH

import Language.Syntactic ((:<:), Syntactic (..))
import Language.Syntactic.TH



-- Make instances of the form
--
-- > instance
-- >     ( Syntactic a
-- >     , ...
-- >     , Syntactic x
-- >
-- >     , internalPred (Internal a)
-- >     , ...
-- >     , internalPred (Internal x)
-- >
-- >     , Tuple :<: sym
-- >     , Domain a ~ mkDomain sym
-- >
-- >     , Domain a ~ Domain b
-- >     , ...
-- >     , Domain a ~ Domain x
-- >     , extraConstraint
-- >     ) =>
-- >       Syntactic (a,...,x)
-- >   where
-- >     type Domain (a,...,x)   = Domain a
-- >     type Internal (a,...,x) = (Internal a ... Internal x)  -- nested pairs
-- >     desugar = desugar . nestTup  -- use pair instance
-- >     sugar   = unnestTup . sugar  -- use pair instance
--
-- Instances will be generated for width 3 and upwards. The existence of an
-- instance for pairs is assumed.
deriveSyntacticForTuples
    :: (Type -> Cxt)   -- ^ @internalPred@ (see above)
    -> (Type -> Type)  -- ^ @mkDomain@ (see above)
    -> Cxt             -- ^ @extraConstraint@ (see above)
    -> Int             -- ^ Max tuple width
    -> DecsQ
deriveSyntacticForTuples internalPred mkDomain extraConstraint n = return $
    map deriveSyntacticForTuple [3..n]
  where
    deriveSyntacticForTuple w = instD
        ( concat
            [ map (classPred ''Syntactic ConT . return) varsT
            , concatMap internalPred $ map (AppT (ConT ''Internal)) varsT
            , [classPred ''(:<:) ConT [ConT (mkName "Tuple"), VarT (mkName "sym")]]
            , [eqPred domainA (mkDomain (VarT (mkName "sym")))]
            , [eqPred domainA (AppT (ConT ''Domain) b)
                | b <- tail varsT
              ]
            , extraConstraint
            ]
        )
        (AppT (ConT ''Syntactic) tupT)
        [ tySynInst ''Domain tupT domainA
        , tySynInst ''Internal tupT tupTI
        , FunD 'desugar
            [ Clause
                []
                (NormalB (foldl AppE (VarE '(.)) $ map VarE [mkName "desugar", 'nest]))
                []
            ]
        , FunD 'sugar
            [ Clause
                []
                (NormalB (foldl AppE (VarE '(.)) $ map VarE ['unnest, mkName "sugar"]))
                []
            ]
        ]
      where
        varsT   = map VarT $ take w varSupply
        tupT    = foldl AppT (TupleT w) varsT
        tupTI   = foldNest id mkPairT $ toNest $ map (AppT (ConT ''Internal)) varsT
        domainA = AppT (ConT ''Domain) (VarT (mkName "a"))

