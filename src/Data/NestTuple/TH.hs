{-# LANGUAGE CPP #-}

module Data.NestTuple.TH where



import Language.Haskell.TH

import Language.Syntactic.TH



mkTupT :: [Type] -> Type
mkTupT ts = foldl AppT (TupleT (length ts)) ts

mkPairT :: Type -> Type -> Type
mkPairT a b = foldl AppT (TupleT 2) [a,b]

mkTupE :: [Exp] -> Exp
#if __GLASGOW_HASKELL__ >= 810
mkTupE = TupE . map Just
#else
mkTupE = TupE
#endif

mkPairE :: Exp -> Exp -> Exp
mkPairE a b = mkTupE [a,b]

mkPairP :: Pat -> Pat -> Pat
mkPairP a b = TupP [a,b]

data Nest a
    = Leaf a
    | Pair (Nest a) (Nest a)
  deriving (Eq, Show, Functor)

foldNest :: (a -> b) -> (b -> b -> b) -> Nest a -> b
foldNest leaf pair = go
  where
    go (Leaf a) = leaf a
    go (Pair a b) = pair (go a) (go b)

toNest :: [a] -> Nest a
toNest [a] = Leaf a
toNest as  = Pair (toNest bs) (toNest cs)
  where
    (bs,cs) = splitAt ((length as + 1) `div` 2) as



-- Make instances of the form
--
-- > instance Nestable (a,...,x)
-- >   where
-- >     type Nested (a,...,x) = (a ... x)  -- nested pairs
-- >     nest   (a,...,x) = (a ... x)
-- >     unnest (a ... x) = (a,...,x)
mkNestableInstances
    :: Int  -- ^ Max tuple width
    -> DecsQ
mkNestableInstances n = return $ map nestableInstance [2..n]
  where
    nestableInstance w = instD
        []
        (AppT (ConT (mkName "Nestable")) tupT)
        [ tySynInst (mkName "Nested") [tupT] (foldNest VarT mkPairT $ toNest vars)
        , FunD (mkName "nest")
            [ Clause
                [TupP (map VarP vars)]
                (NormalB (foldNest VarE mkPairE $ toNest vars))
                []
            ]
        , FunD (mkName "unnest")
            [ Clause
                [foldNest VarP mkPairP $ toNest vars]
                (NormalB (mkTupE (map VarE vars)))
                []
            ]
        ]
      where
        vars = take w varSupply
        tupT = mkTupT $ map VarT vars

