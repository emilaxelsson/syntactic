{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Generate types, classes and instances for tuples

module Language.Syntactic.Functional.Tuple.TH where



import Data.Generics
import Language.Haskell.TH

import Language.Syntactic ((:->), Full, AST (..), (:<:), Syntactic (..))
import Language.Syntactic.TH



-- | Portable method for constructing a 'Pred' of the form @(t1 ~ t2)@
eqPred :: Type -> Type -> Pred
#if MIN_VERSION_template_haskell(2,10,0)
eqPred t1 t2 = foldl1 AppT [EqualityT,t1,t2]
#else
eqPred = EqualP
#endif
  -- This function is just here to provide compatibility with
  -- template-haskell < 2.10

-- | Portable method for constructing a 'Pred' of the form @SomeClass t1 t2 ...@
classPred :: Name -> [Type] -> Pred
#if MIN_VERSION_template_haskell(2,10,0)
classPred cl = foldl AppT (ConT cl)
#else
classPred = ClassP
#endif
  -- This function is just here to provide compatibility with
  -- template-haskell < 2.10

tySynInst :: Name -> [Type] -> Type -> Dec
#if MIN_VERSION_template_haskell(2,9,0)
tySynInst t as rhs = TySynInstD t (TySynEqn as rhs)
#else
tySynInst = TySynInstD
#endif



--------------------------------------------------------------------------------
-- * Generic selection classes and instances
--------------------------------------------------------------------------------

class SelectX tup
  where
    type SelX tup
    selectX :: tup -> SelX tup
  -- Declare the class to be able to quote instances of it

classTemplate :: DecsQ
classTemplate =
  [d| class SelectX tup
        where
          type SelX tup
          selectX :: tup -> SelX tup
  |]

instanceTemplate :: DecsQ
instanceTemplate =
  [d| instance SelectX tup
        where
          type SelX tup = Double
          selectX tup = undefined
            -- Use `Double` and `undefined` as placeholders
  |]

mkSelectClassPlusInstances
    :: Int    -- ^ Max tuple width
    -> DecsQ
mkSelectClassPlusInstances n = do
    [classTempl]    <- classTemplate
    [instanceTempl] <- instanceTemplate
    let classDecs = [everywhere (mkT (fixName s)) classTempl | s <- [1..n]]
        instDecs =
          [ everywhere
              ( mkT (fixTupType s w)
              . mkT (fixTupPat s w)
              . mkT (fixTupExp s w)
              . mkT (fixName s)
              )
              instanceTempl
            | w <- [2..n]
            , s <- [1..w]
          ]
    return (classDecs ++ instDecs)

-- | @"SelectX_0"@ -> @"Select33"@ (for @n=33@)
fixName :: Int -> Name -> Name
fixName s
    = mkName
    . concatMap (\c -> if c=='X' then show s else [c])
    . takeWhile (/='_')
    . nameBase

fixTupType :: Int -> Int -> Type -> Type
fixTupType s w ty
    | VarT tup <- ty
    , "tup" <- show tup = foldl1 AppT ((TupleT w) : tupVars)
    | ConT doub <- ty
    , show doub == "Double" = tupVars !! (s-1)
    | otherwise = ty
  where
    tupVars = map VarT $ take w varSupply

fixTupPat :: Int -> Int -> Pat -> Pat
fixTupPat s w pat
    | VarP tup <- pat
    , "tup" <- show tup = TupP tupVars
    | otherwise = pat
  where
    tupVars = map VarP $ take w varSupply

fixTupExp :: Int -> Int -> Exp -> Exp
fixTupExp s w ex
    | VarE tup <- ex
    , "tup" <- show tup = TupE tupVars
    | VarE undef <- ex
    , show undef == "undefined" = tupVars !! (s-1)
    | otherwise = ex
  where
    tupVars = map VarE $ take w varSupply



--------------------------------------------------------------------------------
-- * Symbol type for tuple construction and elimination of tuples
--------------------------------------------------------------------------------

mkTupleSym
    :: String  -- ^ Type name
    -> String  -- ^ Base name for constructors
    -> String  -- ^ Base name for selectors
    -> Int     -- ^ Max tuple width
    -> DecsQ
mkTupleSym tyName tupName selName n = do
    let tupCons =
          [ ForallC
              (map PlainTV (take w varSupply))
              [eqPred (VarT (mkName "sig")) (signature w)]
              (NormalC (mkName (tupName ++ show w)) [])
            | w <- [2..n]
          ]
    let selCons =
          [ ForallC
              [PlainTV (mkName "tup")]
              [ eqPred
                  (VarT (mkName "sig"))
                  ( foldl1 AppT
                      [ ConT ''(:->)
                      , VarT (mkName "tup")
                      , AppT (ConT ''Full) (AppT (ConT (mkName ("Sel" ++ show s))) (VarT (mkName "tup")))
                      ]
                  )
              , classPred (mkName ("Select" ++ show s)) [VarT (mkName "tup")]
              ]
              (NormalC (mkName (selName ++ show s)) [])
            | s <- [1..n]
          ]
    return [DataD [] (mkName tyName) [PlainTV (mkName "sig")] (tupCons ++ selCons) []]
  where
    signature :: Int -> Type
    signature w = foldr
        (\a res -> foldl1 AppT [ConT ''(:->), a, res])
        (AppT (ConT ''Full)
        (foldl AppT (TupleT w) vars))
        vars
      where
        vars = map VarT $ take w varSupply



--------------------------------------------------------------------------------
-- * 'Syntactic' instances for tuples
--------------------------------------------------------------------------------

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
-- >     ) =>
-- >       Syntactic (a,...,x)
-- >   where
-- >     type Domain (a,...,x)   = Domain a
-- >     type Internal (a,...,x) = (Internal a, ..., Internal x)
-- >     desugar (a,...,x) = Sym (symInj TupN) :$ desugar a :$ ... :$ desugar x
-- >     sugar tup         = (sugar (Sym (symInj Sel1) :$ tup), ..., sugar (Sym (symInj SelN) :$ tup))
deriveSyntacticForTuples
    :: (Type -> Cxt)   -- ^ @internalPred@ (see above)
    -> (Type -> Type)  -- ^ @mkDomain@ (see above)
    -> (Exp -> Exp)    -- ^ Symbol injection
    -> Int             -- ^ Max tuple width
    -> DecsQ
deriveSyntacticForTuples internalPred mkDomain symInj n = return $
    map deriveSyntacticForTuple [2..n]
  where
    deriveSyntacticForTuple w = InstanceD
        ( concat
            [ map (classPred ''Syntactic . return) varsT
            , concatMap internalPred $ map (AppT (ConT ''Internal)) varsT
            , [classPred ''(:<:) [ConT (mkName "Tuple"), VarT (mkName "sym")]]
            , [eqPred domainA (mkDomain (VarT (mkName "sym")))]
            , [eqPred domainA (AppT (ConT ''Domain) b)
                | b <- tail varsT
              ]
            ]
        )
        (AppT (ConT ''Syntactic) tupT)
        [ tySynInst ''Domain [tupT] domainA
        , tySynInst ''Internal [tupT] tupTI
        , FunD 'desugar
            [ Clause
                [TupP varsP]
                (NormalB
                  ( foldl
                      (\s a -> foldl1 AppE [ConE '(:$), s, AppE (VarE 'desugar) a])
                      (AppE (ConE 'Sym) (symInj (ConE (mkName ("Tup" ++ show w)))))
                      varsE
                  )
                )
                []
            ]
        , FunD 'sugar
            [ Clause
                [VarP (mkName "tup")]
                (NormalB
                  ( TupE
                      [ AppE
                          (VarE 'sugar)
                          ( foldl1 AppE
                              [ ConE '(:$)
                              , AppE (ConE 'Sym) (symInj (ConE (mkName ("Sel" ++ show s))))
                              , VarE (mkName "tup")
                              ]
                          )
                        | s <- [1..w]
                      ]
                  )
                )
                []
            ]
        ]
      where
        varsT   = map VarT $ take w varSupply
        tupT    = foldl AppT (TupleT w) varsT
        tupTI   = foldl AppT (TupleT w) $ map (AppT (ConT ''Internal)) varsT
        domainA = AppT (ConT ''Domain) (VarT (mkName "a"))
        varsP   = map VarP $ take w varSupply
        varsE   = map VarE $ take w varSupply

