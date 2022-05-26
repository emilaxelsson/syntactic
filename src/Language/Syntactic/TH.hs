{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}

module Language.Syntactic.TH where



#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif

import Language.Haskell.TH

import Data.Hash (hashInt, combine)
import qualified Data.Hash as Hash

import Language.Syntactic



-- | Get the name and arity of a constructor
conName :: Con -> (Name, Int)
conName (NormalC name args) = (name, length args)
conName (RecC name args)    = (name, length args)
conName (InfixC _ name _)   = (name, 2)
conName (ForallC _ _ c)     = conName c
#if __GLASGOW_HASKELL__ >= 800
conName (GadtC [n] as _)    = (n, length as)
conName (RecGadtC [n] as _) = (n, length as)
  -- I don't know what it means when a `GadtC` and `RecGadtC` don't have
  -- singleton lists of names
#endif

-- | Description of class methods
data Method
    = DefaultMethod Name Name
        -- ^ rhs = lhs
    | MatchingMethod Name (Con -> Int -> Name -> Int -> Clause) [Clause]
        -- ^ @MatchingMethod methodName mkClause extraClauses@
        --
        -- @mkClause@ takes as arguments (1) a description of the constructor,
        -- (2) the constructor's index, (3) the constructor's name, and (4) its
        -- arity.

-- | General method for class deriving
deriveClass
    :: Cxt       -- ^ Instance context
    -> Name      -- ^ Type constructor name
    -> Type      -- ^ Class head (e.g. @Render Con@)
    -> [Method]  -- ^ Methods
    -> DecsQ
deriveClass cxt ty clHead methods = do
    Just cs <- viewDataDef <$> reify ty
    return
      [ instD cxt clHead $
          [ FunD method (clauses ++ extra)
            | MatchingMethod method mkClause extra <- methods
            , let clauses = [ mkClause c i nm ar | (i,c) <- zip [0..] cs
                            , let (nm,ar) = conName c
                            ]
          ] ++
          [ FunD rhs [Clause [] (NormalB (VarE lhs)) []]
            | DefaultMethod rhs lhs <- methods
          ]
      ]

-- | General method for class deriving
deriveClassSimple
    :: Name      -- ^ Class name
    -> Name      -- ^ Type constructor name
    -> [Method]  -- ^ Methods
    -> DecsQ
deriveClassSimple cl ty = deriveClass [] ty (AppT (ConT cl) (ConT ty))

varSupply :: [Name]
varSupply = map mkName $ tail $ concat $ iterate step [[]]
  where
    step :: [String] -> [String]
    step vars = concatMap (\c -> map (c:) vars) ['a' .. 'z']

-- | Derive 'Symbol' instance for a type
deriveSymbol
    :: Name  -- ^ Type name
    -> DecsQ
deriveSymbol ty =
    deriveClassSimple ''Symbol ty [MatchingMethod 'symSig  symSigClause []]
  where
    symSigClause _ _ con arity =
      Clause [conPat con (replicate arity WildP)] (NormalB (VarE 'signature)) []

-- | Derive 'Equality' instance for a type
--
-- > equal Con1 Con1 = True
-- > equal (Con2 a1 ... x1) (Con2 a2 ... x2) = and [a1==a2, ... x1==x2]
-- > equal _ _ = False
--
-- > hash Con1           = hashInt 0
-- > hash (Con2 a ... x) = foldr1 combine [hashInt 1, hash a, ... hash x]
deriveEquality
    :: Name  -- ^ Type name
    -> DecsQ
deriveEquality ty = do
    Just cs <- viewDataDef <$> reify ty
    let equalFallThrough = if length cs > 1
          then [Clause [WildP, WildP] (NormalB $ ConE 'False) []]
          else []
    deriveClassSimple ''Equality ty
      [ MatchingMethod 'equal equalClause equalFallThrough
      , MatchingMethod 'hash hashClause []
      ]
  where
    equalClause _ _ con arity = Clause
        [ conPat con [VarP v | v <- vs1]
        , conPat con [VarP v | v <- vs2]
        ]
        (NormalB body)
        []
      where
        vs1 = take arity varSupply
        vs2 = take arity $ drop arity varSupply

        body = case arity of
          0 -> ConE 'True
          _ -> AppE (VarE 'and)
                 ( ListE
                     [ InfixE (Just (VarE v1)) (VarE '(==)) (Just (VarE v2))
                       | (v1,v2) <- zip vs1 vs2
                     ]
                 )

    hashClause _ i con arity = Clause
        [conPat con [VarP v | v <- vs]]
        (NormalB body)
        []
      where
        vs = take arity varSupply
        body = case arity of
          0 -> AppE (VarE 'hashInt) (LitE (IntegerL (toInteger i)))
          _ -> foldl1 AppE
                [ VarE 'foldr1
                , VarE 'combine
                , ListE
                    $ AppE (VarE 'hashInt) (LitE (IntegerL (toInteger i)))
                    : [ AppE (VarE 'Hash.hash) (VarE v)
                        | v <- vs
                      ]
                ]

-- | Derive 'Render' instance for a type
--
-- > renderSym Con1           = "Con1"
-- > renderSym (Con2 a ... x) = concat ["(", unwords ["Con2", show a, ... show x], ")"]
deriveRender
    :: (String -> String)  -- ^ Constructor name modifier
    -> Name                -- ^ Type name
    -> DecsQ
deriveRender modify ty =
    deriveClassSimple ''Render ty [MatchingMethod 'renderSym renderClause []]
  where
    conName = modify . nameBase

    renderClause _ _ con arity = Clause
        [conPat con [VarP v | v <- take arity varSupply]]
        (NormalB body)
        []
      where
        body = case arity of
            0 -> LitE $ StringL $ conName con
            _ -> renderRHS con $ take arity varSupply

    renderRHS :: Name -> [Name] -> Exp
    renderRHS con args =
      AppE (VarE 'concat)
        ( ListE
            [ LitE (StringL "(")
            , AppE (VarE 'unwords)
                (ListE (LitE (StringL (conName con)) : map showArg args))
            , LitE (StringL ")")
            ]
        )

    showArg :: Name -> Exp
    showArg arg = AppE (VarE 'show) (VarE arg)



--------------------------------------------------------------------------------
-- * Portability
--------------------------------------------------------------------------------

-- Using `__GLASGOW_HASKELL__` instead of `MIN_VERSION_template_haskell`,
-- because the latter doesn't work when the package is compiled with `-f-th`.

-- | Construct an instance declaration
instD
    :: Cxt    -- ^ Context
    -> Type   -- ^ Instance
    -> [Dec]  -- ^ Methods, etc.
    -> Dec
#if __GLASGOW_HASKELL__ >= 800
instD = InstanceD Nothing
#else
instD = InstanceD
#endif

-- | Get the constructors of a data type definition
viewDataDef :: Info -> Maybe [Con]
#if __GLASGOW_HASKELL__ >= 800
viewDataDef (TyConI (DataD _ _ _ _ cs _)) = Just cs
#else
viewDataDef (TyConI (DataD _ _ _ cs _)) = Just cs
#endif
viewDataDef _ = Nothing

-- | Portable method for constructing a 'Pred' of the form @(t1 ~ t2)@
eqPred :: Type -> Type -> Pred
#if __GLASGOW_HASKELL__ >= 710
eqPred t1 t2 = foldl1 AppT [EqualityT,t1,t2]
#else
eqPred = EqualP
#endif

-- | Portable method for constructing a 'Pred' of the form @SomeClass t1 t2 ...@
classPred
    :: Name            -- ^ Class name
    -> (Name -> Type)  -- ^ How to make a type for the class (typically 'ConT' or 'VarT')
    -> [Type]          -- ^ Class arguments
    -> Pred
#if __GLASGOW_HASKELL__ >= 710
classPred cl con = foldl AppT (con cl)
#else
classPred cl con = ClassP cl
#endif

-- | Portable method for constructing a type synonym instance
tySynInst :: Name -> [Type] -> Type -> Dec
#if __GLASGOW_HASKELL__ >= 808
tySynInst t as rhs = TySynInstD $
  TySynEqn Nothing (foldl AppT (ConT t) as) rhs
#elif __GLASGOW_HASKELL__ >= 708
tySynInst t as rhs = TySynInstD t (TySynEqn as rhs)
#else
tySynInst = TySynInstD
#endif

conPat :: Name -> [Pat] -> Pat
#if __GLASGOW_HASKELL__ >= 902
conPat name ps = ConP name [] ps
#else
conPat name ps = ConP name ps
#endif

