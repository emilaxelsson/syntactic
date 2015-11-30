{-# LANGUAGE TemplateHaskell #-}

module Language.Syntactic.TH where



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
    t@(TyConI (DataD _ _ _ cs _)) <- reify ty
    return
      [ InstanceD cxt clHead $
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
      Clause [ConP con (replicate arity WildP)] (NormalB (VarE 'signature)) []

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
    TyConI (DataD _ _ _ cs _) <- reify ty
    let equalFallThrough = if length cs > 1
          then [Clause [WildP, WildP] (NormalB $ ConE 'False) []]
          else []
    deriveClassSimple ''Equality ty
      [ MatchingMethod 'equal equalClause equalFallThrough
      , MatchingMethod 'hash hashClause []
      ]
  where
    equalClause _ _ con arity = Clause
        [ ConP con [VarP v | v <- vs1]
        , ConP con [VarP v | v <- vs2]
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
        [ConP con [VarP v | v <- vs]]
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
        [ConP con [VarP v | v <- take arity varSupply]]
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

