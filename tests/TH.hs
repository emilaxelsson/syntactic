{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

module TH where



import Data.List (nub)

import Language.Syntactic
import Language.Syntactic.TH



data Sym sig
  where
    A :: Int -> Bool -> Sym (a :-> a :-> Full a)
    B :: Sym (Full Bool)
    C :: String -> Sym (a :-> Int :-> Full a)

deriveSymbol    ''Sym
deriveEquality  ''Sym
deriveRender id ''Sym

tests =
    [ equal B B
    , equal (A 5 True) (A 5 True)
    , equal (C "syntactic") (C "syntactic")
    , not $ equal (A 5 True) (A 6 True)
    , not $ equal (A 5 True) (C "c")
    , hashes == nub hashes
    , renderSym (A 5 True) == "(A 5 True)"
    ]
  where
    hashes =
        [ hash $ A 5 True
        , hash $ B
        , hash $ C "a"
        , hash $ A 6 True
        , hash $ C "b"
        ]

main :: IO ()
main = if and tests
    then return ()
    else error "TH tests failed"

