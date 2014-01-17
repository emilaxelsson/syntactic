import Test.Tasty
import Test.Tasty.Golden

import Data.ByteString.Lazy.UTF8 (fromString)

import NanoFeldspar



mkGold_scProd = writeFile "tests/gold/scProd.txt" $ showAST scProd
mkGold_matMul = writeFile "tests/gold/matMul.txt" $ showAST matMul

tests = testGroup "TreeTests"
    [ goldenVsString "scProd" "tests/gold/scProd.txt" $ return $ fromString $ showAST scProd
    , goldenVsString "matMul" "tests/gold/matMul.txt" $ return $ fromString $ showAST matMul
    ]

main = defaultMain tests

