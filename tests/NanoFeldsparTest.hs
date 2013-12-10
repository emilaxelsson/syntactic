import Test.Framework
import Test.Golden

import qualified Data.ByteString.Lazy.Char8 as B

import NanoFeldspar



mkGold_scProd = B.writeFile "tests/gold/scProd.txt" $ B.pack $ showAST scProd
mkGold_matMul = B.writeFile "tests/gold/matMul.txt" $ B.pack $ showAST matMul

tests = testGroup "TreeTests"
    [ goldenVsString "scProd" "tests/gold/scProd.txt" $ return $ B.pack $ showAST scProd
    , goldenVsString "matMul" "tests/gold/matMul.txt" $ return $ B.pack $ showAST matMul
    ]

main = defaultMain [tests]

