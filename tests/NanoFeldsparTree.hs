import Test.Tasty
import Test.Tasty.Golden

import Data.ByteString.Lazy.UTF8 (fromString)

import NanoFeldspar.Core (showAST)
import NanoFeldspar.Test



mkGold_scProd = writeFile "tests/gold/scProd.txt" $ showAST scProd
mkGold_matMul = writeFile "tests/gold/matMul.txt" $ showAST matMul
mkGold_prog1  = writeFile "tests/gold/prog1.txt"  $ showAST prog1
mkGold_prog2  = writeFile "tests/gold/prog2.txt"  $ showAST prog2
mkGold_prog3  = writeFile "tests/gold/prog3.txt"  $ showAST prog3
mkGold_prog4  = writeFile "tests/gold/prog4.txt"  $ showAST prog4
mkGold_prog5  = writeFile "tests/gold/prog5.txt"  $ showAST prog5
mkGold_prog6  = writeFile "tests/gold/prog6.txt"  $ showAST prog6
mkGold_prog7  = writeFile "tests/gold/prog7.txt"  $ showAST prog7
mkGold_prog8  = writeFile "tests/gold/prog8.txt"  $ showAST prog8

tests = testGroup "TreeTests"
    [ goldenVsString "scProd" "tests/gold/scProd.txt" $ return $ fromString $ showAST scProd
    , goldenVsString "matMul" "tests/gold/matMul.txt" $ return $ fromString $ showAST matMul
    , goldenVsString "prog1"  "tests/gold/prog1.txt"  $ return $ fromString $ showAST prog1
    , goldenVsString "prog2"  "tests/gold/prog2.txt"  $ return $ fromString $ showAST prog2
    , goldenVsString "prog3"  "tests/gold/prog3.txt"  $ return $ fromString $ showAST prog3
    , goldenVsString "prog4"  "tests/gold/prog4.txt"  $ return $ fromString $ showAST prog4
    , goldenVsString "prog5"  "tests/gold/prog5.txt"  $ return $ fromString $ showAST prog5
    , goldenVsString "prog6"  "tests/gold/prog6.txt"  $ return $ fromString $ showAST prog6
    , goldenVsString "prog7"  "tests/gold/prog7.txt"  $ return $ fromString $ showAST prog7
    , goldenVsString "prog8"  "tests/gold/prog8.txt"  $ return $ fromString $ showAST prog8
    ]

main = defaultMain tests

