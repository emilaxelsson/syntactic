import Test.Framework
import Test.Golden

import qualified Data.ByteString.Lazy.Char8 as B

import NanoFeldspar.Core (showAST)
import NanoFeldspar.Test



mkGold_scProd = B.writeFile "tests/gold/scProd.txt" $ B.pack $ showAST scProd
mkGold_matMul = B.writeFile "tests/gold/matMul.txt" $ B.pack $ showAST matMul
mkGold_prog1  = B.writeFile "tests/gold/prog1.txt"  $ B.pack $ showAST prog1
mkGold_prog2  = B.writeFile "tests/gold/prog2.txt"  $ B.pack $ showAST prog2
mkGold_prog3  = B.writeFile "tests/gold/prog3.txt"  $ B.pack $ showAST prog3
mkGold_prog4  = B.writeFile "tests/gold/prog4.txt"  $ B.pack $ showAST prog4
mkGold_prog5  = B.writeFile "tests/gold/prog5.txt"  $ B.pack $ showAST prog5
mkGold_prog6  = B.writeFile "tests/gold/prog6.txt"  $ B.pack $ showAST prog6
mkGold_prog7  = B.writeFile "tests/gold/prog7.txt"  $ B.pack $ showAST prog7
mkGold_prog8  = B.writeFile "tests/gold/prog8.txt"  $ B.pack $ showAST prog8

tests = testGroup "TreeTests"
    [ goldenVsString "scProd" "tests/gold/scProd.txt" $ return $ B.pack $ showAST scProd
    , goldenVsString "matMul" "tests/gold/matMul.txt" $ return $ B.pack $ showAST matMul
    , goldenVsString "prog1"  "tests/gold/prog1.txt"  $ return $ B.pack $ showAST prog1
    , goldenVsString "prog2"  "tests/gold/prog2.txt"  $ return $ B.pack $ showAST prog2
    , goldenVsString "prog3"  "tests/gold/prog3.txt"  $ return $ B.pack $ showAST prog3
    , goldenVsString "prog4"  "tests/gold/prog4.txt"  $ return $ B.pack $ showAST prog4
    , goldenVsString "prog5"  "tests/gold/prog5.txt"  $ return $ B.pack $ showAST prog5
    , goldenVsString "prog6"  "tests/gold/prog6.txt"  $ return $ B.pack $ showAST prog6
    , goldenVsString "prog7"  "tests/gold/prog7.txt"  $ return $ B.pack $ showAST prog7
    , goldenVsString "prog8"  "tests/gold/prog8.txt"  $ return $ B.pack $ showAST prog8
    ]

main = defaultMain [tests]

