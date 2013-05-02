import Test.Framework
import Test.Golden

import qualified Data.ByteString.Lazy.Char8 as B

import NanoFeldspar.Core (showAST)
import NanoFeldspar.Test



mkGold1 = B.writeFile "tests/gold/prog1.txt" $ B.pack $ showAST prog1
mkGold2 = B.writeFile "tests/gold/prog2.txt" $ B.pack $ showAST prog2
mkGold3 = B.writeFile "tests/gold/prog3.txt" $ B.pack $ showAST prog3
mkGold5 = B.writeFile "tests/gold/prog5.txt" $ B.pack $ showAST prog5
mkGold6 = B.writeFile "tests/gold/prog6.txt" $ B.pack $ showAST prog6
mkGold7 = B.writeFile "tests/gold/prog7.txt" $ B.pack $ showAST prog7
mkGold8 = B.writeFile "tests/gold/prog8.txt" $ B.pack $ showAST prog8

tests = testGroup "TreeTests"
    [ goldenVsString "prog1" "tests/gold/prog1.txt" $ return $ B.pack $ showAST prog1
    , goldenVsString "prog2" "tests/gold/prog2.txt" $ return $ B.pack $ showAST prog2
    , goldenVsString "prog3" "tests/gold/prog3.txt" $ return $ B.pack $ showAST prog3
    , goldenVsString "prog5" "tests/gold/prog5.txt" $ return $ B.pack $ showAST prog5
    , goldenVsString "prog6" "tests/gold/prog6.txt" $ return $ B.pack $ showAST prog6
    , goldenVsString "prog7" "tests/gold/prog7.txt" $ return $ B.pack $ showAST prog7
    , goldenVsString "prog8" "tests/gold/prog8.txt" $ return $ B.pack $ showAST prog8
    ]

main = defaultMain [tests]

