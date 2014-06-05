module Main where

import qualified Normal
import qualified WithArity
import qualified JoiningTypes

main :: IO ()
main = do
  Normal.main
  WithArity.main
  JoiningTypes.main
