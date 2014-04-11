module Main where

import qualified Normal
import qualified WithArity
import qualified JoiningTypes
import qualified Dynamic

main :: IO ()
main = do
  Normal.main
  WithArity.main
  JoiningTypes.main
  Dynamic.main
