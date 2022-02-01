module Main where

import Kenogrammatics

main :: IO ()
main = do
  print $ tnf "Hello World"
  print $ tContexture 4
  print $ kligate (tnf [1,2,3]) (tnf [1]) []
