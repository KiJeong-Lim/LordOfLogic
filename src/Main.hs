module Main (main) where

import qualified LoL.Main as LoL
import System.Environment (getArgs)

main :: IO ()
main = getArgs >>= LoL.mainWithArgs
