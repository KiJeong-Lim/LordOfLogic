module Main (main) where

import System.Directory (findExecutable, makeAbsolute)
import System.Exit (exitWith)
import System.Process (rawSystem)

main :: IO ()
main = do
    found <- findExecutable "lol"
    case found of
        Nothing -> fail "Cabal did not provide the lol executable for the release tests."
        Just path -> do
            binary <- makeAbsolute path
            rawSystem "python3" ["test/release/check.py", "golden", binary] >>= exitWith
