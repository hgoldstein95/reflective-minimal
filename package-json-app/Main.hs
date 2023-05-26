{-

Main file for application that performs our realistic shrinking example of shrinking
a user provided buggy JSON file.

-}

module Main (main) where

import Data.List (isInfixOf)
import Interps (shrink)
import Examples.PackageJSON (package)

main :: IO ()
main =  getContents >>= putStrLn . shrink (isInfixOf "\"express\":\"^4.15.3\"") package
                            -- printing the json shrunk against the property that it
                            -- contains "express": "^4.15.3" i.e. the simples correct
                            -- json that contains this line
