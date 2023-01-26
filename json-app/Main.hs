module Main (main) where

import JSONExample (parseJSON, printJSON)

main :: IO ()
main = getContents >>= putStrLn . printJSON . parseJSON
