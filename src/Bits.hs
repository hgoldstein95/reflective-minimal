module Bits where

import Control.Applicative ((<|>))
import Data.List (nub, tails)

newtype Bits = Bits {unBits :: [Bool]}
  deriving (Eq)

instance Ord Bits where
  compare (Bits xs) (Bits ys) =
    case compare (length xs) (length ys) of
      EQ -> compare xs ys
      c -> c

instance Show Bits where
  show (Bits bs) = concatMap (\b -> if b then "1" else "0") bs

listBits :: Int -> [Bits]
listBits = map Bits . aux
  where
    aux 0 = [[]]
    aux n =
      let xs = aux (n - 1)
       in ((False :) <$> xs) ++ ((True :) <$> xs)

bitsToInt :: Bits -> Int
bitsToInt = aux (0 :: Int) . reverse . unBits
  where
    aux _ [] = 0
    aux e (True : xs) = 2 ^ e + aux (e + 1) xs
    aux e (False : xs) = aux (e + 1) xs

newtype BitTree = BitTree {unBitTree :: [BitNode]}
  deriving (Eq)

data BitNode = Draw [BitNode] | Bit Bool
  deriving (Eq)

instance Ord BitTree where
  compare x y = compare (flatten x) (flatten y)

instance Show BitTree where
  show (BitTree xs) = concatMap show xs

instance Show BitNode where
  show (Draw xs) = "(" ++ concatMap show xs ++ ")"
  show (Bit b) = if b then "1" else "0"

draw :: BitTree -> BitTree
draw (BitTree []) = BitTree []
draw (BitTree [Bit b]) = BitTree [Bit b]
draw (BitTree [Draw xs]) = BitTree [Draw xs]
draw (BitTree xs) = BitTree [Draw xs]

bit :: Bool -> BitTree
bit b = BitTree [Bit b]

empty :: BitTree
empty = BitTree []

(+++) :: BitTree -> BitTree -> BitTree
BitTree xs +++ BitTree ys = BitTree (xs ++ ys)

flatten :: BitTree -> Bits
flatten = Bits . aux . unBitTree
  where
    aux [] = []
    aux (Bit b : bs) = b : aux bs
    aux (Draw xs : bs) = aux xs ++ aux bs

dropDraws :: BitTree -> [BitTree]
dropDraws x = filter (< x) . nub . map BitTree . aux . unBitTree $ x
  where
    aux :: [BitNode] -> [[BitNode]]
    aux [] = [[]]
    aux (Bit b : bs) = (Bit b :) <$> aux bs
    aux (Draw xs : bs) = ((Draw xs :) <$> aux bs) <|> [bs]

zeroDraws :: BitTree -> [BitTree]
zeroDraws x = filter (< x) . nub . map BitTree . aux . unBitTree $ x
  where
    flat = unBits . flatten . BitTree

    aux :: [BitNode] -> [[BitNode]]
    aux [] = [[]]
    aux (Bit b : bs) = (Bit b :) <$> aux bs
    aux (Draw xs : bs) =
      ((Draw xs :) <$> aux bs)
        <|> ((\ys -> Draw ys : bs) <$> aux xs)
        <|> ((\ys -> Draw ys : bs) <$> zeros xs)

    zeros :: [BitNode] -> [[BitNode]]
    zeros =
      map (map Bit)
        . filter (not . null)
        . tails
        . map (const False)
        . flat

swapBits :: BitTree -> [BitTree]
swapBits v = filter (< v) . map (BitTree . map Bit) . aux . unBits . flatten $ v
  where
    aux :: [Bool] -> [[Bool]]
    aux (True : False : bs) = ([False, True] ++ bs) : (([True, False] ++) <$> bs : aux bs)
    aux (x : xs) = (x :) <$> aux xs
    aux [] = [[]]
