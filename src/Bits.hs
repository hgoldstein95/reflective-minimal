{-# LANGUAGE LambdaCase #-}

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

zeroDraws :: BitTree -> [BitTree]
zeroDraws = map BitTree . aux . unBitTree
  where
    aux :: [BitNode] -> [[BitNode]]
    aux [] = [[]]
    aux (Bit b : bs) = (Bit b :) <$> aux bs
    aux (Draw xs : bs) =
      ((Draw xs :) <$> aux bs)
        <|> ((\case [] -> bs; ys -> Draw ys : bs) <$> aux xs)
        <|> ((\case [] -> bs; ys -> Draw ys : bs) <$> zeros xs)

    zeros :: [BitNode] -> [[BitNode]]
    zeros =
      map (map Bit)
        . tails
        . map (const False)
        . unBits
        . flatten
        . BitTree

swapBits :: BitTree -> [BitTree]
swapBits = map (BitTree . map Bit) . aux . unBits . flatten
  where
    aux :: [Bool] -> [[Bool]]
    aux (True : False : bs) = ([False, True] ++ bs) : (([True, False] ++) <$> bs : aux bs)
    aux (x : xs) = (x :) <$> aux xs
    aux [] = [[]]

pickSubTree :: BitTree -> [BitTree]
pickSubTree x = filter (< x) . nub . map BitTree . aux . unBitTree $ x
  where
    aux :: [BitNode] -> [[BitNode]]
    aux [] = []
    aux (Bit _ : bs) = aux bs
    aux (Draw xs : bs) = aux bs <|> aux xs <|> [xs]

-- simplifyDraws :: BitTree -> BitTree
-- simplifyDraws = BitTree . aux . unBitTree
--   where
--     aux :: [BitNode] -> [BitNode]
--     aux [] = []
--     aux (Draw xs : bs) | length xs > 5 = aux xs ++ aux bs
--     aux (b : bs) = b : aux bs

integerToBits :: (Integer, Integer) -> Integer -> [Bool]
integerToBits (lo, hi) j = ((j < 0) :) . reverse $ aux bitWidth (abs j)
  where
    bitWidth = ceiling $ logBase 2 (fromIntegral (hi - lo + 1) :: Double) :: Int
    aux 0 _ = []
    aux n i = odd i : aux (n - 1) (i `div` 2)

bitsToInteger :: (Integer, Integer) -> [Bool] -> Maybe (Integer, [Bool])
bitsToInteger _ [] = Nothing
bitsToInteger (lo, hi) (sign : bbs) =
  if length bbs < bitWidth
    then Nothing
    else Just ((* if sign then (-1) else 1) . aux (0 :: Int) . reverse $ take bitWidth bbs, drop bitWidth bbs)
  where
    bitWidth = ceiling $ logBase 2 (fromIntegral (hi - lo + 1) :: Double) :: Int
    aux _ [] = 0
    aux n (True : bs) = 2 ^ n + aux (n + 1) bs
    aux n (False : bs) = aux (n + 1) bs