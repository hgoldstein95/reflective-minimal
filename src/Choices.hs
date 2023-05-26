{-

Supporting code for the choices and shrink interps.

-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

module Choices where

import Control.Applicative ((<|>))
import Data.List (tails)

newtype Bits = Bits {unBits :: [Bool]}
  deriving (Eq)

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

data BitTree = BitTree {unBitTree :: [BitNode], size :: Int}
  deriving (Eq)

data BitNode = Draw BitTree | Bit Bool
  deriving (Eq)

instance Ord BitTree where
  compare x y =
    case compare (size x) (size y) of
      EQ -> compare (unBits $ flatten x) (unBits $ flatten y)
      c -> c

instance Show BitTree where
  show (BitTree xs _) = concatMap show xs

instance Show BitNode where
  show (Draw (BitTree xs _)) = "(" ++ concatMap show xs ++ ")"
  show (Bit b) = if b then "1" else "0"

pattern BTEmpty :: BitTree
pattern BTEmpty <- BitTree [] _

pattern BTBit :: Bool -> [BitNode] -> BitTree
pattern BTBit b bs <- BitTree (Bit b : bs) _

pattern BTDraw :: BitTree -> [BitNode] -> BitTree
pattern BTDraw ts bs <- BitTree (Draw ts : bs) _

(+++) :: BitTree -> BitTree -> BitTree
BitTree xs s1 +++ BitTree ys s2 = BitTree (xs ++ ys) (s1 + s2)

draw :: BitTree -> BitTree
draw (BitTree [] _) = empty
draw (BitTree [Bit b] _) = bit b
draw (BitTree [Draw xs] s) = BitTree [Draw xs] s
draw b = BitTree [Draw b] (size b)

bit :: Bool -> BitTree
bit b = BitTree [Bit b] 1

empty :: BitTree
empty = BitTree [] 0

tree :: [BitNode] -> BitTree
tree ns = BitTree ns (sum $ map sz ns)
  where
    sz (Draw t) = size t
    sz (Bit _) = 1

flatten :: BitTree -> Bits
flatten = Bits . ($ []) . aux . unBitTree
  where
    aux [] = id
    aux (Bit !b : !bs) = b `cons` aux bs
    aux (Draw !xs : !bs) = aux (unBitTree xs) `app` aux bs
    cons !x !xs = (x :) `app` xs
    app = (.)

zeroDraws :: BitTree -> [BitTree]
zeroDraws = aux
  where
    aux :: BitTree -> [BitTree]
    aux BTEmpty = [empty]
    aux (BTBit b bs) = (bit b +++) <$> aux (tree bs)
    aux (BTDraw xs bs) =
      ((draw xs +++) <$> aux (tree bs))
        <|> ((\case BTEmpty -> tree bs; ys -> draw ys +++ tree bs) <$> aux xs)
        <|> ((\case BTEmpty -> tree bs; ys -> draw ys +++ tree bs) <$> zeros xs)
    aux _ = error "zeroDraws: impossible"

    zeros :: BitTree -> [BitTree]
    zeros =
      map (\xs -> BitTree (map Bit xs) (length xs))
        . tails
        . map (const False)
        . unBits
        . flatten

swapBits :: BitTree -> [BitTree]
swapBits = map (tree . map Bit) . aux . unBits . flatten
  where
    aux :: [Bool] -> [[Bool]]
    aux (True : False : bs) = ([False, True] ++ bs) : (([True, False] ++) <$> bs : aux bs)
    aux (x : xs) = (x :) <$> aux xs
    aux [] = [[]]

subChoices :: BitTree -> [BitTree]
subChoices BTEmpty = []
subChoices (BTDraw xs bs) = [xs] ++ subChoices xs ++ subChoices (tree bs)
subChoices (BTBit _ bs) = subChoices (tree bs)
subChoices _ = error "undefined"

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