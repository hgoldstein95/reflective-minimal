{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE LambdaCase #-}

-- TODO: this file has become out of date and doesnt compile. It should be updated
--       and have the properties we list in it and testable

import Data.List (nub)
import Freer (Reflective, choices, choicesS, comap, exact, fix, gen, label, magic, pick, regen, regenS)
import Test.QuickCheck (Gen)
import qualified Test.QuickCheck as QC

data Tree = Leaf | Node Tree Int Tree
  deriving (Show, Eq, Ord)

reflInt :: (Int, Int) -> Reflective Int Int
reflInt (lo, hi) = pick [label (show i) (exact i) | i <- [lo .. hi]]

genInt :: (Int, Int) -> Gen Int
genInt (lo, hi) = QC.elements [lo .. hi]

reflTree :: Reflective Tree Tree
reflTree = fix aux (10 :: Int)
  where
    aux self n
      | n == 0 = exact Leaf
      | otherwise = do
          pick
            [ exact Leaf,
              do
                x <- comap (\case Leaf -> Nothing; Node _ x _ -> Just x) (reflInt (1, 10))
                l <- comap (\case Leaf -> Nothing; Node l _ _ -> Just l) (self (n - 1))
                r <- comap (\case Leaf -> Nothing; Node _ _ r -> Just r) (self (n - 1))
                pure (Node l x r),
              exact (Node Leaf 2 Leaf)
            ]

genBST :: Gen Tree
genBST = aux (1, 10)
  where
    aux (lo, hi)
      | lo > hi = return Leaf
      | otherwise = do
          QC.oneof
            [ return Leaf,
              do
                x <- genInt (lo, hi)
                l <- aux (lo, x - 1)
                r <- aux (x + 1, hi)
                return (Node l x r)
            ]

reflBST :: Reflective Tree Tree
reflBST = fix aux (1, 10)
  where
    aux self (lo, hi)
      | lo > hi = return Leaf
      | otherwise = do
          pick
            [ return Leaf,
              do
                x <- magic (reflInt (lo, hi))
                l <- magic (self (lo, x - 1))
                r <- magic (self (x + 1, hi))
                return (Node l x r)
            ]

reflBSTgood :: Reflective Tree Tree
reflBSTgood = fix aux (1, 10)
  where
    aux self (lo, hi)
      | lo > hi = exact Leaf
      | otherwise = do
          pick
            [ label "leaf" (exact Leaf),
              label "node" $ do
                x <- comap (\case Leaf -> Nothing; (Node _ x _) -> Just x) (reflInt (lo, hi))
                l <- comap (\case Leaf -> Nothing; Node l _ _ -> Just l) (self (lo, x - 1))
                r <- comap (\case Leaf -> Nothing; Node _ _ r -> Just r) (self (x + 1, hi))
                exact (Node l x r)
            ]

main :: IO ()
main = do
  print (nub $ choices reflTree (Node Leaf 1 (Node Leaf 2 Leaf)))
  print =<< QC.generate (gen reflTree)
  print =<< QC.generate genBST
  let cs = head . nub $ choices reflBSTgood (Node Leaf 1 (Node Leaf 2 Leaf))
  print cs
  print (regen reflBSTgood cs)
  let ss = head . nub $ choicesS reflBSTgood (Node Leaf 1 (Node Leaf 2 Leaf))
  print ss
  print (regenS reflBSTgood ss)
  print (nub $ choices reflBST (Node Leaf 1 (Node Leaf 2 Leaf)))