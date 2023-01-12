{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE LambdaCase #-}

import Data.List (nub)
import FR (FR, choices, fix, gen, magic, pick)
import PartialProfunctors (comap)
import Reflective (exact)
import Test.QuickCheck (Gen)
import qualified Test.QuickCheck as QC

data Tree = Leaf | Node Tree Int Tree
  deriving (Show, Eq, Ord)

reflInt :: (Int, Int) -> FR String Int Int
reflInt (lo, hi) = pick "Int" [exact i | i <- [lo .. hi]]

genInt :: (Int, Int) -> Gen Int
genInt (lo, hi) = QC.elements [lo .. hi]

reflTree :: FR String Tree Tree
reflTree = fix aux (10 :: Int)
  where
    aux self n
      | n == 0 = exact Leaf
      | otherwise = do
          pick
            "Tree"
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

reflBST :: FR String Tree Tree
reflBST = fix aux (1, 10)
  where
    aux self (lo, hi)
      | lo > hi = return Leaf
      | otherwise = do
          pick
            "Tree"
            [ return Leaf,
              do
                x <- magic (reflInt (lo, hi))
                l <- magic (self (lo, x - 1))
                r <- magic (self (x + 1, hi))
                return (Node l x r)
            ]

reflBSTgood :: FR String Tree Tree
reflBSTgood = fix aux (1, 10)
  where
    aux self (lo, hi)
      | lo > hi = exact Leaf
      | otherwise = do
          pick
            "Tree"
            [ exact Leaf,
              do
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
  print (nub $ choices reflBSTgood (Node Leaf 1 (Node Leaf 2 Leaf)))
  print (nub $ choices reflBST (Node Leaf 1 (Node Leaf 2 Leaf)))