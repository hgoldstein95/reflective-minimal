{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE LambdaCase #-}

import PartialProfunctors (comap)
import Reflective (Pick (pick), Reflective, exact)
import UnGenFChoices (unGenFChoices)

data Tree = Leaf | Node Tree Int Tree
  deriving (Show, Eq, Ord)

reflTree :: Reflective g => g String Tree Tree
reflTree = aux (10 :: Int)
  where
    reflInt lo hi = pick [(show i, exact i) | i <- [lo .. hi]]
    aux n
      | n == 0 = exact Leaf
      | otherwise = do
          pick
            [ ("Leaf", exact Leaf),
              ( "Node",
                do
                  x <- comap (\case Leaf -> Nothing; Node _ x _ -> Just x) (reflInt 1 10)
                  l <- comap (\case Leaf -> Nothing; Node l _ _ -> Just l) (aux (n - 1))
                  r <- comap (\case Leaf -> Nothing; Node _ _ r -> Just r) (aux (n - 1))
                  pure (Node l x r)
              ),
              ("Thing", exact (Node Leaf 2 Leaf))
            ]

reflBST :: Reflective g => g String Tree Tree
reflBST = aux 1 10
  where
    reflInt lo hi = pick [(show i, exact i) | i <- [lo .. hi]]
    aux lo hi
      | lo > hi = exact Leaf
      | otherwise = do
          pick
            [ ("Leaf", exact Leaf),
              ( "Node",
                do
                  x <- comap (\case Leaf -> Nothing; Node _ x _ -> Just x) (reflInt lo hi)
                  l <- comap (\case Leaf -> Nothing; Node l _ _ -> Just l) (aux lo (x - 1))
                  r <- comap (\case Leaf -> Nothing; Node _ _ r -> Just r) (aux (x + 1) hi)
                  pure (Node l x r)
              )
            ]

main :: IO ()
main = do
  print (unGenFChoices reflTree (Node Leaf 1 (Node Leaf 2 Leaf)))
  print (unGenFChoices reflBST (Node Leaf 1 (Node Leaf 2 Leaf)))