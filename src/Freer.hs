{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Freer where

import BidirectionalProfunctors (Profmonad)
import Bits
  ( BitNode (..),
    BitTree,
    Bits (..),
    bit,
    bitsToInt,
    bitsToInteger,
    draw,
    flatten,
    integerToBits,
    listBits,
    swapBits,
    tree,
    zeroDraws,
    (+++),
  )
import qualified Bits as BitTree
import Control.Exception (SomeException)
import Control.Lens (Getting, makePrisms, over, preview, view, _1, _2, _3, _head, _tail)
import Control.Monad (ap, guard, (>=>))
import Control.Monad.Logic (Logic, MonadLogic ((>>-)), observeAll)
import Data.Bifunctor (Bifunctor (second))
import Data.Char (chr, ord)
import Data.Foldable (asum)
import Data.List (group, minimumBy, nub, sort, transpose)
import Data.Maybe (catMaybes, fromMaybe, isJust, listToMaybe, maybeToList)
import Data.Monoid (First)
import Data.Ord (comparing)
import Data.Profunctor (Profunctor (..))
import Data.Void (Void)
import GHC.IO (catch, evaluate)
import PartialProfunctors (PartialProfunctor (..))
import Test.QuickCheck (Args (maxSize, maxSuccess), Gen, forAll, quickCheckWith, stdArgs)
import qualified Test.QuickCheck as QC

-- Core Definitions

type Weight = Rational

data Freer2 f b a where
  Return :: a -> Freer2 f b a
  Bind :: f b a -> (a -> Freer2 f b c) -> Freer2 f b c

type FR b a = Freer2 Refl b a

data Refl b a where
  Pick :: [(Int, Maybe String, FR b a)] -> Refl b a
  ChooseInteger :: (Integer, Integer) -> Refl Integer Integer
  Lmap :: (c -> d) -> Refl d a -> Refl c a
  Prune :: Refl b a -> Refl (Maybe b) a
  GetSize :: Refl b Int
  Resize :: Int -> Refl b a -> Refl b a

type Reflective a = FR a a

-- Typeclass Instances Combinators

instance Functor (Freer2 f b) where
  fmap f (Return x) = Return (f x)
  fmap f (Bind u g) = Bind u (fmap f . g)

instance Applicative (Freer2 f b) where
  pure = return
  (<*>) = ap

instance Monad (Freer2 f b) where
  return = Return
  Return x >>= f = f x
  Bind u g >>= f = Bind u (g >=> f)

instance Profunctor (Freer2 Refl) where
  dimap _ g (Return a) = Return (g a)
  dimap f g (Bind x h) = Bind (Lmap f x) (dimap f g . h)

instance Profmonad (Freer2 Refl)

instance PartialProfunctor (Freer2 Refl) where
  internaliseMaybe (Return a) = Return a
  internaliseMaybe (Bind x f) = Bind (Prune x) (internaliseMaybe . f)

prune :: FR b a -> FR (Maybe b) a
prune = internaliseMaybe

comap :: (a -> Maybe b) -> FR b v -> FR a v
comap f = lmap f . prune

getbits :: Int -> FR b Int
getbits w =
  Bind
    ( Pick
        [(1, Just (show (bitsToInt i)), pure (bitsToInt i)) | i <- listBits w]
    )
    Return

pick :: [(Int, String, FR b a)] -> FR b a
pick xs = Bind (Pick (map (over _2 Just) xs)) Return

frequency :: [(Int, FR b a)] -> FR b a
frequency xs = Bind (Pick (map (\(w, g) -> (w, Nothing, g)) xs)) Return

labelled :: [(String, FR b a)] -> FR b a
labelled xs = Bind (Pick (map (\(s, g) -> (1, Just s, g)) xs)) Return

oneof :: [FR b a] -> FR b a
oneof xs = Bind (Pick (map (1,Nothing,) xs)) Return

exact :: Eq v => v -> FR v v
exact x = comap (\y -> if y == x then Just y else Nothing) $ oneof [pure x]

choose :: (Int, Int) -> FR Int Int
choose (lo, hi) = labelled [(show i, exact i) | i <- [lo .. hi]]

chooseInteger :: (Integer, Integer) -> FR Integer Integer
chooseInteger p = Bind (ChooseInteger p) Return

integer :: FR Int Int
integer = sized $ \n -> labelled [(show i, exact i) | i <- concat (transpose [[0 .. n], reverse [-n .. -1]])]

char :: FR Char Char
char = sized $ \n -> labelled [(show i, exact (chr i)) | i <- [ord 'a' .. ord 'a' + n]]

alphaNum :: FR Char Char
alphaNum = labelled [(show c, exact c) | c <- ['a', 'b', 'c', '1', '2', '3']]

bool :: FR Bool Bool
bool = oneof [exact True, exact False]

vectorOf :: Eq a => Int -> FR a a -> FR [a] [a]
vectorOf 0 _ = exact []
vectorOf n g = do
  x <- tryFocus _head g
  xs <- tryFocus _tail (vectorOf (n - 1) g)
  exact (x : xs)

listOf :: Eq a => FR a a -> FR [a] [a]
listOf g = sized aux
  where
    aux 0 = exact []
    aux n =
      frequency
        [ (1, exact []),
          ( n,
            do
              x <- tryFocus _head g
              xs <- tryFocus _tail (aux (n - 1))
              exact (x : xs)
          )
        ]

nonEmptyListOf :: Eq a => FR a a -> FR [a] [a]
nonEmptyListOf g = do
  x <- tryFocus _head g
  xs <- tryFocus _tail (sized aux)
  exact (x : xs)
  where
    aux 0 = exact []
    aux n =
      frequency
        [ (1, exact []),
          ( n,
            do
              x <- tryFocus _head g
              xs <- tryFocus _tail (aux (n - 1))
              exact (x : xs)
          )
        ]

fwd :: FR c a -> FR Void a
fwd = lmap (\case {})

tryFocus :: Getting (First u') s u' -> FR u' v -> FR s v
tryFocus = comap . preview

focus :: Getting b s b -> FR b c -> FR s c
focus = lmap . view

resize :: Int -> FR b a -> FR b a
resize _ (Return x) = Return x
resize w (Bind x f) = Bind (Resize w x) (resize w . f)

sized :: (Int -> FR b a) -> FR b a
sized = Bind GetSize

-- suchThat :: FR a a -> (a -> Bool) -> FR a a
-- g `suchThat` p = comap (\x -> if p x then Just x else Nothing) aux
--   where
--     aux = do
--       x <- g
--       if p x then return x else aux

-- suchThatMaybe :: Eq a => FR a a -> (a -> Bool) -> FR (Maybe a) (Maybe a)
-- g `suchThatMaybe` p = sized (\n -> try n (2 * n))
--   where
--     try m n
--       | m > n = exact Nothing
--       | otherwise = do
--           x <- comap _ (resize m g)
--           if p x then exact (Just x) else try (m + 1) n

-- -- Interpretations
-- derivative :: FR b a -> String -> Maybe (FR b a)
-- derivative (Return _) _ = Nothing
-- derivative (Bind r f) s = do
--   x <- drefl r
--   pure (x >>= f)
--   where
--     drefl :: Refl b a -> Maybe (FR b a)
--     drefl (Pick xs) = do
--       (_, _, x) <- find ((== Just s) . view _2) xs
--       pure x
--     drefl (Lmap g x) = lmap g <$> drefl x
--     drefl (Prune x) = internaliseMaybe <$> drefl x

gen :: FR b a -> Gen a
gen = interp
  where
    interpR :: Refl b a -> Gen a
    interpR (Pick xs) = QC.frequency [(w, interp x) | (w, _, x) <- xs]
    interpR (Lmap _ x) = interpR x
    interpR (Prune x) = interpR x
    interpR (ChooseInteger (lo, hi)) = QC.chooseInteger (lo, hi)
    interpR GetSize = QC.getSize
    interpR (Resize n x) = QC.resize n (interpR x)

    interp :: FR b a -> Gen a
    interp (Return x) = pure x
    interp (Bind x f) = interpR x >>= interp . f

check :: FR a a -> a -> Bool
check g v = isJust (interp g v Nothing)
  where
    interp :: FR b a -> b -> Maybe Int -> Maybe a
    interp (Return x) _ _ = return x
    interp (Bind x f) b s = interpR x b s >>= \y -> interp (f y) b s

    interpR :: Refl b a -> b -> Maybe Int -> Maybe a
    interpR (Pick xs) b s = (\case [] -> Nothing; l -> Just (last l)) (catMaybes [interp x b s | (_, _, x) <- xs])
    interpR (Lmap f x) b s = interpR x (f b) s
    interpR (Prune x) b s = b >>= \b' -> interpR x b' s
    interpR (ChooseInteger (lo, hi)) b _
      | lo <= b && b <= hi = pure b
      | otherwise = Nothing
    interpR GetSize _ (Just s) = return s
    interpR GetSize _ Nothing = pure 30
    interpR (Resize s x) b _ = interpR x b (Just s)

weighted :: FR b a -> (String -> Int) -> Gen a
weighted = aux
  where
    interpR :: Refl b a -> (String -> Int) -> Gen a
    interpR (Pick xs) w = QC.frequency (map (\(_, s, x) -> (maybe 1 w s, aux x w)) xs)
    interpR (ChooseInteger (lo, hi)) _ = QC.chooseInteger (lo, hi)
    interpR (Lmap _ x) w = interpR x w
    interpR (Prune x) w = interpR x w
    interpR GetSize _ = QC.getSize
    interpR (Resize n x) w = QC.resize n (interpR x w)

    aux :: FR b a -> (String -> Int) -> Gen a
    aux (Return x) _ = pure x
    aux (Bind x f) w = do
      y <- interpR x w
      aux (f y) w

weights :: FR a a -> [a] -> [(String, Int)]
weights g =
  map (\xs -> (head xs, length xs))
    . group
    . sort
    . head
    . concatMap (unparse g)

byExample :: FR a a -> [a] -> Gen a
byExample g xs = weighted g (\s -> fromMaybe 0 (lookup s (weights g xs)))

enum :: FR b a -> [a]
enum = observeAll . aux
  where
    interpR :: Refl b a -> Logic a
    interpR (Pick xs) = asum (map (aux . view _3) xs)
    interpR (ChooseInteger (lo, hi)) = asum (map pure [lo .. hi])
    interpR (Lmap _ x) = interpR x
    interpR (Prune x) = interpR x
    interpR GetSize = error "enum: GetSize"
    interpR (Resize {}) = error "enum: Resize"

    aux :: FR b a -> Logic a
    aux (Return x) = pure x
    aux (Bind x f) =
      interpR x >>- \y ->
        aux (f y)

regen :: FR b a -> Bits -> Maybe a
regen rg cs = listToMaybe (fst <$> aux rg (unBits cs) Nothing)
  where
    interpR :: Refl b a -> [Bool] -> Maybe Int -> [(a, [Bool])]
    interpR (Pick xs) b s = do
      let numBits = ceiling (logBase 2 (fromIntegral (length xs) :: Double))
      (bs, (_, _, x)) <- zip (listBits numBits) xs
      guard (unBits bs == take numBits b)
      (y, bs') <- aux x (drop numBits b) s
      pure (y, bs')
    interpR (ChooseInteger (lo, hi)) b _ = maybeToList $ bitsToInteger (lo, hi) b
    interpR (Lmap _ x) b s = interpR x b s
    interpR (Prune x) b s = interpR x b s
    interpR GetSize b Nothing = pure (30, b)
    interpR GetSize b (Just n) = pure (n, b)
    interpR (Resize n x) b _ = interpR x b (Just n)

    aux :: FR b a -> [Bool] -> Maybe Int -> [(a, [Bool])]
    aux (Return x) b _ = pure (x, b)
    aux (Bind mx f) b s = do
      (x, b') <- interpR mx b s
      aux (f x) b' s

parse :: FR b a -> [String] -> [(a, [String])]
parse g v = aux g v Nothing
  where
    search [] = []
    search xs = (: []) . minimumBy (comparing (length . snd)) $ xs
    -- search = take 1

    interpR :: Refl b a -> [String] -> Maybe Int -> [(a, [String])]
    interpR (Pick xs) st sz = search $ do
      (_, ms, x) <- xs
      case ms of
        Nothing -> aux x st sz
        Just s -> do
          case st of
            s' : ss -> do
              guard (s == s')
              aux x ss sz
            _ -> []
    interpR (ChooseInteger (lo, hi)) s _ = (,s) <$> [lo .. hi]
    interpR (Lmap _ x) b sz = interpR x b sz
    interpR (Prune x) b sz = interpR x b sz
    interpR GetSize b (Just sz) = pure (sz, b)
    interpR GetSize b _ = pure (30, b)
    interpR (Resize sz x) b _ = interpR x b (Just sz)

    aux :: FR b a -> [String] -> Maybe Int -> [(a, [String])]
    aux (Return x) b _ = pure (x, b)
    aux (Bind mx f) b s = do
      (x, b') <- interpR mx b s
      aux (f x) b' s

choices :: FR a a -> a -> [BitTree]
choices rg v = snd <$> aux rg v Nothing
  where
    interpR :: Refl b a -> b -> Maybe Int -> [(a, BitTree)]
    interpR (Pick xs) b s = do
      let numBits = ceiling (logBase 2 (fromIntegral (length xs) :: Double))
      (bs, (_, _, x)) <- zip (listBits numBits) xs
      (y, bs') <- aux x b s
      pure (y, foldr ((+++) . bit) BitTree.empty (unBits bs) +++ bs')
    interpR (ChooseInteger (lo, hi)) b _ =
      [(b, tree . map Bit $ integerToBits (lo, hi) b) | not (b < lo || b > hi)]
    interpR (Lmap f x) b s = interpR x (f b) s
    interpR (Prune x) b s = case b of
      Nothing -> []
      Just a -> interpR x a s
    interpR GetSize _ Nothing = pure (30, BitTree.empty)
    interpR GetSize _ (Just n) = pure (n, BitTree.empty)
    interpR (Resize n x) b _ = interpR x b (Just n)

    aux :: FR b a -> b -> Maybe Int -> [(a, BitTree)]
    aux (Return x) _ _ = pure (x, BitTree.empty)
    aux (Bind mx f) b s = do
      (x, cs) <- interpR mx b s
      (y, cs') <- aux (f x) b s
      pure (y, draw cs +++ cs')

unparse :: FR a a -> a -> [[String]]
unparse rg v = snd <$> aux rg v
  where
    interpR :: Refl b a -> b -> [(a, [String])]
    interpR (Pick xs) b = take 1 . reverse $ do
      (_, ms, x) <- xs
      case ms of
        Nothing -> aux x b
        Just s -> second (s :) <$> aux x b
    interpR (ChooseInteger _) b = pure (b, [])
    interpR (Lmap f x) b = interpR x (f b)
    interpR (Prune x) b = case b of
      Nothing -> []
      Just a -> interpR x a
    interpR GetSize _ = error "unparse: GetSize"
    interpR (Resize {}) _ = error "unparse: Resize"

    aux :: FR b a -> b -> [(a, [String])]
    aux (Return x) _ = pure (x, [])
    aux (Bind mx f) b = do
      (x, cs) <- interpR mx b
      (y, cs') <- aux (f x) b
      pure (y, cs ++ cs')

complete :: FR a a -> a -> IO (Maybe a)
complete g v = do
  aux g v >>= \case
    [] -> pure Nothing
    xs -> Just <$> QC.generate (QC.elements xs)
  where
    interpR :: Refl b a -> b -> IO [a]
    interpR (Pick xs) b = concat <$> mapM (\(_, _, x) -> aux x b) xs
    interpR (ChooseInteger (lo, hi)) _ = pure [lo .. hi] -- TODO: Check on this
    interpR (Lmap f x) b = do
      catch
        (evaluate (f b) >>= \a -> interpR x a)
        (\(_ :: SomeException) -> (: []) <$> QC.generate (gen (Bind x Return)))
    interpR (Prune x) b = case b of
      Nothing -> pure []
      Just a -> interpR x a
    interpR GetSize _ = error "complete: GetSize"
    interpR (Resize {}) _ = error "complete: Resize"

    aux :: FR b a -> b -> IO [a]
    aux (Return x) _ = pure [x]
    aux (Bind mx f) b = do
      xs <- interpR mx b
      concat <$> mapM (\x -> aux (f x) b) xs

-- Examples

data Tree = Leaf | Node Tree Int Tree
  deriving (Show, Eq, Ord)

makePrisms ''Tree

height :: Tree -> Int
height Leaf = 0
height (Node l _ r) = 1 + max (height l) (height r)

unbalanced :: Tree -> Bool
unbalanced Leaf = False
unbalanced (Node l _ r) =
  unbalanced l || unbalanced r || abs (height l - height r) > 1

nodeValue :: Tree -> Maybe Int
nodeValue (Node _ x _) = Just x
nodeValue _ = Nothing

nodeLeft :: Tree -> Maybe Tree
nodeLeft (Node l _ _) = Just l
nodeLeft _ = Nothing

nodeRight :: Tree -> Maybe Tree
nodeRight (Node _ _ r) = Just r
nodeRight _ = Nothing

weirdTree :: FR Tree Tree
weirdTree = aux (10 :: Int)
  where
    aux n
      | n == 0 = exact Leaf
      | otherwise = do
          oneof
            [ exact Leaf,
              do
                x <- comap nodeValue (choose (1, 10))
                l <- comap nodeLeft (aux (n - 1))
                r <- comap nodeRight (aux (n - 1))
                pure (Node l x r),
              exact (Node Leaf 2 Leaf)
            ]

bstFwd :: FR Void Tree
bstFwd = aux (1, 10)
  where
    aux (lo, hi)
      | lo > hi = return Leaf
      | otherwise = do
          oneof
            [ return Leaf,
              do
                x <- fwd (choose (lo, hi))
                l <- fwd (aux (lo, x - 1))
                r <- fwd (aux (x + 1, hi))
                return (Node l x r)
            ]

bst :: Reflective Tree
bst = aux (1, 10)
  where
    aux (lo, hi)
      | lo > hi = exact Leaf
      | otherwise = do
          labelled
            [ ( "leaf",
                exact Leaf
              ),
              ( "node",
                do
                  x <- tryFocus (_Node . _2) (choose (lo, hi))
                  l <- tryFocus (_Node . _1) (aux (lo, x - 1))
                  r <- tryFocus (_Node . _3) (aux (x + 1, hi))
                  exact (Node l x r)
              )
            ]

hypoTree :: FR Tree Tree
hypoTree =
  oneof
    [ exact Leaf,
      do
        l <- comap nodeLeft hypoTree
        r <- comap nodeRight hypoTree
        exact (Node l 0 r)
    ]

data Expr
  = Num Int
  | Add Expr Expr
  | Mul Expr Expr
  deriving (Show, Eq, Ord)

makePrisms ''Expr

expression :: FR Expr Expr
expression = expr (10 :: Int)
  where
    expr n
      | n <= 1 = term n
      | otherwise =
          oneof
            [ do
                x <- tryFocus (_Add . _1) (term (n `div` 2))
                y <- token "+" *> tryFocus (_Add . _2) (expr (n `div` 2))
                pure (Add x y),
              term n
            ]
    term n
      | n <= 1 = factor n
      | otherwise =
          oneof
            [ do
                x <- tryFocus (_Mul . _1) (factor (n `div` 2))
                y <- token "*" *> tryFocus (_Mul . _2) (term (n `div` 2))
                pure (Mul x y),
              factor n
            ]
    factor n
      | n <= 1 = Num <$> tryFocus _Num (choose (1, 10))
      | otherwise =
          oneof
            [ Num <$> tryFocus _Num (choose (1, 10)),
              token "(" *> expr (n - 1) <* token ")"
            ]
    token s = labelled [(s, pure ())]

shrink :: (a -> Bool) -> FR a a -> a -> a
shrink p g =
  fromMaybe (error "shrink: no solution")
    . regen g
    . flatten
    . head
    . applyShrinker swapBits
    . applyShrinker zeroDraws
    . take 1
    . choices g
  where
    applyShrinker :: (BitTree -> [BitTree]) -> [BitTree] -> [BitTree]
    applyShrinker s !ts =
      let ts' = take 1 . filter (any p . regen g . flatten) . sort . concatMap s $ ts
       in if null ts' || ts' == ts then ts else applyShrinker s ts'

validate :: Show a => FR a a -> IO ()
validate g =
  quickCheckWith
    (stdArgs {maxSuccess = 1000, maxSize = 30})
    (forAll (gen g) (check g))

validateChoice :: (Eq a, Show a) => FR a a -> IO ()
validateChoice g =
  quickCheckWith
    (stdArgs {maxSuccess = 1000})
    (forAll (gen g) $ \x -> all ((== Just x) . regen g . flatten) (choices g x))

validateParse :: (Eq a, Show a) => FR a a -> IO ()
validateParse g =
  quickCheckWith
    (stdArgs {maxSuccess = 10000})
    (forAll (gen g) $ \x -> all ((== x) . fst . head . filter (null . snd) . parse g) (unparse g x))

main :: IO ()
main = do
  print =<< QC.generate (gen weirdTree)
  print =<< QC.generate (gen bstFwd)
  let ss = head . nub $ unparse bst (Node Leaf 1 (Node Leaf 2 Leaf))
  print ss
  print (parse bst ss)
  let n l = Node l 0
  print $ (map flatten . choices hypoTree) (n (n Leaf (n (n Leaf (n (n Leaf Leaf) Leaf)) Leaf)) (n (n Leaf (n (n Leaf (n Leaf Leaf)) (n Leaf Leaf))) Leaf))
  print $ (map flatten . choices hypoTree) (n Leaf (n (n Leaf (n (n Leaf (n Leaf Leaf)) (n Leaf Leaf))) Leaf))
  print $ choices hypoTree (n Leaf (n (n Leaf Leaf) Leaf))
  print $ (map flatten . choices hypoTree) (n Leaf (n Leaf (n Leaf Leaf)))
  print $ choices hypoTree (n Leaf (n Leaf (n Leaf Leaf)))
  print $ choices bst (Node (Node Leaf 1 Leaf) 3 (Node Leaf 5 Leaf))
  print $ map fst $ filter (null . snd) $ parse expression (words "( 1 + 2 ) * ( 3 + 3 * 4 )")
  print $ take 3 $ map concat $ unparse expression (Mul (Add (Num 1) (Num 2)) (Num 3))
  let _hole_ = undefined
  print =<< complete bst (Node _hole_ 5 _hole_)
  print =<< complete bst (Node (Node _hole_ 2 Leaf) 5 (Node _hole_ 7 _hole_))
  print =<< QC.generate (byExample expression [Mul (Num 1) (Num 2), Mul (Num 3) (Num 4)])

  let t = n (n Leaf (n (n Leaf (n (n Leaf Leaf) Leaf)) Leaf)) (n (n Leaf (n (n Leaf (n Leaf Leaf)) (n Leaf Leaf))) Leaf)
  print (choices hypoTree t)
  print $ shrink unbalanced hypoTree t