{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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

import Choices
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
    subChoices,
    swapBits,
    tree,
    zeroDraws,
    (+++),
  )
import qualified Choices
import Control.Applicative (empty)
import Control.Exception (SomeException)
import Control.Lens (Getting, makePrisms, over, preview, view, _1, _2, _3, _head, _tail)
import Control.Monad (ap, guard, (>=>))
import Control.Monad.Logic (Logic, MonadLogic ((>>-)), observeAll)
import Data.Bifunctor (Bifunctor (..))
import Data.Char (chr, ord)
import Data.Foldable (asum)
import Data.List (group, minimumBy, sort, transpose)
import Data.Maybe (fromMaybe, listToMaybe, mapMaybe, maybeToList)
import Data.Monoid (First)
import Data.Ord (comparing)
import Data.Void (Void)
import GHC.IO (catch, evaluate)
import Test.QuickCheck (Args (maxSize, maxSuccess), Gen, forAll, quickCheckWith, stdArgs)
import qualified Test.QuickCheck as QC

-- Core Definitions

data Freer f a where
  Return :: a -> Freer f a
  Bind :: f a -> (a -> Freer f c) -> Freer f c

type Choice = Maybe String

type Weight = Int

data R b a where
  Pick :: [(Weight, Choice, Reflective b a)] -> R b a
  Lmap :: (c -> d) -> R d a -> R c a
  Prune :: R b a -> R (Maybe b) a
  ChooseInteger :: (Integer, Integer) -> R Integer Integer
  GetSize :: R b Int
  Resize :: Int -> R b a -> R b a

type Reflective b = Freer (R b)

-- Typeclass Instances Combinators

instance Functor (Reflective b) where
  fmap f (Return x) = Return (f x)
  fmap f (Bind u g) = Bind u (fmap f . g)

instance Applicative (Reflective b) where
  pure = return
  (<*>) = ap

instance Monad (Reflective b) where
  return = Return
  Return x >>= f = f x
  Bind u g >>= f = Bind u (g >=> f)

dimap :: (c -> d) -> (a -> b) -> Reflective d a -> Reflective c b
dimap _ g (Return a) = Return (g a)
dimap f g (Bind x h) = Bind (Lmap f x) (dimap f g . h)

lmap :: (c -> d) -> Reflective d a -> Reflective c a
lmap f = dimap f id

prune :: Reflective b a -> Reflective (Maybe b) a
prune (Return a) = Return a
prune (Bind x f) = Bind (Prune x) (prune . f)

comap :: (a -> Maybe b) -> Reflective b v -> Reflective a v
comap f = lmap f . prune

getbits :: Int -> Reflective b Int
getbits w =
  Bind
    ( Pick
        [(1, Just (show (bitsToInt i)), pure (bitsToInt i)) | i <- listBits w]
    )
    Return

pick :: [(Int, String, Reflective b a)] -> Reflective b a
pick xs = Bind (Pick (map (over _2 Just) xs)) Return

frequency :: [(Int, Reflective b a)] -> Reflective b a
frequency xs = Bind (Pick (map (\(w, g) -> (w, Nothing, g)) xs)) Return

labelled :: [(String, Reflective b a)] -> Reflective b a
labelled xs = Bind (Pick (map (\(s, g) -> (1, Just s, g)) xs)) Return

oneof :: [Reflective b a] -> Reflective b a
oneof xs = Bind (Pick (map (1,Nothing,) xs)) Return

exact :: Eq v => v -> Reflective v v
exact x = comap (\y -> if y == x then Just y else Nothing) $ oneof [pure x]

choose :: (Int, Int) -> Reflective Int Int
choose (lo, hi) = labelled [(show i, exact i) | i <- [lo .. hi]]

chooseInteger :: (Integer, Integer) -> Reflective Integer Integer
chooseInteger p = Bind (ChooseInteger p) Return

integer :: Reflective Int Int
integer = sized $ \n -> labelled [(show i, exact i) | i <- concat (transpose [[0 .. n], reverse [-n .. -1]])]

char :: Reflective Char Char
char = sized $ \n -> labelled [(show i, exact (chr i)) | i <- [ord 'a' .. ord 'a' + n]]

alphaNum :: Reflective Char Char
alphaNum = labelled [(show c, exact c) | c <- ['a', 'b', 'c', '1', '2', '3']]

bool :: Reflective Bool Bool
bool = oneof [exact True, exact False]

vectorOf :: Eq a => Int -> Reflective a a -> Reflective [a] [a]
vectorOf 0 _ = exact []
vectorOf n g = do
  x <- focus _head g
  xs <- focus _tail (vectorOf (n - 1) g)
  exact (x : xs)

listOf :: Eq a => Reflective a a -> Reflective [a] [a]
listOf g = sized aux
  where
    aux 0 = exact []
    aux n =
      frequency
        [ (1, exact []),
          ( n,
            do
              x <- focus _head g
              xs <- focus _tail (aux (n - 1))
              exact (x : xs)
          )
        ]

nonEmptyListOf :: Eq a => Reflective a a -> Reflective [a] [a]
nonEmptyListOf g = do
  x <- focus _head g
  xs <- focus _tail (sized aux)
  exact (x : xs)
  where
    aux 0 = exact []
    aux n =
      frequency
        [ (1, exact []),
          ( n,
            do
              x <- focus _head g
              xs <- focus _tail (aux (n - 1))
              exact (x : xs)
          )
        ]

fwd :: Reflective c a -> Reflective Void a
fwd = lmap (\case {})

focus :: Getting (First u') s u' -> Reflective u' v -> Reflective s v
focus = comap . preview

resize :: Int -> Reflective b a -> Reflective b a
resize _ (Return x) = Return x
resize w (Bind x f) = Bind (Resize w x) (resize w . f)

sized :: (Int -> Reflective b a) -> Reflective b a
sized = Bind GetSize

-- Interpretations

gen :: forall d c. Reflective d c -> Gen c
gen = interp
  where
    interp :: forall b a. Reflective b a -> Gen a
    interp (Return x) = pure x
    interp (Bind r f) = interpR r >>= interp . f

    interpR :: forall b a. R b a -> Gen a
    interpR (Pick xs) = QC.frequency [(w, gen x) | (w, _, x) <- xs]
    interpR (Lmap _ x) = interpR x
    interpR (Prune x) = interpR x
    interpR (ChooseInteger (lo, hi)) = QC.chooseInteger (lo, hi)
    interpR GetSize = QC.getSize
    interpR (Resize n x) = QC.resize n (interpR x)

checkClean :: Reflective a a -> a -> Bool
checkClean g v = (not . null) (interp g v)
  where
    interp :: Reflective b a -> b -> [a]
    interp (Return x) _ = return x
    interp (Bind x f) b = interpR x b >>= \y -> interp (f y) b

    interpR :: R b a -> b -> [a]
    interpR (Pick xs) b = xs >>= (\(_, _, x) -> interp x b)
    interpR (Lmap f x) b = interpR x (f b)
    interpR (Prune x) b = maybeToList b >>= \b' -> interpR x b'
    interpR _ _ = error "interpR: clean"

check :: Reflective a a -> a -> Bool
check g v = (not . null) (interp g v Nothing)
  where
    interp :: Reflective b a -> b -> Maybe Int -> [a]
    interp (Return x) _ _ = return x
    interp (Bind x f) b s = interpR x b s >>= \y -> interp (f y) b s

    interpR :: R b a -> b -> Maybe Int -> [a]
    interpR (Pick xs) b s = concat [interp x b s | (_, _, x) <- xs]
    interpR (Lmap f x) b s = interpR x (f b) s
    interpR (Prune x) b s = maybeToList b >>= \b' -> interpR x b' s
    interpR (ChooseInteger (lo, hi)) b _
      | lo <= b && b <= hi = pure b
      | otherwise = empty
    interpR GetSize _ (Just s) = return s
    interpR GetSize _ Nothing = pure 30
    interpR (Resize s x) b _ = interpR x b (Just s)

weighted :: Reflective b a -> Bool -> (String -> Int) -> Gen a
weighted g inv ws = aux g ws 100
  where
    interpR :: R b a -> (String -> Int) -> Int -> Gen a
    interpR (Pick xs) w 0 = aux (view _3 (head xs)) w 0
    interpR (Pick xs) w s =
      case filter ((> 0) . fst) . maybeInv $ map (\(_, l, x) -> (maybe 1 w l, aux x w (s - 1))) xs of
        [] -> QC.oneof (map (\(_, _, x) -> aux x w (s - 1)) xs)
        gs -> QC.frequency gs
    interpR (ChooseInteger (lo, hi)) _ _ = QC.chooseInteger (lo, hi)
    interpR (Lmap _ x) w s = interpR x w s
    interpR (Prune x) w s = interpR x w s
    interpR GetSize _ _ = QC.getSize
    interpR (Resize n x) w s = QC.resize n (interpR x w s)

    maybeInv :: [(Int, d)] -> [(Int, d)]
    maybeInv x =
      if inv
        then
          let m = maximum (map fst x)
           in map (first (m -)) x
        else x

    aux :: Reflective b a -> (String -> Int) -> Int -> Gen a
    aux (Return x) _ _ = pure x
    aux (Bind x f) w s = do
      y <- interpR x w s
      aux (f y) w s

weights :: Reflective a a -> [a] -> [(String, Int)]
weights g =
  map (\xs -> (head xs, length xs))
    . group
    . sort
    . concat
    . mapMaybe (unparse g)

byExample :: Reflective a a -> [a] -> Gen a
byExample g xs = weighted g False (\s -> fromMaybe 0 (lookup s (weights g xs)))

byExampleInv :: Reflective a a -> [a] -> Gen a
byExampleInv g xs = weighted g True (\s -> fromMaybe 0 (lookup s (weights g xs)))

enum :: Reflective b a -> [a]
enum = observeAll . aux
  where
    interpR :: R b a -> Logic a
    interpR (Pick xs) = asum (map (aux . view _3) xs)
    interpR (ChooseInteger (lo, hi)) = asum (map pure [lo .. hi])
    interpR (Lmap _ x) = interpR x
    interpR (Prune x) = interpR x
    interpR GetSize = error "enum: GetSize"
    interpR (Resize {}) = error "enum: Resize"

    aux :: Reflective b a -> Logic a
    aux (Return x) = pure x
    aux (Bind x f) =
      interpR x >>- \y ->
        aux (f y)

regen :: Reflective b a -> Bits -> Maybe a
regen rg cs = listToMaybe (fst <$> aux rg (unBits cs) Nothing)
  where
    interpR :: R b a -> [Bool] -> Maybe Int -> [(a, [Bool])]
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

    aux :: Reflective b a -> [Bool] -> Maybe Int -> [(a, [Bool])]
    aux (Return x) b _ = pure (x, b)
    aux (Bind mx f) b s = do
      (x, b') <- interpR mx b s
      aux (f x) b' s

parse :: Reflective b a -> [String] -> [(a, [String])]
parse g v = aux g v Nothing
  where
    search [] = []
    search xs = (: []) . minimumBy (comparing (length . snd)) $ xs
    -- search = take 1

    interpR :: R b a -> [String] -> Maybe Int -> [(a, [String])]
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

    aux :: Reflective b a -> [String] -> Maybe Int -> [(a, [String])]
    aux (Return x) b _ = pure (x, b)
    aux (Bind mx f) b s = do
      (x, b') <- interpR mx b s
      aux (f x) b' s

choices :: Reflective a a -> a -> [BitTree]
choices rg v = snd <$> aux rg v Nothing
  where
    interpR :: R b a -> b -> Maybe Int -> [(a, BitTree)]
    interpR (Pick xs) b s = do
      let numBits = ceiling (logBase 2 (fromIntegral (length xs) :: Double))
      (bs, (_, _, x)) <- zip (listBits numBits) xs
      (y, bs') <- aux x b s
      pure (y, foldr ((+++) . bit) Choices.empty (unBits bs) +++ bs')
    interpR (ChooseInteger (lo, hi)) b _ =
      [(b, tree . map Bit $ integerToBits (lo, hi) b) | not (b < lo || b > hi)]
    interpR (Lmap f x) b s = interpR x (f b) s
    interpR (Prune x) b s = case b of
      Nothing -> []
      Just a -> interpR x a s
    interpR GetSize _ Nothing = pure (30, Choices.empty)
    interpR GetSize _ (Just n) = pure (n, Choices.empty)
    interpR (Resize n x) b _ = interpR x b (Just n)

    aux :: Reflective b a -> b -> Maybe Int -> [(a, BitTree)]
    aux (Return x) _ _ = pure (x, Choices.empty)
    aux (Bind mx f) b s = do
      (x, cs) <- interpR mx b s
      (y, cs') <- aux (f x) b s
      pure (y, draw cs +++ cs')

unparse :: Reflective a a -> a -> Maybe [String]
unparse rg v = listToMaybe (snd <$> aux rg v Nothing)
  where
    interpR :: R b a -> b -> Maybe Int -> [(a, [String])]
    interpR (Pick xs) b s = do
      (_, ms, x) <- xs
      case ms of
        Nothing -> aux x b s
        Just l -> second (l :) <$> aux x b s
    interpR (ChooseInteger _) b _ = pure (b, [])
    interpR (Lmap f x) b s = interpR x (f b) s
    interpR (Prune x) b s = case b of
      Nothing -> []
      Just a -> interpR x a s
    interpR GetSize _ Nothing = pure (30, [])
    interpR GetSize _ (Just n) = pure (n, [])
    interpR (Resize n r) b _ = interpR r b (Just n)

    aux :: Reflective b a -> b -> Maybe Int -> [(a, [String])]
    aux (Return x) _ _ = pure (x, [])
    aux (Bind mx f) b s = do
      (x, cs) <- interpR mx b s
      (y, cs') <- aux (f x) b s
      pure (y, cs ++ cs')

complete :: Reflective a a -> a -> IO (Maybe a)
complete g v = do
  aux g v >>= \case
    [] -> pure Nothing
    xs -> Just <$> QC.generate (QC.elements xs)
  where
    interpR :: R b a -> b -> IO [a]
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

    aux :: Reflective b a -> b -> IO [a]
    aux (Return x) _ = pure [x]
    aux (Bind mx f) b = do
      xs <- interpR mx b
      concat <$> mapM (\x -> aux (f x) b) xs

-- Other Functions

shrink :: (a -> Bool) -> Reflective a a -> a -> a
shrink p g =
  fromMaybe (error "shrink: no solution")
    . regen g
    . flatten
    . head
    . applyShrinker swapBits
    . applyShrinker zeroDraws
    . applyShrinker subChoices
    . take 1
    . choices g
  where
    applyShrinker :: (BitTree -> [BitTree]) -> [BitTree] -> [BitTree]
    applyShrinker s !ts =
      let ts' = take 1 . filter (any p . regen g . flatten) . sort . concatMap s $ ts
       in if null ts' || ts' == ts then ts else applyShrinker s ts'

validate :: Show a => Reflective a a -> IO ()
validate g =
  quickCheckWith
    (stdArgs {maxSuccess = 1000, maxSize = 30})
    (forAll (gen g) (check g))

validateChoice :: (Eq a, Show a) => Reflective a a -> IO ()
validateChoice g =
  quickCheckWith
    (stdArgs {maxSuccess = 1000})
    (forAll (gen g) $ \x -> all ((== Just x) . regen g . flatten) (choices g x))

validateParse :: (Eq a, Show a) => Reflective a a -> IO ()
validateParse g =
  quickCheckWith
    (stdArgs {maxSuccess = 10000})
    (forAll (gen g) $ \x -> all ((== x) . fst . head . filter (null . snd) . parse g) (unparse g x))

-- Examples

data Tree = Leaf | Node Tree Int Tree
  deriving (Show, Eq, Ord)

makePrisms ''Tree

nodeValue :: Tree -> Maybe Int
nodeValue (Node _ x _) = Just x
nodeValue _ = Nothing

nodeLeft :: Tree -> Maybe Tree
nodeLeft (Node l _ _) = Just l
nodeLeft _ = Nothing

nodeRight :: Tree -> Maybe Tree
nodeRight (Node _ _ r) = Just r
nodeRight _ = Nothing

bstFwd :: Reflective Void Tree
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

bst :: Reflective Tree Tree
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
                  x <- focus (_Node . _2) (choose (lo, hi))
                  l <- focus (_Node . _1) (aux (lo, x - 1))
                  r <- focus (_Node . _3) (aux (x + 1, hi))
                  exact (Node l x r)
              )
            ]

hypoTree :: Reflective Tree Tree
hypoTree =
  oneof
    [ exact Leaf,
      do
        l <- comap nodeLeft hypoTree
        r <- comap nodeRight hypoTree
        exact (Node l 0 r)
    ]

-- main :: IO ()
-- main = do
--   print =<< QC.generate (gen weirdTree)
--   print =<< QC.generate (gen bstFwd)
--   let ss = fromJust $ unparse bst (Node Leaf 1 (Node Leaf 2 Leaf))
--   print ss
--   print (parse bst ss)
--   let n l = Node l 0
--   print $ (map flatten . choices hypoTree) (n (n Leaf (n (n Leaf (n (n Leaf Leaf) Leaf)) Leaf)) (n (n Leaf (n (n Leaf (n Leaf Leaf)) (n Leaf Leaf))) Leaf))
--   print $ (map flatten . choices hypoTree) (n Leaf (n (n Leaf (n (n Leaf (n Leaf Leaf)) (n Leaf Leaf))) Leaf))
--   print $ choices hypoTree (n Leaf (n (n Leaf Leaf) Leaf))
--   print $ (map flatten . choices hypoTree) (n Leaf (n Leaf (n Leaf Leaf)))
--   print $ choices hypoTree (n Leaf (n Leaf (n Leaf Leaf)))
--   print $ choices bst (Node (Node Leaf 1 Leaf) 3 (Node Leaf 5 Leaf))
--   print $ map fst $ filter (null . snd) $ parse expression (words "( 1 + 2 ) * ( 3 + 3 * 4 )")
--   let _hole_ = undefined
--   print =<< complete bst (Node _hole_ 5 _hole_)
--   print =<< complete bst (Node (Node _hole_ 2 Leaf) 5 (Node _hole_ 7 _hole_))
--   print =<< QC.generate (byExample expression [Mul (Num 1) (Num 2), Mul (Num 3) (Num 4)])

--   let t = n (n Leaf (n (n Leaf (n (n Leaf Leaf) Leaf)) Leaf)) (n (n Leaf (n (n Leaf (n Leaf Leaf)) (n Leaf Leaf))) Leaf)
--   print (choices hypoTree t)
--   print $ shrink unbalanced hypoTree t