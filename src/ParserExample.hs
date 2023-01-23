{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use zipWith" #-}
{-# HLINT ignore "Use infix" #-}
{-# HLINT ignore "Use intercalate" #-}

module ParserExample where

--------------------------------------------------------------------------
-- imports

--------------------------------------------------------------------------
-- imports
import Control.Lens (makePrisms, _1, _2, _3)
import Control.Monad.State
import Data.Char (isAlphaNum)
import Data.List (intersperse, isPrefixOf, stripPrefix)
import Freer (FR)
import qualified Freer as FR
import GHC.Generics (Generic)
import Test.QuickCheck
  ( Arbitrary (..),
    Args (chatty),
    Gen,
    Result (Failure, failingTestCase),
    Testable (propertyForAllShrinkShow),
    choose,
    elements,
    frequency,
    genericShrink,
    oneof,
    quickCheckWithResult,
    shrinkNothing,
    stdArgs,
    suchThat,
  )
import Prelude hiding (showList)

data Lang = Lang
  { modules :: [Mod],
    funcs :: [Func]
  }
  deriving (Show, Read, Generic, Eq)

newtype Var = Var String
  deriving (Show, Read, Generic, Eq)

data Mod = Mod
  { imports :: [Var],
    exports :: [Var]
  }
  deriving (Show, Read, Generic, Eq)

data Func = Func
  { fnName :: Var,
    args :: [Exp],
    stmts :: [Stmt]
  }
  deriving (Show, Read, Generic, Eq)

data Stmt
  = Assign Var Exp
  | Alloc Var Exp
  | Return Exp
  deriving (Show, Read, Generic, Eq)

data Exp
  = Int Int
  | Bool Bool
  | Add Exp Exp
  | Sub Exp Exp
  | Mul Exp Exp
  | Div Exp Exp
  | Not Exp
  | And Exp Exp
  | Or Exp Exp
  deriving (Show, Read, Generic, Eq)

makePrisms ''Lang
makePrisms ''Mod
makePrisms ''Func
makePrisms ''Stmt
makePrisms ''Exp
makePrisms ''Var

nonEmpty :: Gen [a] -> Gen [a]
nonEmpty a = suchThat a (not . null)

instance Arbitrary Var where
  arbitrary =
    Var
      <$> suchThat
        arbitrary
        (\s -> all isAlphaNum s && not (null s))

instance Arbitrary Lang where
  arbitrary = Lang <$> nonEmpty arbitrary <*> nonEmpty arbitrary

  -- shrink (Lang m f) = map go (shrink (m, f))
  --   where
  --     go (a, b) = Lang a b
  shrink = genericShrink

instance Arbitrary Mod where
  arbitrary = Mod <$> nonEmpty arbitrary <*> nonEmpty arbitrary

  -- shrink (Mod a b) = map go (shrink (a, b))
  --   where
  --     go (x, y) = Mod x y

  shrink = genericShrink

instance Arbitrary Func where
  arbitrary = Func <$> arbitrary <*> nonEmpty arbitrary <*> nonEmpty arbitrary

  -- shrink (Func f a st) = map go (shrink (a, st))
  --   where
  --     go (x, s) = Func f x s

  shrink = genericShrink

instance Arbitrary Stmt where
  arbitrary = do
    v <- arbitrary
    e <- arbitrary
    let a0 = Assign v e
    let a1 = Alloc v e
    let a2 = Return e
    elements [a0, a1, a2]

  --   shrink stmt = case stmt of
  --     Assign v e -> map (Assign v) (shrink e)
  --     Alloc v e -> map (Alloc v) (shrink e)
  --     Return e -> map Return (shrink e)

  shrink = genericShrink

instance Arbitrary Exp where
  arbitrary = go
    where
      go = go' =<< choose (0 :: Int, 100)
      go' 0 = oneof [Bool <$> arbitrary, Int <$> arbitrary]
      go' i =
        let g = go' =<< choose (0 :: Int, i - 1)
         in frequency
              [ (10, Not <$> g),
                (100, And <$> g <*> g),
                (100, Or <$> g <*> g),
                (100, Add <$> g <*> g),
                (100, Sub <$> g <*> g),
                (100, Mul <$> g <*> g),
                (100, Div <$> g <*> g)
              ]

  -- shrink e = case e of
  --   Int i -> map Int (shrink i)
  --   Bool b -> map Bool (shrink b)
  --   Add e0 e1 -> map (uncurry Add) (zip (shrink e0) (shrink e1))
  --   Sub e0 e1 -> map (uncurry Sub) (zip (shrink e0) (shrink e1))
  --   Mul e0 e1 -> map (uncurry Mul) (zip (shrink e0) (shrink e1))
  --   Div e0 e1 -> map (uncurry Div) (zip (shrink e0) (shrink e1))
  --   Not e0 -> map Not (shrink e0)
  --   And e0 e1 -> map (uncurry And) (zip (shrink e0) (shrink e1))
  --   Or e0 e1 -> map (uncurry Or) (zip (shrink e0) (shrink e1))

  shrink = genericShrink

reflVar :: FR Var Var
reflVar = Var <$> FR.focus _Var (FR.nonEmptyListOf FR.alphaNum)

reflLang :: FR Lang Lang
reflLang =
  Lang
    <$> FR.focus (_Lang . _1) (FR.listOf reflMod)
    <*> FR.focus (_Lang . _2) (FR.listOf reflFunc)

reflMod :: FR Mod Mod
reflMod =
  Mod
    <$> FR.focus (_Mod . _1) (FR.listOf reflVar)
    <*> FR.focus (_Mod . _2) (FR.listOf reflVar)

reflFunc :: FR Func Func
reflFunc =
  Func
    <$> FR.focus (_Func . _1) reflVar
    <*> FR.focus (_Func . _2) (FR.listOf reflExp)
    <*> FR.focus (_Func . _3) (FR.listOf reflStmt)

reflStmt :: FR Stmt Stmt
reflStmt =
  FR.oneof
    [ Assign <$> FR.tryFocus (_Assign . _1) reflVar <*> FR.tryFocus (_Assign . _2) reflExp,
      Alloc <$> FR.tryFocus (_Alloc . _1) reflVar <*> FR.tryFocus (_Alloc . _2) reflExp,
      Return <$> FR.tryFocus _Return reflExp
    ]

reflExp :: FR Exp Exp
reflExp = FR.sized go
  where
    go i | i <= 1 = FR.oneof [Bool <$> FR.tryFocus _Bool FR.bool, Int <$> FR.tryFocus _Int FR.integer]
    go i =
      let g = go (i `div` 2)
       in FR.frequency
            [ (1, Bool <$> FR.tryFocus _Bool FR.bool),
              (1, Int <$> FR.tryFocus _Int FR.integer),
              (i `div` 10, Not <$> FR.tryFocus _Not (go (i - 1))),
              (i, And <$> FR.tryFocus (_And . _1) g <*> FR.tryFocus (_And . _2) g),
              (i, Or <$> FR.tryFocus (_Or . _1) g <*> FR.tryFocus (_Or . _2) g),
              (i, Add <$> FR.tryFocus (_Add . _1) g <*> FR.tryFocus (_Add . _2) g),
              (i, Sub <$> FR.tryFocus (_Sub . _1) g <*> FR.tryFocus (_Sub . _2) g),
              (i, Mul <$> FR.tryFocus (_Mul . _1) g <*> FR.tryFocus (_Mul . _2) g),
              (i, Div <$> FR.tryFocus (_Div . _1) g <*> FR.tryFocus (_Div . _2) g)
            ]

parens :: String -> String
parens a = '(' : a ++ ")"

showList :: Show' a => Char -> [a] -> String
showList sep ls = parens $ concat $ intersperse [sep] $ map show' ls

class Show a => Show' a where
  show' :: a -> String
  show' = show

instance Show' Char

instance Show' Int

instance Show' Bool

instance Show' Lang where
  show' (Lang m f) =
    unwords
      [ "Lang",
        showList ';' m,
        showList ';' f
      ]

instance Show' Mod where
  show' (Mod i e) =
    unwords
      [ "Mod",
        showList ':' i,
        showList ':' e
      ]

instance Show' Func where
  show' (Func f a s) =
    unwords
      [ "Func",
        show' f,
        showList ',' a,
        showList ',' s
      ]

instance Show' Var where
  show' (Var v) = v

instance Show' Stmt where
  show' stmt = unwords $ case stmt of
    Assign v e -> ["Assign", show' v, parens $ show' e]
    Alloc v e -> ["Alloc", show' v, parens $ show' e]
    Return e -> ["Return", parens $ show' e]

instance Show' Exp where
  show' e = unwords $ case e of
    Int i -> ["Int", show' i]
    Bool b -> ["Bool", show' b]
    Add e0 e1 -> ["Add", parens $ show' e0, parens $ show' e1]
    Sub e0 e1 -> ["Sub", parens $ show' e0, parens $ show' e1]
    Mul e0 e1 -> ["Mul", parens $ show' e0, parens $ show' e1]
    Div e0 e1 -> ["Div", parens $ show' e0, parens $ show' e1]
    Not e0 -> ["Not", parens $ show' e0]
    And e0 e1 -> ["And", parens $ show' e0, parens $ show' e1]
    Or e0 e1 -> ["Or", parens $ show' e0, parens $ show' e1]

--------------------------------------------------------------------------------
-- "parser"

class Read a => Read' a where
  read' :: String -> a
  read' = read

instance Read' Lang where
  read' str = run str $ do
    modify (strip "Lang")
    m <- state unparens
    let ms = map read' (fromSeps ';' m)
    f <- state unparens
    let fs = map read' (fromSeps ';' f)
    return (Lang ms fs)

instance Read' Mod where
  read' md = run md $ do
    modify (strip "Mod")
    m <- state unparens
    let i = fromSeps ':' m
    es <- state unparens
    let e = fromSeps ':' es
    return (Mod (map Var i) (map Var e))

instance Read' Func where
  read' f = run f $ do
    modify (strip "Func")
    n <- state (procWord id)
    as <- state unparens
    let ars = map read' (fromSeps ',' as)
    ss <- state unparens
    let sts = map read' (fromSeps ',' ss)
    return (Func (Var n) ars sts)

instance Read' Stmt where
  read' stmt
    | isPrefixOf "Assign" stmt = run stmt $ do
        modify (strip "Assign")
        v <- state (procWord id)
        e <- state (procParens read')
        return (Assign (Var v) e)
    | isPrefixOf "Alloc" stmt = run stmt $ do
        modify (strip "Alloc")
        v <- state (procWord id)
        e <- state (procParens read')
        return (Alloc (Var v) e)
    | isPrefixOf "Return" stmt = run stmt $ do
        modify (strip "Return")
        e <- state (procParens read')
        return (Return e)
    | otherwise = error $ "Couldn't match stmt " ++ stmt

instance Read' Exp where
  read' e
    | isPrefixOf "Int" e = Int (read $ strip "Int" e)
    | isPrefixOf "Bool" e = Bool (read $ strip "Bool" e)
    | isPrefixOf "Add" e = run e $ do
        modify (strip "Add")
        e0 <- state (procParens read')
        e1 <- state (procParens read')
        return (Add e0 e1)
    | isPrefixOf "Sub" e = run e $ do
        modify (strip "Sub")
        e0 <- state (procParens read')
        e1 <- state (procParens read')
        return (Sub e0 e1)
    | isPrefixOf "Mul" e = run e $ do
        modify (strip "Mul")
        e0 <- state (procParens read')
        e1 <- state (procParens read')
        return (Mul e0 e1)
    | isPrefixOf "Div" e = run e $ do
        modify (strip "Div")
        e0 <- state (procParens read')
        e1 <- state (procParens read')
        return (Div e0 e1)
    | isPrefixOf "Not" e = run e $ do
        modify (strip "Not")
        e0 <- state (procParens read')
        return (Not e0)
    | isPrefixOf "And" e = run e $ do
        modify (strip "And")
        e0 <- state (procParens read')
        e1 <- state (procParens read')
        -- XXX Bug!
        return (And e1 e0)
    | isPrefixOf "Or" e = run e $ do
        modify (strip "Or")
        e0 <- state (procParens read')
        e1 <- state (procParens read')
        -- XXX Bug!
        return (And e1 e0)
    | otherwise = error $ "Couldn't match exp " ++ e

--------------------------------------------------------------------------------

run :: s -> State s a -> a
run = flip evalState

strip :: String -> String -> String
strip pre str = case stripPrefix pre str of
  Nothing -> error $ "Couldn't strip " ++ pre ++ " from " ++ str
  Just rst -> if null rst then rst else tail rst

-- Strip the next word.
stripWord :: String -> (String, String)
stripWord str =
  let strs = words str
   in (head strs, unwords (tail strs))

procWord :: (String -> a) -> String -> (a, String)
procWord = runProc stripWord

-- Return a prefix inside parens and the remainder of a string.
unparens :: String -> (String, String)
unparens ('(' : str) = unparens' (1 :: Integer) [] str
  where
    unparens' n s ('(' : r) = unparens' (n + 1) ('(' : s) r
    unparens' n s (')' : r)
      | n == 1 = (reverse s, strip "" r)
      | otherwise = unparens' (n - 1) (')' : s) r
    unparens' _ _ [] = error "End of string reached in unparens"
    unparens' n s (c : r) = unparens' n (c : s) r
unparens str = error $ "Unparsens couldn't parse " ++ str

procParens :: (String -> a) -> String -> (a, String)
procParens = runProc unparens

-- Parse up to a sep
fromSep :: Char -> String -> (String, String)
fromSep sep str =
  let pre = takeWhile (/= sep) str
   in let post = drop (length pre + 1) str
       in (pre, post)

fromSeps :: Char -> String -> [String]
fromSeps _ [] = []
fromSeps sep str =
  let (a, b) = fromSep sep str
   in let as = fromSeps sep b
       in a : as

runProc ::
  (String -> (String, String)) ->
  (String -> a) ->
  String ->
  (a, String)
runProc t f s = let (a, b) = t s in (f a, b)

--------------------------------------------------------------------------------

size :: Lang -> Int
size (Lang m f) = sumit sizem m + sumit sizef f
  where
    sizem (Mod is es) = length is + length es
    sizef (Func _ as sts) = sumit sizee as + sumit sizes sts
    sizes stmt = case stmt of
      Assign _ e -> 1 + sizee e
      Alloc _ e -> 1 + sizee e
      Return e -> 1 + sizee e
    sizee e = case e of
      Int _ -> 1
      Bool _ -> 1
      Add e0 e1 -> 1 + sizee e0 + sizee e1
      Sub e0 e1 -> 1 + sizee e0 + sizee e1
      Mul e0 e1 -> 1 + sizee e0 + sizee e1
      Div e0 e1 -> 1 + sizee e0 + sizee e1
      Not e0 -> 1 + sizee e0
      And e0 e1 -> 1 + sizee e0 + sizee e1
      Or e0 e1 -> 1 + sizee e0 + sizee e1
    sumit sz ls = sum (map sz ls)

prop_Parse :: Lang -> Bool
prop_Parse e = read' (show' e) == e

counterExampleNone :: (Show a, Read a, Arbitrary a) => (a -> Bool) -> IO a
counterExampleNone p =
  quickCheckWithResult (stdArgs {chatty = False}) (propertyForAllShrinkShow arbitrary shrinkNothing ((: []) . show) p) >>= \case
    Failure {failingTestCase = [v]} -> pure (read v)
    _ -> error "counterExampleFR: no counterexample found"

counterExampleGeneric :: (Show a, Read a, Arbitrary a) => (a -> Bool) -> (a -> Bool) -> IO a
counterExampleGeneric p inv =
  quickCheckWithResult (stdArgs {chatty = False}) (propertyForAllShrinkShow arbitrary (filter inv . shrink) ((: []) . show) p) >>= \case
    Failure {failingTestCase = [v]} -> pure (read v)
    _ -> error "counterExampleFR: no counterexample found"

counterExampleFR :: (Eq a, Show a, Read a) => FR a a -> (a -> Bool) -> IO a
counterExampleFR g p =
  quickCheckWithResult (stdArgs {chatty = False}) (propertyForAllShrinkShow (FR.gen g) (\v -> let v' = FR.shrink (not . p) g v in [v' | v /= v']) ((: []) . show) p) >>= \case
    Failure {failingTestCase = [v]} -> pure (read v)
    e -> error $ "counterExampleFR: no counterexample found" ++ show e

average :: [Int] -> Double
average xs = fromIntegral (sum xs) / fromIntegral (length xs)

main :: Int -> IO (Double, Double, Double)
main n = do
  putStr "parser: "
  x <- measure $ counterExampleNone prop_Parse
  y <- measure $ counterExampleGeneric prop_Parse (const True)
  z <- measure $ counterExampleFR reflLang prop_Parse
  pure (x, y, z)
  where
    measure x = do
      xs <- replicateM n x
      pure $ average (size <$> xs)