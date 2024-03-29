{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use zipWith" #-}
{-# HLINT ignore "Use infix" #-}
{-# HLINT ignore "Use intercalate" #-}

module Examples.Hypothesis.Parser where

import Control.Lens (makePrisms, _1, _2, _3)
import Control.Monad.State
  ( MonadState (state),
    State,
    evalState,
    modify,
  )
import Data.List (intersperse, isPrefixOf, stripPrefix)
import Reflectives (Reflective)
import qualified Reflectives as Reflective
import qualified Interps as Interp
import GHC.Generics (Generic)
import Test.QuickCheck
  ( Arbitrary (..),
    Gen,
    genericShrink,
    suchThat,
  )
import Test.QuickCheck.Arbitrary.Generic (genericArbitrary)
import Prelude hiding (showList)

-- From SmartCheck

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

instance Arbitrary Lang where
  arbitrary = genericArbitrary
  shrink = genericShrink

instance Arbitrary Mod where
  arbitrary = genericArbitrary
  shrink = genericShrink

instance Arbitrary Var where
  arbitrary = genericArbitrary

instance Arbitrary Func where
  arbitrary = genericArbitrary
  shrink = genericShrink

instance Arbitrary Stmt where
  arbitrary = genericArbitrary
  shrink = genericShrink

instance Arbitrary Exp where
  arbitrary = genericArbitrary
  shrink = genericShrink

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

sizeGL :: GenLang -> Int
sizeGL (GL l) = size l

prop_Parse :: Lang -> Bool
prop_Parse e = read' (show' e) == e

prop_ParseGL :: GenLang -> Bool
prop_ParseGL e = read' (show' e) == e

invariant :: a -> Bool
invariant = const True

-- Reflective Generator

reflVar :: Reflective Var Var
reflVar = Var <$> Reflective.focus _Var (Reflective.nonEmptyListOf Reflective.alphaNum)

reflLang :: Reflective Lang Lang
reflLang =
  Lang
    <$> Reflective.focus (_Lang . _1) (Reflective.listOf reflMod)
    <*> Reflective.focus (_Lang . _2) (Reflective.listOf reflFunc)

reflMod :: Reflective Mod Mod
reflMod =
  Mod
    <$> Reflective.focus (_Mod . _1) (Reflective.listOf reflVar)
    <*> Reflective.focus (_Mod . _2) (Reflective.listOf reflVar)

reflFunc :: Reflective Func Func
reflFunc =
  Func
    <$> Reflective.focus (_Func . _1) reflVar
    <*> Reflective.focus (_Func . _2) (Reflective.listOf reflExp)
    <*> Reflective.focus (_Func . _3) (Reflective.listOf reflStmt)

reflStmt :: Reflective Stmt Stmt
reflStmt =
  Reflective.oneof
    [ Assign <$> Reflective.focus (_Assign . _1) reflVar <*> Reflective.focus (_Assign . _2) reflExp,
      Alloc <$> Reflective.focus (_Alloc . _1) reflVar <*> Reflective.focus (_Alloc . _2) reflExp,
      Return <$> Reflective.focus _Return reflExp
    ]

reflExp :: Reflective Exp Exp
reflExp = Reflective.sized go
  where
    go i | i <= 1 = Reflective.oneof [Bool <$> Reflective.focus _Bool Reflective.bool, Int <$> Reflective.focus _Int Reflective.integer]
    go i =
      let g = go (i `div` 2)
       in Reflective.frequency
            [ (1, Bool <$> Reflective.focus _Bool Reflective.bool),
              (1, Int <$> Reflective.focus _Int Reflective.integer),
              (10, Not <$> Reflective.focus _Not (go (i - 1))),
              (100, And <$> Reflective.focus (_And . _1) g <*> Reflective.focus (_And . _2) g),
              (100, Or <$> Reflective.focus (_Or . _1) g <*> Reflective.focus (_Or . _2) g),
              (100, Add <$> Reflective.focus (_Add . _1) g <*> Reflective.focus (_Add . _2) g),
              (100, Sub <$> Reflective.focus (_Sub . _1) g <*> Reflective.focus (_Sub . _2) g),
              (100, Mul <$> Reflective.focus (_Mul . _1) g <*> Reflective.focus (_Mul . _2) g),
              (100, Div <$> Reflective.focus (_Div . _1) g <*> Reflective.focus (_Div . _2) g)
            ]

-- newtype wrapper around Lang, so it can be tested without generic arb instance
newtype GenLang = GL Lang deriving (Show, Read, Generic, Eq)

instance Show' GenLang where
  show' (GL x) = show' x

instance Read' GenLang where
  read' x = GL $ read' x

makePrisms ''GenLang

reflGL :: Reflective GenLang GenLang
reflGL = GL <$> Reflective.focus _GL reflLang

instance Arbitrary GenLang where
  arbitrary = Interp.generate reflGL -- Modified
  shrink = genericShrink
