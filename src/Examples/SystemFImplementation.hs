{-

Contains an implementation of SystemF to be used by SystemFExample.hs

-}

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wall #-}

module Examples.SystemFImplementation where

import Control.Lens (makePrisms)
import Control.Monad (guard)
import Data.Data (Data, Typeable)
import Data.Maybe (isJust)
import GHC.Generics (Generic)
import Text.Printf
  ( FieldFormat (fmtChar, fmtPrecision),
    PrintfArg (formatArg),
    errorBadFormat,
    formatString,
    vFmt,
  )
import Test.QuickCheck ( Arbitrary(..), genericShrink)
import Test.QuickCheck.Arbitrary.Generic (genericArbitrary)

------------------------------------------
-- DEFINITIONS
------------------------------------------

data Type = Base | TBool | Fun Type Type | TVar Int | ForAll Type
  deriving (Eq, Ord, Generic)

instance Arbitrary Type where
  arbitrary = genericArbitrary
  shrink = genericShrink

data Expr
  = Con
  | Var Int
  | Lam Type Expr
  | App Expr Expr
  | Cond Expr Expr Expr
  | BTrue
  | BFalse
  | TLam Expr
  | TApp Expr Type
  deriving (Eq, Ord, Generic)

instance Arbitrary Expr where
  arbitrary = genericArbitrary
  shrink = genericShrink

makePrisms ''Type
makePrisms ''Expr

------------------------------------------
-- PRINTING
------------------------------------------

data Precedence = Outer | Appl | Inner
  deriving (Eq, Ord)

instance Show Type where
  show = showType' Outer

showType' :: Precedence -> Type -> [Char]
showType' _ Base = "()"
showType' _ TBool = "B"
showType' _ (TVar n) = show n
showType' p (ForAll t) = parens p Outer $ "forall " ++ showType' Outer t
showType' p (Fun t1 t2) = parens p Appl $ showType' Inner t1 ++ "->" ++ showType' Appl t2

instance Show Expr where
  show = show' Outer

show' :: Precedence -> Expr -> [Char]
show' _ Con = "#"
show' _ BTrue = "T"
show' _ BFalse = "F"
show' _ (Var x) = show x
show' p (Lam t e) = parens p Outer $ "lam " ++ show t ++ ". " ++ show' Outer e
show' p (TLam e) = parens p Outer $ "Lam. " ++ show' Outer e
show' p (App e1 e2) = parens p Appl $ show' Appl e1 ++ " " ++ show' Inner e2
show' p (TApp e1 t2) = parens p Appl $ show' Appl e1 ++ " [" ++ showType' Outer t2 ++ "]"
show' p (Cond e1 e2 e3) =
  parens p Inner $
    "if "
      ++ show' Outer e1
      ++ " then "
      ++ show' Outer e2
      ++ " else "
      ++ show' Outer e3

parens :: Ord a => a -> a -> [Char] -> [Char]
parens outer inner s = if outer > inner then "(" ++ s ++ ")" else s

------------------------------------------
-- MUTANTS
------------------------------------------

data Mutant
  = NoMutant
  | LiftVar
  | LiftLam
  | LiftTLamA
  | LiftTLamB
  | LiftTApp
  | SubstVar
  | SubstLT
  | SubstApp
  | SubstInTypeNoLift
  | SubstInTypeNoDecr
  | SubstInTypeLT
  | LiftTypeTVar
  | LiftTypeForAll
  | TSubstNoLift
  | TSubstNoIncr
  | AppForgetSubst
  | TAppForgetSubst
  | SubstSwapped
  | SubstNoIncr
  | SubstNoLift
  | SubstInTypeNoIncr
  | SubstNoLiftT
  | LiftTNoIncr
  | CondFalseToTrue
  deriving (Show, Eq, Ord, Enum, Bounded, Data, Typeable)

instance PrintfArg Mutant where
  formatArg x fmt
    | fmtChar (vFmt 's' fmt) == 's' = formatString (show x) (fmt {fmtChar = 's', fmtPrecision = Nothing})
  formatArg _ fmt = errorBadFormat $ fmtChar fmt

mut :: (Eq a, ?mutant :: a) => a -> p -> p -> p
mut m good bad = if m == ?mutant then bad else good

-- TYPECHECKING
------------------------------------------

-- | I can't believe we had to write this
nth :: Int -> [a] -> Maybe a
nth _ [] = Nothing
nth 0 (a : _) = Just a
nth n (_ : as) = nth (n - 1) as

wellFormedType :: Int -> Type -> Bool
wellFormedType _ Base = True
wellFormedType _ TBool = True
wellFormedType ftv (TVar n) = n < ftv && n >= 0
wellFormedType ftv (Fun t1 t2) = wellFormedType ftv t1 && wellFormedType ftv t2
wellFormedType ftv (ForAll t) = wellFormedType (ftv + 1) t

typeOf' :: (?mutant :: Mutant) => Int -> [Type] -> Expr -> Maybe Type
typeOf' _ _ Con = Just Base
typeOf' _ _ BTrue = Just TBool
typeOf' _ _ BFalse = Just TBool
typeOf' ftv c (Lam t e) = guard (wellFormedType ftv t) >> fmap (Fun t) (typeOf' ftv (t : c) e)
typeOf' ftv c (TLam e) = fmap ForAll (typeOf' (ftv + 1) (map (liftType 0) c) e)
typeOf' _ c (Var n) = nth n c
typeOf' ftv c (TApp e t) = do
  t2 <- typeOf' ftv c e
  guard $ wellFormedType ftv t
  case t2 of
    ForAll t2' -> Just $ substInType 0 t t2'
    _ -> Nothing
typeOf' ftv c (App e1 e2) = do
  t12 <- typeOf' ftv c e1
  t1' <- typeOf' ftv c e2
  case t12 of
    Fun t1 t2 -> do
      guard (t1 == t1')
      Just t2
    _ -> Nothing
typeOf' ftv c (Cond e1 e2 e3) = do
  t1 <- typeOf' ftv c e1
  t2 <- typeOf' ftv c e2
  t3 <- typeOf' ftv c e3
  guard (t1 == TBool && t2 == t3)
  Just t2

typeOf :: Expr -> Maybe Type
typeOf = let ?mutant = NoMutant in typeOf' 0 []

------------------------------------------
-- SUBSTITUTION
------------------------------------------

subst :: (?mutant :: Mutant) => Int -> Expr -> Expr -> Expr
subst _ _ Con = Con
subst _ _ BTrue = BTrue
subst _ _ BFalse = BFalse
subst n s (Var x)
  | x == n = s
  | mut SubstLT (x > n) (x < n) = Var $ mut SubstVar (x - 1) x
  | otherwise = Var x
subst n s (Lam t e) = Lam t $ subst (mut SubstNoIncr (n + 1) n) (mut SubstNoLift (lift 0 s) s) e
subst n s (TLam e) = TLam $ subst n (mut SubstNoLiftT (liftTypes 0 s) s) e
subst n s (App e1 e2) = App (mut SubstApp (subst n s e1) (subst n e1 s)) (subst n s e2)
subst n s (TApp e1 t2) = TApp (subst n s e1) t2
subst n s (Cond e1 e2 e3) = Cond (subst n s e1) (subst n s e2) (subst n s e3)

lift :: (?mutant :: Mutant) => Int -> Expr -> Expr
lift _ Con = Con
lift _ BTrue = BTrue
lift _ BFalse = BFalse
lift n (Var x) = Var $ mut LiftVar (if x < n then x else x + 1) (x + 1)
lift n (Lam t e) = Lam t $ lift (mut LiftLam (n + 1) n) e
lift n (TLam e) = TLam $ mut LiftTLamA (lift (mut LiftTLamB n (n + 1)) e) e
lift n (App e1 e2) = App (lift n e1) (lift n e2)
lift n (TApp e1 t2) = TApp (mut LiftTApp (lift n e1) e1) t2
lift n (Cond e1 e2 e3) = Cond (lift n e1) (lift n e2) (lift n e3)

-- Increase type annotations above n
liftTypes :: (?mutant :: Mutant) => Int -> Expr -> Expr
liftTypes _ Con = Con
liftTypes _ BTrue = BTrue
liftTypes _ BFalse = BFalse
liftTypes _ (Var x) = Var x
liftTypes n (Lam t e) = Lam (liftType n t) $ liftTypes n e
liftTypes n (TLam e) = TLam $ liftTypes (mut LiftTNoIncr (n + 1) n) e
liftTypes n (App e1 e2) = App (liftTypes n e1) (liftTypes n e2)
liftTypes n (TApp e1 t2) = TApp (liftTypes n e1) (liftType n t2)
liftTypes n (Cond e1 e2 e3) = Cond (liftTypes n e1) (liftTypes n e2) (liftTypes n e3)

-- Increase (by one) all indices above n in t
liftType :: (?mutant :: Mutant) => Int -> Type -> Type
liftType n (TVar x) = TVar $ mut LiftTypeTVar (if x < n then x else x + 1) (x + 1)
liftType n (ForAll x) = ForAll $ liftType (mut LiftTypeForAll (n + 1) n) x
liftType n (Fun t1 t2) = Fun (liftType n t1) (liftType n t2)
liftType _ x = x

substInType :: (?mutant :: Mutant) => Int -> Type -> Type -> Type
substInType n s (TVar x)
  | x == n = s
  | mut SubstInTypeLT (x > n) (x < n) = TVar $ mut SubstInTypeNoDecr (x - 1) x
  | otherwise = TVar x
substInType n s (ForAll e) = ForAll $ substInType (mut SubstInTypeNoIncr (n + 1) n) (mut SubstInTypeNoLift (liftType 0 s) s) e
substInType n s (Fun t1 t2) = Fun (substInType n s t1) (substInType n s t2)
substInType _ _ x = x

tSubst :: (?mutant :: Mutant) => Int -> Type -> Expr -> Expr
tSubst n s (TLam e) = TLam $ tSubst (mut TSubstNoIncr (n + 1) n) (mut TSubstNoLift (liftType 0 s) s) e
tSubst n s (TApp e t) = TApp (tSubst n s e) (substInType n s t)
tSubst n s (Lam t e) = Lam (substInType n s t) (tSubst n s e)
tSubst n s (App e1 e2) = App (tSubst n s e1) (tSubst n s e2)
tSubst n s (Cond e1 e2 e3) = Cond (tSubst n s e1) (tSubst n s e2) (tSubst n s e3)
tSubst _ _ x = x

------------------------------------------
-- PARALLEL REDUCTION
------------------------------------------

pstep :: (?mutant :: Mutant) => Expr -> Expr
pstep (Lam t e1) =
  let e1' = pstep e1
   in Lam t e1'
pstep (App e1 e2) =
  let e1' = pstep e1
   in let e2' = pstep e2
       in case e1' of
            Lam _ body -> mut AppForgetSubst (mut SubstSwapped (subst 0 e2' body) (subst 0 body e2')) body
            _ -> App e1' e2'
pstep (TLam e1) =
  let e1' = pstep e1
   in TLam e1'
pstep (TApp e1 t) =
  let e1' = pstep e1
   in case e1' of
        TLam body -> mut TAppForgetSubst (tSubst 0 t body) body
        _ -> TApp e1' t
pstep (Cond e1 e2 e3) =
  let e1' = pstep e1
   in let e2' = pstep e2
       in let e3' = pstep e3
           in case e1' of
                BTrue -> e2'
                BFalse -> mut CondFalseToTrue e3' e2'
                _ -> Cond e1' e2' e3'
pstep e = e

peval :: (?mutant :: Mutant) => Expr -> Expr
peval e =
  let e' = pstep e
   in if e' == e then e else peval e'

------------------------------------------
-- LAMBDA TERM UTILITIES
------------------------------------------

wellTyped :: Expr -> Bool
wellTyped = isJust . typeOf

size :: Expr -> Int
size Con = 1
size BTrue = 1
size BFalse = 1
size (Var _) = 1
size (Lam _ e) = 1 + size e
size (App e1 e2) = 1 + size e1 + size e2
size (Cond e1 e2 e3) = 1 + size e1 + size e2 + size e3
size (TApp e _) = 1 + size e
size (TLam e) = 1 + size e
