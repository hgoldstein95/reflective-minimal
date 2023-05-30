{-

Contains STLC example.
(type inference used as bwd annotation)

-}

{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE TemplateHaskell #-}

module Examples.STLC where

import Control.Lens (makePrisms, _1, _2)
import Control.Monad.Reader
import Data.Maybe (isJust, catMaybes)
import GHC.Generics (Generic)
import qualified Interps as Interp
import Reflectives (Reflective)
import qualified Reflectives as R
import Test.QuickCheck (Gen)
import qualified Test.QuickCheck as QC

-- STLC:

data Type = TInt | Fun Type Type
  deriving (Show, Eq, Ord, Generic)

data Expr = Int Int | Plus Expr Expr | Lam Type Expr | Var Int | App Expr Expr
  deriving (Show, Eq, Ord, Generic)

makePrisms ''Type
makePrisms ''Expr

typeOf :: Expr -> Maybe Type
typeOf expr = runReaderT (aux expr) []
  where
    aux :: Expr -> ReaderT [Type] Maybe Type
    aux (Int _) = return TInt
    aux (Plus e1 e2) = do
      TInt <- aux e1
      TInt <- aux e2
      return TInt
    aux (Lam t e) = do
      t' <- local (t :) (aux e)
      return (Fun t t')
    aux (App e1 e2) = do
      (Fun t1 t2) <- aux e1
      t1' <- aux e2
      guard (t1 == t1')
      return t2
    aux (Var n) = do
      ctx <- ask
      if length ctx <= n then lift Nothing else return (ctx !! n)

hasType :: Expr -> Bool
hasType = isJust . typeOf

-- QC generator

genType :: Gen Type
genType = QC.sized aux
  where
    aux 0 = QC.oneof [pure TInt]
    aux n =
      QC.oneof
        [ pure TInt,
          Fun <$> aux (n - 1) <*> aux (n - 1)
        ]

genExpr :: Gen Expr
genExpr = QC.resize 4 genType >>= \t -> QC.sized (aux [] t)
  where
    aux :: [Type] -> Type -> Int -> Gen Expr
    aux ctx TInt 0 =
      QC.oneof $ (Int <$> QC.choose (1, 3)) : catMaybes [genVar ctx TInt]
    aux ctx TInt n =
      QC.oneof $
        [ Int <$> QC.choose (1, 3),
          Plus <$> aux ctx TInt (n - 1) <*> aux ctx TInt (n - 1)
        ]
          ++ catMaybes [genVar ctx TInt]
    aux ctx (Fun t1 t2) n = Lam t1 <$> aux (t1 : ctx) t2 (n-1)

    genVar ::  [Type] -> Type -> Maybe (Gen Expr)
    genVar ctx t =
      case concat (zipWith (\i t' -> [i | t == t']) [0 ..] ctx) of
        [] -> Nothing
        xs -> Just (Var <$> QC.elements xs)

-- reflective generator:

reflType :: Reflective Type Type
reflType = R.sized aux
  where
    aux 0 = R.oneof [R.exact TInt]
    aux n =
      R.oneof
        [ R.exact TInt,
          Fun <$> R.focus (_Fun . _1) (aux (n - 1)) <*> R.focus (_Fun . _2) (aux (n - 1))
        ]

reflExpr :: Reflective Expr Expr
reflExpr = R.comap typeOf (R.resize 4 reflType) >>= \t -> R.sized (aux [] t)
  where
    aux :: [Type] -> Type -> Int -> Reflective Expr Expr
    aux ctx TInt 0 =
      R.oneof $ (Int <$> R.focus _Int (R.choose (1, 3)))
              : catMaybes [relVar ctx TInt]
    aux ctx TInt n =
      R.oneof $
        [ Int <$> R.focus _Int (R.choose (1, 3)),
          Plus <$> aux ctx TInt (n - 1) <*> aux ctx TInt (n - 1)
        ]
          ++ catMaybes [relVar ctx TInt]
    aux ctx (Fun t1 t2) n = Lam t1 <$> aux (t1 : ctx) t2 (n-1)

    relVar ::  [Type] -> Type -> Maybe (Reflective Expr Expr)
    relVar ctx t =
      case concat (zipWith (\i t' -> [i | t == t']) [0 ..] ctx) of
        [] -> Nothing
        xs -> Just (Var <$> R.focus _Var (R.oneof (fmap R.exact xs)))

-- examples:

genExample :: IO Expr
genExample = QC.generate genExpr

reflExampleGen :: IO Expr
reflExampleGen = QC.generate . Interp.generate $ reflExpr
