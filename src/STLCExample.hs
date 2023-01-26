module STLCExample where

import Control.Monad.Reader
import Data.Maybe (catMaybes, isJust)
import Test.QuickCheck (Gen)
import qualified Test.QuickCheck as QC

data Type = TInt | Fun Type Type
  deriving (Show, Eq, Ord)

data Expr = Int Int | Plus Expr Expr | Lam Type Expr | Var Int | App Expr Expr
  deriving (Show, Eq, Ord)

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

genType :: Gen Type
genType = QC.sized aux
  where
    aux 0 = QC.oneof [pure TInt]
    aux n =
      QC.oneof
        [ pure TInt,
          Fun <$> aux (n - 1) <*> aux (n - 1)
        ]

-- genExpr :: Gen Expr
-- genExpr = QC.resize 4 genType >>= \t -> QC.sized (aux [] t)
--   where
--     aux ctx TInt 0 =
--       QC.oneof $ (Int <$> QC.choose (1, 3)) : catMaybes [genVar ctx TInt]
--     aux ctx TInt n =
--       QC.oneof $
--         [ Int <$> QC.choose (1, 3),
--           Plus <$> aux ctx TInt (n - 1) <*> aux ctx TInt (n - 1)
--         ]
--           ++ catMaybes [genVar ctx TInt]

--     aux ctx (Fun t1 t2) n =
--       QC.oneof
--         [ QC.oneof [pure (Int i) | i <- [0 .. 3]],
--           Plus <$> aux (n - 1) <*> aux (n - 1),
--           Lam <$> QC.resize 3 genType <*> aux (n - 1),
--           App <$> aux (n - 1) <*> aux (n - 1),
--           Var <$> genVar
--         ]

--     genVar ctx t =
--       case concat (zipWith (\i t' -> [i | t == t']) [0 ..] ctx) of
--         [] -> Nothing
--         xs -> Just (Var <$> QC.elements xs)
