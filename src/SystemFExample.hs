{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wall #-}

module SystemFExample where

import Control.Lens (preview, _1, _2)
import Control.Monad ((<=<))
import Data.List (nub)
import Data.Maybe (catMaybes)
import Freer
import SystemF

type VarIdx = Int

genType :: Int -> VarIdx -> Reflective Type Type
genType s freeTypeVar = arb freeTypeVar s
  where
    arb ftv 0 =
      labelled $
        ("base", exact Base) : [("tvar_" ++ show v, exact (TVar v)) | v <- [0 .. ftv - 1]]
    arb ftv n =
      labelled
        [ ("base_type", arb ftv 0),
          ("fun", Fun <$> focus (_Fun . _1) (arb ftv (n `div` 6)) <*> focus (_Fun . _2) (arb ftv (n `div` 4))),
          ("forall", ForAll <$> focus _ForAll (arb (ftv + 1) (n - 1)))
        ]

weights :: [(String, Int)]
weights = [("base_expr", 6), ("lam", 8), ("tlam", 4), ("app1", 8), ("app2", 4)]

genExpr :: Int -> Reflective (Maybe Expr) (Maybe Expr)
genExpr s =
  let ?mutant = NoMutant
   in do
        t <- comap (typeOf =<<) (genType 10 0)
        arb 0 [] t s
  where
    arb ftv c t 0 =
      labelledMaybe $
        [("con", return $ Just Con) | t == Base]
          ++ [("var_" ++ show i, return $ Just $ Var i) | (i, t') <- zip [0 ..] c, t == t']
          ++ [("base_lam", fmap (Lam t1) <$> arb ftv (t1 : c) t2 0) | (Fun t1 t2) <- [t]]
          ++ [("base_forall", fmap TLam <$> arb (ftv + 1) (map (liftType 0) c) t1 0) | (ForAll t1) <- [t]]
    arb ftv c t n =
      labelled $
        [("base_expr", arb ftv c t 0)]
          ++ [("lam", fmap (Lam t1) <$> arb ftv (t1 : c) t2 (n - 1)) | (Fun t1 t2) <- [t]]
          ++ [("tlam", fmap TLam <$> arb (ftv + 1) (map (liftType 0) c) t1 (n - 1)) | (ForAll t1) <- [t]]
          ++ [ ( "app1",
                 do
                   t2 <- comap ((preview (_Fun . _1) <=< typeOf) =<<) $ do
                     labelled [("", x) | x <- map exact (nub $ michal c t) ++ [genType 10 ftv]]
                   me1 <- comap (preview (_App . _1) <$>) (arb ftv c (Fun t2 t) (n `div` 2))
                   me2 <- comap (preview (_App . _2) <$>) (arb ftv c t2 (n `div` 2))
                   return $ App <$> me1 <*> me2
               )
             ]
          ++ [ ( "app2",
                 do
                   (t1, t2) <-
                     comap
                       ( \case
                           Just (TApp ee tt) -> (,tt) <$> typeOf ee
                           _ -> Nothing
                       )
                       g
                   me1 <- comap (preview (_TApp . _1) <$>) (arb ftv c t1 (n - 1))
                   return $ TApp <$> me1 <*> return t2
               )
               | Just g <- [genT1T2 t]
             ]

michal :: [Type] -> Type -> [Type]
michal c t =
  [ t' | varType <- c, t' <- aux varType
  ]
  where
    aux (Fun t1 t2)
      | t == t2 = [t1]
      | t /= t2 = aux t2
    aux _ = []

isClosed :: Type -> Bool
isClosed = isClosed' 0
  where
    isClosed' :: Int -> Type -> Bool
    isClosed' tc (TVar x) = x < tc
    isClosed' tc (Fun t1 t2) = isClosed' tc t1 && isClosed' tc t2
    isClosed' tc (ForAll t) = isClosed' (tc + 1) t
    isClosed' _ TBool = True
    isClosed' _ Base = True

-- Randomly fetch a subterm of a type
fetchSubType :: Type -> Maybe (Reflective Type Type)
fetchSubType t =
  labelledMaybe' $
    [Just ("simple_return", return t) | isClosed t]
      ++ [("arg_type",) <$> fetchSubType t1 | (Fun t1 _) <- [t]]
      ++ [("res_type",) <$> fetchSubType t2 | (Fun _ t2) <- [t]]
      ++ [("forall",) <$> fetchSubType t' | (ForAll t') <- [t]]

labelledMaybe :: Eq a => [(String, Reflective (Maybe a) (Maybe a))] -> Reflective (Maybe a) (Maybe a)
labelledMaybe [] = exact Nothing
labelledMaybe gs = labelled gs

labelledMaybe' :: [Maybe (String, Reflective a a)] -> Maybe (Reflective a a)
labelledMaybe' [] = Nothing
labelledMaybe' (catMaybes -> []) = Nothing
labelledMaybe' (catMaybes -> gs) = Just (labelled gs)

-- "Replace (some occurrences of) closed type s in type t by (TVar n)"
replaceSubType :: Int -> Type -> Type -> Reflective Type Type
replaceSubType n s t =
  labelled $
    [("rst_return", exact t)]
      ++ [("rst_var_" ++ show n, exact $ TVar n) | s == t]
      ++ [ ( "rst_fun",
             Fun <$> focus (_Fun . _1) (replaceSubType n s t1) <*> focus (_Fun . _2) (replaceSubType n s t2)
           )
           | (Fun t1 t2) <- [t]
         ]
      ++ [ ( "rst_forall",
             ForAll <$> focus _ForAll (replaceSubType (n + 1) s t')
           )
           | (ForAll t') <- [t],
             t' == s
         ]

-- Generate t1 t2 such that t1{0:=t2} = t
genT1T2 :: Type -> Maybe (Reflective (Type, Type) (Type, Type))
genT1T2 t = do
  let t' = let ?mutant = NoMutant in liftType 0 t
  case fetchSubType t' of
    Nothing -> Nothing
    Just g -> Just $ do
      t2' <- focus _2 g
      t1 <- focus (_1 . _ForAll) (replaceSubType 0 t2' t')
      return (ForAll t1, t2')
