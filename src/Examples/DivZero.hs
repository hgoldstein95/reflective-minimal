{-

Example Reflective Generator that showcases their expressiveness.
Specifically the example from Section 4.3, where a term can be generated such that
it does not divide by zero.

-}

{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE TemplateHaskell #-}

module Examples.DivZero where

import Control.Lens (makePrisms, _1, _2)
import Control.Monad (liftM2)
import GHC.Generics (Generic)
import Reflectives (Reflective, exact, oneof, focus)
import qualified Interps as Interp
import qualified Test.QuickCheck as QC

-- Term lang:

-- | Simple expression language tat features division, and the potential to divide by zero
data Term = Factor Factor | Mul Term Factor | Div Term Factor deriving (Eq, Show, Read, Generic)
data Factor = Zero | One deriving (Eq, Show, Read, Generic)

-- auto generated prisms to allow us to use focus

makePrisms ''Term
makePrisms ''Factor

-- Evaluator:

-- Evaluation of term
-- >>> evalTerm (Factor One)
-- 1
-- >>> evalTerm (Mul (Factor One) One)
-- 1
-- >>> evalTerm (Div (Factor One) One)
-- 1
evalTerm :: Term -> Int
evalTerm (Factor f) = evalFactor f
evalTerm (Mul t f) = evalTerm t * evalFactor f
evalTerm (Div t f) = evalTerm t `div` evalFactor f

evalFactor :: Factor -> Int
evalFactor Zero = 0
evalFactor One  = 1

-- Reflective Generator:

factorRefl :: Reflective Factor Factor
factorRefl = oneof
  [ exact Zero
  , exact One]

termRefl :: Reflective Term Term
termRefl = oneof
  [ fmap Factor (focus _Factor factorRefl)
  , liftM2 Mul (focus (_Mul . _1) termRefl) (focus (_Mul . _2) factorRefl)
  , divRefl ]
  where
    divRefl :: Reflective Term Term
    divRefl = do
      f <- focus _Factor factorRefl
      if evalFactor f == 0
        then liftM2 Mul (focus (_Mul . _1) termRefl) (focus (_Mul . _2) (exact f))
        else liftM2 Div (focus (_Div . _1) termRefl) (focus (_Div . _2) (exact f))

example :: IO Term
example = QC.generate $ Interp.generate termRefl
