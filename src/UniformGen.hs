{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module UniformGen where

import BidirectionalProfunctors (Profmonad)
import Data.Profunctor (Profunctor (..))
import PartialProfunctors (PartialProfunctor (..))
import Reflective (Pick (..), Reflective)
import Test.QuickCheck (oneof)
import qualified Test.QuickCheck as QuickCheck

{- begin Gen -}
newtype Gen t b a = Gen
  {run :: QuickCheck.Gen a}
  {- end Gen -}
  deriving (Functor, Applicative, Monad)

instance Profunctor (Gen t) where
  dimap _ fwd = Gen . (fwd <$>) . run

instance PartialProfunctor (Gen t) where
  internaliseMaybe = Gen . run

instance Profmonad (Gen t)

{- begin GenPick -}
instance Pick Gen where
  pick = Gen . oneof . map (run . snd)

{- end GenPick -}

instance Reflective Gen

{- begin uniformGen -}
gen :: Gen t b a -> QuickCheck.Gen a
gen = run

{- end uniformGen -}
