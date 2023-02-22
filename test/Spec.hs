{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE GADTs         #-}

-- module Spec where
-- here so you can enter this file with the repl, needs to be commented to test

-- base
import Data.Maybe (maybeToList)

-- hspec
import Test.Hspec
import Test.Hspec.QuickCheck

-- QuickCheck
import           Test.QuickCheck ((==>))
import qualified Test.QuickCheck as QC

-- local / under test
import Freer (Reflective, Freer(..), R(..), generate, resize, check
             , bst, hypoTree, unlabelled,)
import Bound5Example (int16, reflT)
import CalcExample (reflCalc)
import HeapExample (reflHeap)
import JSONExample (start, object, members, pair, array, elements, value, string
                   , chars, char_, letter, escapedspecial, number, int_, frac, expo
                   , digits, digit, nonzerodigit, e, withChecksum)
import ListExample (reflList)
import ParserExample (reflVar, reflLang, reflMod, reflFunc, reflStmt, reflExp)

-- TODO add to paper how this is tested? Or is that too hask specific?
--   - ~ corresponding to forall
--   - complete needing aligned (to use check)
--   - discussion of pureproj difficulties

main :: IO ()
main = hspec $ do
  -- Testing our example generators:
  describe "Our reflectives are sound" $ do
    -- Freer
    prop "bst" $ soundness bst
    prop "unlabelled" $ soundness unlabelled
    prop "hypoTree" $ soundness hypoTree -- slow
    -- Bound5Example
    prop "int16" $ soundness int16
    prop "reflT" $ soundness reflT
    -- CalcExample
    prop "reflCalc" $ soundness reflCalc
    -- HeapExample
    prop "reflHeap" $ soundness reflHeap
    -- JSONExample
    prop "start" $ soundness start
    prop "object" $ soundness object
    prop "members" $ soundness members
    prop "pair" $ soundness pair
    prop "array" $ soundness array
    prop "elements" $ soundness elements
    prop "value" $ soundness value
    prop "string" $ soundness string
    prop "chars" $ soundness chars
    prop "char_" $ soundness char_
    prop "letter" $ soundness letter
    prop "escapedspecial" $ soundness escapedspecial
    prop "number" $ soundness number
    prop "int_" $ soundness int_
    prop "frac" $ soundness frac
    prop "expo" $ soundness expo
    prop "digits" $ soundness digits
    prop "digit" $ soundness digit
    prop "nonzerodigit" $ soundness nonzerodigit
    prop "e" $ soundness e
    prop "withChecksum" $ soundness withChecksum
    -- ListExample
    prop "reflList" $ soundness reflList
    -- Parser Example
    prop "reflVar" $ soundness reflVar
    prop "reflLang" $ soundness reflLang -- slow
    prop "reflMod" $ soundness reflMod
    prop "reflFunc" $ soundness reflFunc -- slow
    prop "reflStmt" $ soundness reflStmt
    prop "reflExp" $ soundness reflExp
  describe "Our reflectives are weak complete" $ do
    -- Freer
    prop "bst" $ weakComplete bst
    prop "unlabelled" $ weakComplete unlabelled
    prop "hypoTree" $ weakComplete hypoTree -- slow
    -- Bound5Example
    prop "int16" $ weakComplete int16
    prop "reflT" $ weakComplete reflT
    -- CalcExample
    prop "reflCalc" $ weakComplete reflCalc
    -- HeapExample
    prop "reflHeap" $ weakComplete reflHeap
    -- JSONExample
    prop "start" $ weakComplete start
    prop "object" $ weakComplete object
    prop "members" $ weakComplete members
    prop "pair" $ weakComplete pair
    prop "array" $ weakComplete array
    prop "elements" $ weakComplete elements
    prop "value" $ weakComplete value
    prop "string" $ weakComplete string
    prop "chars" $ weakComplete chars
    prop "char_" $ weakComplete char_
    prop "letter" $ weakComplete letter
    prop "escapedspecial" $ weakComplete escapedspecial
    prop "number" $ weakComplete number
    prop "int_" $ weakComplete int_
    prop "frac" $ weakComplete frac
    prop "expo" $ weakComplete expo
    prop "digits" $ weakComplete digits
    prop "digit" $ weakComplete digit
    prop "nonzerodigit" $ weakComplete nonzerodigit
    prop "e" $ weakComplete e
    prop "withChecksum" $ weakComplete withChecksum
    -- ListExample
    prop "reflList" $ weakComplete reflList
    -- Parser Example
    prop "reflVar" $ weakComplete reflVar
    prop "reflLang" $ weakComplete reflLang -- slow
    prop "reflMod" $ weakComplete reflMod
    prop "reflFunc" $ weakComplete reflFunc -- slow
    prop "reflStmt" $ weakComplete reflStmt
    prop "reflExp" $ weakComplete reflExp
  describe "Our reflectives satisfy pure proj" $
    -- NOTE:- because this property is challenging to test, which is why we will
    -- only demo it on bst.
    prop "bst" $ pureProj bst
    -- NOTE:- In fact most of our JSON reflectives do not fulfil this property.
    -- They can only be considered "intentionally incomplete".
    -- This is so that the implementation can be useable in terms of efficiency.
    -- At every step, it checks a prefix but never the whole suffix, The generator
    -- is essentially parsing in reverse, and no individual sub-generator can enforce
    -- that the whole input is consumed.
    -- This causes this property to fail, because two different inputs that have
    -- the same prefix pass the precondition, but then of course are not equal and
    -- fail the rest.
    -- This is an example where completeness is not always desirable.

  -- TODO other props:
  --     - external soundness and completeness for bst
  -- TODO test interps lawful?
  -- TODO think about fan out prop

-- NOTES:
--   * dont test infFanOut cos the point of that is that it doesnt stop
--   * bstFwd not tested cos its not aligned

-- Special interp to facilitate testing:
reflect' :: Reflective b a -> b -> [a]
reflect' g v = interp g v Nothing
  where
    -- ref -> value -> maybe size -> values
    interp :: Reflective b a -> b -> Maybe Int -> [a]
    interp (Return x) _ _ = return x
    interp (Bind x f) b s = interpR x b s >>= \y -> interp (f y) b s

    interpR :: R b a -> b -> Maybe Int -> [a]
    interpR (Pick  xs) b s = concat [interp x b s | (_, _, x) <- xs]
    interpR (Lmap f x) b s = interpR x (f b) s
    interpR (Prune  x) b s = maybeToList b >>= \b' -> interpR x b' s
    interpR (ChooseInteger (lo, hi)) b _
      | lo <= b && b <= hi = pure b
      | otherwise = []
    interpR GetSize _ (Just s) = return s
    interpR GetSize _ Nothing = pure 30
    interpR (Resize s x) b _ = interpR x b (Just s)

-- Properties:

-- a ~ generate g ==> (not . null) (reflect' g a)
soundness :: Show a => Reflective a a -> QC.NonNegative Int -> QC.Property
soundness g n
  = QC.forAll
      (generate (resize (QC.getNonNegative n) g))
      (not . null . reflect' (resize (QC.getNonNegative n) g))

-- a ∈ reflect’ g b ==> a ∼ generate g
-- adapted to be aligned for testing, for pen and paper proof, we want unaligned tho
-- TODO QUESTION aligned right?
-- TODO QUESTION i also cant tell if using the forall is cheating, but also we get too many
-- discarded tests otherwise
weakComplete :: (Show a, Eq a) => Reflective a a -> QC.NonNegative Int -> QC.Property
weakComplete g n
  = QC.forAll
    (generate (resize (QC.getNonNegative n) g))
    (\a -> a `elem` reflect' g a ==> check g a)

-- a’ ∈ reflect’ g a ==> a = a’
-- "if the reflective can reflect the input, then all of the things we get out are equal"
-- Unlike the other properties, this must use a generic generator so that we can
-- find out if there are things that cannot be generated by the reflective, but
-- can be reflected by it.
-- The issue with this property is that it often fails vacuously, because the precondition
-- is unlikely to hold. This makes it a challenge to test.
pureProj :: (Show a, Eq a) => Reflective a a -> a -> a -> QC.Property
pureProj g a a' = a' `elem` reflect' g a ==> a == a'
