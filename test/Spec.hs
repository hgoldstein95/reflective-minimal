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
import Freer (Reflective, Freer(..), R(..), generate, resize, Tree(..)
             , bst, hypoTree, unlabelled,)
import Bound5Example (int16, reflT)
import CalcExample (reflCalc)
import HeapExample (reflHeap)
import JSONExample (start, object, members, pair, array, elements, value, string
                   , chars, char_, letter, escapedspecial, number, int_, frac, expo
                   , digits, digit, nonzerodigit, e, withChecksum)
import ListExample (reflList)
import ParserExample (reflVar, reflLang, reflMod, reflFunc, reflStmt, reflExp)
import SystemFExample (genExpr)

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
    prop "systemF" $ soundness (genExpr 10) -- TODO fails
  describe "Our reflectives satisfy pure proj" $ do
    prop "bst" $ pureProj bst
    prop "unlabelled" $ pureProj unlabelled
    prop "hypoTree" $ pureProj hypoTree -- slow
    -- NOTE:- this property is very difficult to test because the antecedent is
    -- often not fulfilled, causing QuickCheck to give up. This is why most of these
    -- tests are commented out, because QuickCheck gives up
    -- Freer
    -- -- Bound5Example
    -- prop "int16" $ pureProj int16
    -- prop "reflT" $ pureProj reflT
    -- -- CalcExample
    -- prop "reflCalc" $ pureProj reflCalc
    -- -- HeapExample
    -- prop "reflHeap" $ pureProj reflHeap
    -- -- JSONExample
    -- prop "start" $ pureProj start
    -- prop "object" $ pureProj object
    -- prop "members" $ pureProj members
    -- prop "pair" $ pureProj pair
    -- prop "array" $ pureProj array
    -- prop "elements" $ pureProj elements
    -- prop "value" $ pureProj value
    -- prop "string" $ pureProj string
    -- prop "chars" $ pureProj chars
    -- prop "char_" $ pureProj char_
    -- prop "letter" $ pureProj letter
    -- prop "escapedspecial" $ pureProj escapedspecial
    -- prop "number" $ pureProj number
    -- prop "int_" $ pureProj int_
    -- prop "frac" $ pureProj frac
    -- prop "expo" $ pureProj expo
    -- prop "digits" $ pureProj digits
    -- prop "digit" $ pureProj digit
    -- prop "nonzerodigit" $ pureProj nonzerodigit
    -- prop "e" $ pureProj e
    -- prop "withChecksum" $ pureProj withChecksum
    -- -- ListExample
    -- prop "reflList" $ pureProj reflList
    -- -- Parser Example
    -- prop "reflVar" $ pureProj reflVar
    -- prop "reflLang" $ pureProj reflLang
    -- prop "reflMod" $ pureProj reflMod
    -- prop "reflFunc" $ pureProj reflFunc -- slow
    -- prop "reflStmt" $ pureProj reflStmt
    -- prop "reflExp" $ pureProj reflExp
    -- prop "systemF" $ pureProj (genExpr 10) -- TODO fails, often vacuously, but sometimes with prefix issue
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
  describe "bst satisfies external properties" $ do
    prop "soundness re bst prop" $ exSound bstProp bst
    prop "completeness re bst prop" $ exComp bstProp bst

-- NOTES:
--   * dont test infFanOut cos the point of that is that it doesnt stop
--   * bstFwd not tested cos its not aligned
--   * Can't test interps cos they require Eq / Arbitrary instances for things that
--     dont have them e.g. Eq for Gen a, or Arb for Reflective
--   * weakComplete is impossible to test
--   * As above, pure proj is often intractable to test

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

-- a’ ∈ reflect’ g a ==> a = a’
-- "if the reflective can reflect the input, then all of the things we get out are equal"
-- Unlike the other properties, this must use a generic generator so that we can
-- find out if there are things that cannot be generated by the reflective, but
-- can be reflected by it.
-- The issue with this property is that it often fails vacuously, because the precondition
-- is unlikely to hold. This makes it a challenge to test.
pureProj :: (Eq a) => Reflective a a -> a -> a -> QC.Property
pureProj g a a' = a' `elem` reflect' g a ==> a == a'

-- x ∈ gen g ==> p x
exSound :: Show a => (a -> Bool) -> Reflective a a ->  QC.NonNegative Int ->  QC.Property
exSound p g n = QC.forAll
    (generate (resize (QC.getNonNegative n) g))
    (\a -> p a)

exComp :: (a -> Bool) -> Reflective a a -> a -> QC.Property
exComp p g t = p t ==> (not . null) (reflect' g t)

-- What it means to be a valid BST
bstProp :: Tree -> Bool
bstProp = aux (1, 10) -- to match our def of bst and keep the size down
  where
    aux :: (Int,Int) -> Tree -> Bool
    aux (_ ,  _)  Leaf = True
    aux (lo, hi) (Node l x r) = lo <= x && x <= hi
                              && aux (lo, x - 1) l && aux (x + 1,hi) r
