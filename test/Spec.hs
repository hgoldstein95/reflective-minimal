{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE GADTs         #-}

-- base
import Data.Maybe (maybeToList)

-- hspec
import Test.Hspec
import Test.Hspec.QuickCheck

-- QuickCheck
import qualified Test.QuickCheck as QC

-- local / under test
import Freer (Reflective, Freer(..), R(..), generate, resize
             , bst, hypoTree, unlabelled,)
import Bound5Example (int16, reflT)
import CalcExample (reflCalc)
import HeapExample (reflHeap)
import JSONExample (start, object, members, pair, array, elements, value, string
                   , chars, char_, letter, escapedspecial, number, int_, frac, expo
                   , digits, digit, nonzerodigit, e, withChecksum)
import ListExample (reflList)
import ParserExample (reflVar, reflLang, reflMod, reflFunc, reflStmt, reflExp)

main :: IO ()
main = hspec $
  -- Testing our example generators:
  describe "Our reflectives are sound" $ do
    -- Freer
    prop "bst" $ soundness bst
    prop "unlabelled" $ soundness unlabelled
    prop "hypoTree" $ soundness hypoTree
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
    prop "reflLang" $ soundness reflLang
    prop "reflMod" $ soundness reflMod
    prop "reflFunc" $ soundness reflFunc
    prop "reflStmt" $ soundness reflStmt
    prop "reflExp" $ soundness reflExp
  -- TODO other props
  -- TODO test interps lawful?

-- NOTE:
-- dont test infFanOut cos the point of that is that it doesnt stop
-- bstFwd not tested cos its not aligned

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
