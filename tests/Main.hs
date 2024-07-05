module Main (main) where

import Data.Algorithm.Assignment (assign)
import Data.List (sort)
import Data.List qualified
import Data.Tuple (swap)
import Test.Hspec
import Test.QuickCheck

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "assign" $ do
    it "returns the empty list if the first collection is empty" $
      assign (\_ _ -> 0) ([] :: [Int]) ([1, 2, 3] :: [Int]) `shouldBe` []
    it "returns the empty list if the second collection is empty" $
      assign (\_ _ -> 0) ([1, 2, 3] :: [Int]) ([] :: [Int]) `shouldBe` []
    it "solves the example from Wikipedia" $ do
      let cost "Alice" "Clean bathroom" = 8
          cost "Alice" "Sweep floors" = 4
          cost "Alice" "Wash windows" = 7
          cost "Bob" "Clean bathroom" = 5
          cost "Bob" "Sweep floors" = 2
          cost "Bob" "Wash windows" = 3
          cost "Dora" "Clean bathroom" = 9
          cost "Dora" "Sweep floors" = 4
          cost "Dora" "Wash windows" = 8
          cost _ _ = 0
      Data.List.sortOn
        fst
        ( assign
            cost
            ["Alice", "Bob", "Dora"]
            ["Clean bathroom", "Sweep floors", "Wash windows"]
        )
        `shouldBe` [ ("Alice", "Clean bathroom"),
                     ("Bob", "Wash windows"),
                     ("Dora", "Sweep floors")
                   ]
    it "always finds the best assignment" $
      property $ \(Fun _ cost) (Short as) (Short bs) -> do
        let totalCost = sum . fmap cost
        forAll (shuffle bs) $ \bs' ->
          totalCost (assign (curry cost) as bs) <= totalCost (zip as bs')
    it "swapping of the collections results in the same pairings" $
      property $ \(Fun _ cost) (Short as) (Short bs) -> do
        let cost0 = curry cost
            cost1 x y = cost0 y x
        sort (assign cost0 as bs) == sort (swap <$> assign cost1 bs as)
    it "shuffling of collections results in the same pairings" $
      property $ \(Fun _ cost) (Short as) (Short bs) -> do
        let cost' = curry cost
        forAll (shuffle as) $ \as' ->
          sort (assign cost' as bs) == sort (assign cost' as' bs)

newtype Short = Short [Int]
  deriving (Show)

instance Arbitrary Short where
  arbitrary = Short <$> scale (`div` 20) arbitrary
