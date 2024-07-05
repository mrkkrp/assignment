module Main (main) where

import Data.Algorithm.Assignment (assign)
import Data.List qualified
import Test.Hspec

-- import Test.QuickCheck

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "assign" $ do
    it "returns the empty list if the first collection is empty" $
      assign ([] :: [Int]) ([1, 2, 3] :: [Int]) (\_ _ -> 0) `shouldBe` []
    it "returns the empty list if the second collection is empty" $
      assign ([1, 2, 3] :: [Int]) ([] :: [Int]) (\_ _ -> 0) `shouldBe` []
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
            ["Alice", "Bob", "Dora"]
            ["Clean bathroom", "Sweep floors", "Wash windows"]
            cost
        )
        `shouldBe` [ ("Alice", "Clean bathroom"),
                     ("Bob", "Wash windows"),
                     ("Dora", "Sweep floors")
                   ]

-- TODO collections do not have to be of the same size

-- TODO always finds the best assignment (total cost is always <= than
-- any other assignment)

-- TODO swapping of the collections results in the same pairings

-- TODO shuffling of the collections should result in an equivalent assignment
