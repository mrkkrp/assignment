-- | A solution to the assignment problem.
module Data.Algorithm.Assignment
  ( assign,
  )
where

import Control.Monad (forM_, unless, when)
import Control.Monad.Fix (fix)
import Control.Monad.ST (ST, runST)
import Data.Array (Array)
import Data.Array qualified as A
import Data.Array.ST (STUArray)
import Data.Array.ST qualified as ST
import Data.Bifunctor (first, second)
import Data.Function (on)
import Data.List qualified
import Data.List.NonEmpty qualified as NonEmpty
import Data.STRef (modifySTRef', newSTRef, readSTRef)
import Debug.Trace (traceShow, traceShowId)

-- | Assign elements from the first two arguments to each other so that the
-- total cost is minimal. The cost of each combination is given the by the
-- third argument. If any of the collections is empty the result is the
-- empty list. Finally, there is no guarantees on the order of elements in
-- the returned list of pairs.
--
-- See: <https://en.wikipedia.org/wiki/Hungarian_algorithm#Matrix_interpretation>
assign ::
  -- | The first collection of elements
  [a] ->
  -- | The second collection of elements
  [b] ->
  -- | How to calculate the cost
  (a -> b -> Int) ->
  -- | The resulting optimal assignment (no guarantees about order)
  [(a, b)]
assign [] _ _ = []
assign _ [] _ = []
assign as bs cost = runST $ do
  let length_a = length as
      length_b = length bs
      aMinBound = 0
      aMaxBound = length_a - 1
      bMinBound = 0
      bMaxBound = length_b - 1
      asArray = A.listArray (aMinBound, aMaxBound) as
      bsArray = A.listArray (bMinBound, bMaxBound) bs
  c <- ST.newArray_ ((aMinBound, bMinBound), (aMaxBound, bMaxBound))
  countFromTo aMinBound aMaxBound $ \i ->
    countFromTo bMinBound bMaxBound $ \j ->
      ST.writeArray c (i, j) (cost (asArray A.! i) (bsArray A.! j))
  normalizePerA c
  es0 <- ST.getElems c
  r0 <- traceShowId <$> attemptAssignment (traceShow es0 c)
  bestAssignment cost . fmap (indicesToElems asArray bsArray) <$> case r0 of
    [] -> do
      normalizePerB c
      es1 <- ST.getElems c
      r1 <- traceShowId <$> attemptAssignment (traceShow es1 c)
      case r1 of
        [] ->
          fix $ \recurse -> do
            rearrange c
            es2 <- ST.getElems c
            r2 <- traceShowId <$> attemptAssignment (traceShow es2 c)
            case r2 of
              [] -> recurse
              _ -> return r2
        _ -> return r1
    _ -> return r0

-- | Normalize the matrix by finding the minimal element from the second
-- collection (B) that corresponds to a given element from the first
-- collection (A) and subtracting it from all elements that correspond to
-- that given element from A.
normalizePerA :: STUArray s (Int, Int) Int -> ST s ()
normalizePerA c = do
  ((aMinBound, bMinBound), (aMaxBound, bMaxBound)) <- ST.getBounds c
  countFromTo aMinBound aMaxBound $ \i -> do
    minValueRef <- newSTRef maxBound
    countFromTo bMinBound bMaxBound $ \j ->
      ST.readArray c (i, j) >>= modifySTRef' minValueRef . min
    minValue <- readSTRef minValueRef
    when (minValue /= 0) $ do
      countFromTo bMinBound bMaxBound $ \j -> do
        ST.modifyArray' c (i, j) (subtract minValue)

-- | Normalize the matrix by finding the minimal element from the first
-- collection (A) that corresponds to a given element from the second
-- collection (B) and subtracting it from all elements that correspond to
-- that given element from B.
normalizePerB :: STUArray s (Int, Int) Int -> ST s ()
normalizePerB c = do
  ((aMinBound, bMinBound), (aMaxBound, bMaxBound)) <- ST.getBounds c
  countFromTo bMinBound bMaxBound $ \j -> do
    minValueRef <- newSTRef maxBound
    countFromTo aMinBound aMaxBound $ \i ->
      ST.readArray c (i, j) >>= modifySTRef' minValueRef . min
    minValue <- readSTRef minValueRef
    when (minValue /= 0) $ do
      countFromTo aMinBound aMaxBound $ \i -> do
        ST.modifyArray' c (i, j) (subtract minValue)

-- | Rearrange the given matrix so as get closer to a successful assignment.
rearrange :: STUArray s (Int, Int) Int -> ST s ()
rearrange c = do
  ((aMinBound, bMinBound), (aMaxBound, bMaxBound)) <- ST.getBounds c
  (aMarksList, bMarksList) <- optimalMarks c
  aMarks <- asSTUArray (ST.newArray (aMinBound, aMaxBound) False)
  bMarks <- asSTUArray (ST.newArray (bMinBound, bMaxBound) False)
  forM_ aMarksList $ \i ->
    ST.writeArray aMarks i True
  forM_ bMarksList $ \j ->
    ST.writeArray bMarks j True
  minUnmarkedValueRef <- newSTRef maxBound
  countFromTo aMinBound aMaxBound $ \i ->
    countFromTo bMinBound bMaxBound $ \j -> do
      aMarked <- ST.readArray aMarks i
      bMarked <- ST.readArray bMarks j
      unless (aMarked || bMarked) $
        ST.readArray c (i, j) >>= modifySTRef' minUnmarkedValueRef . min
  minUnmarkedValue <- readSTRef minUnmarkedValueRef
  countFromTo aMinBound aMaxBound $ \i ->
    countFromTo bMinBound bMaxBound $ \j -> do
      aMarked <- ST.readArray aMarks i
      bMarked <- ST.readArray bMarks j
      if not aMarked && not bMarked
        then ST.modifyArray c (i, j) (subtract minUnmarkedValue)
        else
          when (aMarked && bMarked) $
            ST.modifyArray c (i, j) (+ minUnmarkedValue)

-- | Return optimal marks in A and B respectively so that they cover all
-- zeros in the matrix.
optimalMarks :: STUArray s (Int, Int) Int -> ST s ([Int], [Int])
optimalMarks c = do
  ((aMinBound, bMinBound), (aMaxBound, bMaxBound)) <- ST.getBounds c
  zeroPositionsRef <- newSTRef []
  countFromTo aMinBound aMaxBound $ \i ->
    countFromTo bMinBound bMaxBound $ \j -> do
      x <- ST.readArray c (i, j)
      when (x == 0) $
        modifySTRef' zeroPositionsRef ((i, j) :)
  marksFromZeroPositions <$> readSTRef zeroPositionsRef

-- | Convert zero positions into optimal marks.
marksFromZeroPositions :: [(Int, Int)] -> ([Int], [Int])
marksFromZeroPositions [] = ([], [])
marksFromZeroPositions xs =
  if length bestAMark >= length bestBMark
    then
      let aMark = fst (NonEmpty.head bestAMark)
          positionsToCover = filter ((/= aMark) . fst) xs
       in first (aMark :) (marksFromZeroPositions positionsToCover)
    else
      let bMark = snd (NonEmpty.head bestBMark)
          positionsToCover = filter ((/= bMark) . snd) xs
       in second (bMark :) (marksFromZeroPositions positionsToCover)
  where
    bestAMark = maximumLength (NonEmpty.groupAllWith fst xs)
    bestBMark = maximumLength (NonEmpty.groupAllWith snd xs)
    maximumLength = Data.List.maximumBy (compare `on` length)

-- | Attempt assignment, return candidate assignments as pairs of indices in
-- the original collections. When assignment is not possible the empty list
-- is returned. When the sizes of two collections are not equal, more than
-- one candidate assignment may be returned.
attemptAssignment ::
  STUArray s (Int, Int) Int ->
  ST s [[(Int, Int)]]
attemptAssignment c = do
  ((aMinBound, bMinBound), (aMaxBound, bMaxBound)) <- ST.getBounds c
  let go zeroPositions i = do
        let f recurse j =
              if j > bMaxBound
                then return []
                else do
                  x <- ST.readArray c (i, j)
                  if x == 0 && j `notElem` (snd <$> zeroPositions)
                    then do
                      candidates <- go ((i, j) : zeroPositions) (i + 1)
                      case candidates of
                        [] -> recurse (j + 1)
                        _ -> (candidates ++) <$> recurse (j + 1)
                    else recurse (j + 1)
        if i > aMaxBound
          then return [zeroPositions]
          else fix f bMinBound
  go [] aMinBound

-- | Transform an assignment expressed as pairs of indices into pairs of
-- elements of the actual collections.
indicesToElems :: Array Int a -> Array Int b -> [(Int, Int)] -> [(a, b)]
indicesToElems asArray bsArray = fmap f
  where
    f (i, j) = (asArray A.! i, bsArray A.! j)

-- | Select the best assignment from a collection of alternatives.
bestAssignment ::
  -- | The cost function
  (a -> b -> Int) ->
  -- | A collection of alternatives
  [[(a, b)]] ->
  -- | The best assignment
  [(a, b)]
bestAssignment cost =
  Data.List.minimumBy (compare `on` (sum . fmap (uncurry cost)))

countFromTo :: Int -> Int -> (Int -> ST s ()) -> ST s ()
countFromTo start end action = go start
  where
    go !n = when (n <= end) $ do
      action n
      go (n + 1)

asSTUArray :: ST s (STUArray s i a) -> ST s (STUArray s i a)
asSTUArray = id
