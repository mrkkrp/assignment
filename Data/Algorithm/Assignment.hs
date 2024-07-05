-- |
-- Module      :  Data.Algorithm.Assignment
-- Copyright   :  © 2024–present Mark Karpov
-- License     :  BSD 3 clause
--
-- Maintainer  :  Mark Karpov <markkarpov92@gmail.com>
-- Stability   :  experimental
-- Portability :  portable
--
-- A solution to the assignment problem.
module Data.Algorithm.Assignment
  ( assign,
  )
where

import Control.Monad (forM_, unless, when)
import Control.Monad.Fix (fix)
import Control.Monad.ST (ST, runST)
import Data.Array (Array)
import Data.Array.Base qualified as A
import Data.Array.ST (STUArray)
import Data.Array.ST qualified as ST
import Data.Function (on)
import Data.List qualified
import Data.List.NonEmpty qualified as NonEmpty
import Data.Maybe (mapMaybe)
import Data.STRef (modifySTRef', newSTRef, readSTRef)

-- | \(\mathcal{O}(n^4)\). Assign elements from two collections to each
-- other so that the total cost is minimal. The cost of each combination is
-- given the by the first argument and it can be negative. If any of the
-- collections is empty the result is the empty list. The sizes of the
-- collections need not to match. Finally, there is no guarantees on the
-- order of elements in the returned list of pairs.
--
-- See: <https://en.wikipedia.org/wiki/Hungarian_algorithm#Matrix_interpretation>
assign ::
  -- | How to calculate the cost
  (a -> b -> Int) ->
  -- | The first collection
  [a] ->
  -- | The second collection
  [b] ->
  -- | The resulting optimal assignment (no guarantees about order)
  [(a, b)]
assign _ [] _ = []
assign _ _ [] = []
assign cost as bs = runST $ do
  let length_a = length as
      length_b = length bs
      aMinBound = 0
      aMaxBound = length_a - 1
      bMinBound = 0
      bMaxBound = length_b - 1
      abMaxBound = max aMaxBound bMaxBound
      asArray = A.listArray (aMinBound, aMaxBound) as
      bsArray = A.listArray (bMinBound, bMaxBound) bs
  c <- ST.newArray ((aMinBound, bMinBound), (abMaxBound, abMaxBound)) 0
  countFromTo aMinBound aMaxBound $ \i ->
    countFromTo bMinBound bMaxBound $ \j ->
      ST.writeArray c (i, j) (cost (asArray A.! i) (bsArray A.! j))
  let (normalization, assignment) =
        if aMaxBound - aMinBound >= bMaxBound - bMinBound
          then (normalizePerB, assignPerB)
          else (normalizePerA, assignPerA)
  normalization c
  r0 <- assignment c
  indicesToElems asArray bsArray <$> case r0 of
    Nothing ->
      fix $ \recurse -> do
        rearrange c
        r1 <- assignment c
        maybe recurse return r1
    Just is -> return is
{-# INLINEABLE assign #-}

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
{-# INLINEABLE normalizePerA #-}

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
{-# INLINEABLE normalizePerB #-}

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
{-# INLINEABLE rearrange #-}

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
{-# INLINEABLE optimalMarks #-}

-- | Convert zero positions into optimal marks.
marksFromZeroPositions :: [(Int, Int)] -> ([Int], [Int])
marksFromZeroPositions = go ([], []) (0 :: Int)
  where
    go results _ [] = results
    go (aMarksSoFar, bMarksSoFar) markBalance xs =
      let bestAMark = maximumLength (NonEmpty.groupAllWith fst xs)
          bestBMark = maximumLength (NonEmpty.groupAllWith snd xs)
          preferA = case length bestAMark `compare` length bestBMark of
            LT -> False
            EQ -> markBalance < 0
            GT -> True
       in if preferA
            then
              let aMark = fst (NonEmpty.head bestAMark)
                  positionsToCover = filter ((/= aMark) . fst) xs
               in go
                    (aMark : aMarksSoFar, bMarksSoFar)
                    (markBalance + 1)
                    positionsToCover
            else
              let bMark = snd (NonEmpty.head bestBMark)
                  positionsToCover = filter ((/= bMark) . snd) xs
               in go
                    (aMarksSoFar, bMark : bMarksSoFar)
                    (markBalance - 1)
                    positionsToCover
    maximumLength = Data.List.maximumBy (compare `on` length)

-- | Attempt assignment per elements of the first collection and return
-- pairs in the form of indices in the original collections. When assignment
-- is not possible 'Nothing' is returned.
assignPerA ::
  STUArray s (Int, Int) Int ->
  ST s (Maybe [(Int, Int)])
assignPerA c = do
  ((aMinBound, bMinBound), (aMaxBound, bMaxBound)) <- ST.getBounds c
  let go zeroPositions i = do
        let f recurse j =
              if j > bMaxBound
                then return Nothing
                else do
                  x <- ST.readArray c (i, j)
                  if x == 0 && j `notElem` (snd <$> zeroPositions)
                    then do
                      m <- go ((i, j) : zeroPositions) (i + 1)
                      case m of
                        Nothing -> recurse (j + 1)
                        Just r -> return (Just r)
                    else recurse (j + 1)
        if i > aMaxBound
          then return (Just zeroPositions)
          else fix f bMinBound
  go [] aMinBound
{-# INLINEABLE assignPerA #-}

-- | Attempt assignment per elements of the second collection and return
-- pairs in the form of indices in the original collections. When assignment
-- is not possible 'Nothing' is returned.
assignPerB ::
  STUArray s (Int, Int) Int ->
  ST s (Maybe [(Int, Int)])
assignPerB c = do
  ((aMinBound, bMinBound), (aMaxBound, bMaxBound)) <- ST.getBounds c
  let go zeroPositions j = do
        let f recurse i =
              if i > aMaxBound
                then return Nothing
                else do
                  x <- ST.readArray c (i, j)
                  if x == 0 && i `notElem` (fst <$> zeroPositions)
                    then do
                      m <- go ((i, j) : zeroPositions) (j + 1)
                      case m of
                        Nothing -> recurse (i + 1)
                        Just r -> return (Just r)
                    else recurse (i + 1)
        if j > bMaxBound
          then return (Just zeroPositions)
          else fix f aMinBound
  go [] bMinBound
{-# INLINEABLE assignPerB #-}

-- | Transform an assignment expressed as pairs of indices into pairs of
-- elements of the actual collections.
indicesToElems :: Array Int a -> Array Int b -> [(Int, Int)] -> [(a, b)]
indicesToElems asArray bsArray = mapMaybe f
  where
    f (i, j) = (,) <$> (asArray A.!? i) <*> (bsArray A.!? j)
{-# INLINE indicesToElems #-}

countFromTo :: Int -> Int -> (Int -> ST s ()) -> ST s ()
countFromTo start end action = go start
  where
    go !n = when (n <= end) $ do
      action n
      go (n + 1)
{-# INLINE countFromTo #-}

asSTUArray :: ST s (STUArray s i a) -> ST s (STUArray s i a)
asSTUArray = id
{-# INLINE asSTUArray #-}
