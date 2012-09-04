{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}

----------------------------------------------------------------------
{- |
   Module      : Data.RangeSpace
   Copyright   : John Lato
   License     : BSD3 (see LICENSE)

   Maintainer  : John Lato <jwlato@gmail.com>
   Stability   : unstable
   Portability : unknown

-}
----------------------------------------------------------------------
module Data.RangeSpace (
-- * Types
  Range (..)
, Bounds
, Span

-- * Conversions
, toBounds
, fromBounds
, fromBoundsC
, newRange

, rangeStart
, rangeEnd
, range

, toSpan
, fromSpan
, fromSpanC

, range2D
, fromRange2D

-- ** AffineSpace conversions
, unPoint

-- * Functions
-- ** Combining ranges
, unionBounds
, translateRange
, unionRange
, maskRange
-- ** Querying ranges
, inRange
, inOrdRange
, compareRange
, extentX
, extentY

-- * Modules
, module X
, module V
)

where

import Data.RangeSpace.TwoD   as X

import Data.Basis             as V
import Data.VectorSpace       as V
import Data.AffineSpace       as V
import Data.AffineSpace.Point as V

import Control.Applicative
import Control.Arrow             ((***))
import Data.List                 (zipWith4)

-- | This should be provided by the AffineSpace.Point module, but isn't.
unPoint :: Point v -> v
unPoint (P v) = v

-- | Define a Range over some domain
data Range t = Range !t !t
    deriving (Eq, Show, Ord, Functor)

instance Applicative Range where
    pure a = Range a a
    (Range minf maxf) <*> (Range minv maxv) = Range (minf minv) (maxf maxv)

-- | A '(minimum,maximum)' pair
type Bounds t = (t,t)

-- | A starting point and duration
type Span t = (t, Diff t)

unRange :: Range t -> (t,t)
unRange (Range t1 t2) = (t1,t2)

-- | Convert a @Range@ to a '(min,max)' pair.
toBounds :: (Ord t) => Range t -> Bounds t
toBounds (Range s0 s1) = if s1 >= s0
    then (s0,s1)
    else (s1,s0)

-- | Generate a @Span@, '(start, distance)' from a 'Range'
toSpan :: (AffineSpace t) => Range t -> (t, Diff t)
toSpan (Range s0 s1) = (s0, s1 .-. s0)

-- | Generate a @Range@ from a @Span@ '(start, distance)'
fromSpan :: (AffineSpace t) => Span t -> Range t
fromSpan (s0,dur) = Range s0 (s0 .+^ dur)

-- | A curried @fromSpan@
fromSpanC :: (AffineSpace t) => t -> Diff t -> Range t
fromSpanC = curry fromSpan

-- | Create a @Range@ from a '(min,max)' 'Bounds' pair.
--
-- 'fromBounds' uses the 'Ord' instance to construct a 'Range'.  For
-- multi-dimensional types, this probably isn't correct.  For that case, see
-- 'newRange'
fromBounds :: (Ord t) => Bounds t -> Range t
fromBounds (minT,maxT)
    | maxT >= minT = Range minT maxT
    | otherwise    = Range maxT minT

-- |  A curried form of @fromBounds@
--
-- See the notes for @fromBounds@.
fromBoundsC :: (Ord t) => t -> t -> Range t
fromBoundsC = curry fromBounds

rangeStart :: (Ord t) => Range t -> t
rangeStart = fst . toBounds

rangeEnd :: (Ord t) => Range t -> t
rangeEnd = snd . toBounds

-- | Get the range covered by a @Range@
range :: (AffineSpace t) => Range t -> Diff t
range = snd . toSpan

-- | Translate a 'Range' by the given amount.
translateRange :: AffineSpace t => Diff t -> Range t -> Range t
translateRange t rng = (.+^ t) <$> rng

-- -------------------------------------------------------------------------
-- multi-dimensional stuff

-- | Create a range from a 'start,stop' pair.  For multi-dimensional ranges,
-- the resulting range will be the union of the two points.
newRange :: (Ord t, AffineSpace t, HasBasis (Diff t)
            ,Ord (Scalar (Diff t)), Num (Scalar (Diff t)))
         => t
         -> t
         -> Range t
newRange start stop = unionRange (Range start start) (Range stop stop)

-- | Calculate the union of two 'Bounds'.  See the notes for @unionRange@.
unionBounds :: (Num (Scalar (Diff t)), Ord (Scalar (Diff t)), Ord t,
               HasBasis (Diff t), AffineSpace t)
            => Bounds t
            -> Bounds t
            -> Bounds t
unionBounds r1 r2 = unRange $ unionRange (fromBounds r1) (fromBounds r2)

-- | Calculate the union of two 'Range's, per-basis.
--
-- The union is constructed by calculating the difference vector between two points,
-- performing a basis decomposition on that vector, performing comparisons and
-- adjustments on each basis vector, recomposing, and adding the result back to
-- the starting position.
--
-- The advantage of this method is that it works on an 'AffineSpace' and
-- doesn't require a full 'VectorSpace'. It does require that the
-- affine space scalars are in a vector space, but this is more easily
-- satisfiable.
unionRange :: (Num (Scalar (Diff t)), Ord t, Ord (Scalar (Diff t)),
                HasBasis (Diff t), AffineSpace t)
           => Range t -> Range t -> Range t
unionRange r0 r1 =
        Range (adjust combineMin min0 min1) (adjust combineMax max0 max1)
    where
        combineMin diff = min diff 0
        combineMax diff = max diff 0
        adjust f orig s = (orig .+^) . recompose . map (fmap f)
                             . decompose $ s .-. orig
        (min0,max0) = toBounds r0
        (min1,max1) = toBounds r1

-- | Restrict a 'Range' by applying a sub-'Range' mask.
--
--  For ranges with multiple dimensions, the masking is performed
--  independently for each basis.
--  If the range lies entirely outside the mask, the returned value
--  is 'Range rmin rmin' (per-basis)
maskRange :: (Eq (Basis (Diff t)), Num (Scalar (Diff t)), Ord t,
                   Ord (Scalar (Diff t)), HasBasis (Diff t), AffineSpace t)
              => Range t    -- ^ restriction
              -> Range t    -- ^ original Range
              -> Range t
maskRange restriction orig = uncurry Range newBounds
    where
        combine (b0,minDiff) (b1,maxDiff) (b2,minCheck) (b3,maxCheck)
            | b0 == b1 && b0 == b2 && b0 == b3 =
                    if minCheck > 0 || maxCheck < 0
                       -- completely outside the restriction on this axis
                       then ((b0, minDiff), (b0, negate maxCheck))
                       else ((b0, max 0 minDiff), (b0, min 0 maxDiff))
            | otherwise = error "Data.RangeSpace.maskRange: basis decompositions must be deterministically ordered"
        (minAdj,maxAdj) = (recompose *** recompose) $ unzip pairs
        newBounds = (oMin .+^ minAdj, oMax .+^ maxAdj)

        pairs = zipWith4 combine (decompose $ rMin .-. oMin)
                                 (decompose $ rMax .-. oMax)
                                 (decompose $ oMin .-. rMax)
                                 (decompose $ oMax .-. rMin)
        (oMin,oMax) = toBounds orig
        (rMin,rMax) = toBounds restriction

-- | Create a 2D range from two independent axes.
range2D :: (Ord a, Ord b)
        => Range a -> Range b -> Range (D2V a b)
range2D r1 r2 = Range (D2V min1 min2) (D2V max1 max2)
    where
        (min1,max1) = toBounds r1
        (min2,max2) = toBounds r2

-- | Decompose a 2D range into X/Y axes.
fromRange2D :: (Ord a, Ord b)
            => Range (D2V a b) -> (Range a, Range b)
fromRange2D (Range (D2V minX minY) (D2V maxX maxY)) =
    (fromBoundsC minX maxX, fromBoundsC minY maxY)

-- | Calculate the X extent of a 2D pointwise range
extentX :: (Ord b, Ord a)
        => Range (Point (D2V a b)) -> Range a
extentX = fst . fromRange2D . fmap unPoint

-- | Calculate the Y extent of a 2D pointwise range
extentY :: (Ord b, Ord a)
        => Range (Point (D2V a b)) -> Range b
extentY = snd . fromRange2D . fmap unPoint
-- -------------------------------------------------------------------------

-- | True if a value lies inside a 'Range'.
inRange :: (Ord a, AffineSpace a, HasBasis (Diff a), Eq (Basis (Diff a))
           ,Num (Scalar (Diff a)) ,Ord (Scalar (Diff a)))
        => a
        -> Range a
        -> Bool
inRange val rng = all f $ zip (decompose pVec) (decompose rVec)
  where
    f ((b1,ppart), (b2,rpart))
        | b1 == b2 = ppart >= 0 && rpart - ppart > 0
        | otherwise = error "Data.RangeSpace.inRange: basis decompositions must be deterministically ordered"
    pVec = val .-. start
    rVec = stop .-. start
    (start, stop) = toBounds rng

-- | Check if a value is in a @Range@, using 'Ord' comparison.
--
-- If 'Ord' is usable, this is likely to be faster than @inRange@.
inOrdRange :: Ord a => a -> Range a -> Bool
inOrdRange val rng = val >= start && val <= stop
  where
    (start,stop) = toBounds rng

-- | Compare a value to a @Range@.  Returns @EQ@ if the value is
-- inside the range, @LT@ or @GT@ if it's outside.
--
-- Uses @Ord@ for comparison.
compareRange :: Ord a => a -> Range a -> Ordering
compareRange val rng = case (compare val start, compare val stop) of
    (LT, _) -> LT
    (_, GT) -> GT
    _       -> EQ
  where
    (start,stop) = toBounds rng

