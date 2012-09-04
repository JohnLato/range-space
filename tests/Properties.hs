{-# OPTIONS -Wall -fno-warn-orphans #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Main (main) where

import Data.RangeSpace

import Control.Applicative
import Data.List (sort)

import Data.Time.Calendar (Day(..))
import Data.Time.Clock

import Test.QuickCheck

import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.Providers.QuickCheck2 (testProperty)

----------------------------------------------------------------------
-- * Derive some instances

instance (ApproxEq t, Ord t, AffineSpace t) => ApproxEq (Range t) where
    approxEq tol r1 r2 = approxEq tol (toBounds r1) (toBounds r2)

deriving instance Arbitrary p => Arbitrary (Point p)
deriving instance ApproxEq p => ApproxEq (Point p)

deriving instance Arbitrary Day
instance Arbitrary UTCTime where
    arbitrary = do
      day <- arbitrary
      diff <- arbitrary
      return $ UTCTime { utctDay = day, utctDayTime = diff }
    shrink (UTCTime day diff) = UTCTime <$> shrink day <*> shrink diff

instance Arbitrary DiffTime where
    arbitrary = picosecondsToDiffTime <$> arbitrary

instance Arbitrary NominalDiffTime where
    arbitrary = diffUTCTime <$> arbitrary <*> arbitrary

instance (Arbitrary a, Arbitrary b) => Arbitrary (D2V a b) where
    arbitrary = D2V <$> arbitrary <*> arbitrary
    shrink (D2V x y) = D2V <$> shrink x <*> shrink y

instance (ApproxEq a, ApproxEq b) => ApproxEq (D2V a b) where
    approxEq tol (D2V x1 y1) (D2V x2 y2) = approxEq tol (x1,y1) (x2,y2)

instance ApproxEq UTCTime where
    approxEq tol t1 t2 = abs (diffUTCTime t1 t2) < realToFrac (tol*2)

instance ApproxEq NominalDiffTime where
    approxEq tol t1 t2 = abs (t2 - t1) <= realToFrac (tol*20)

-- Although Ranges created by @fromBounds@ should always have a positive
-- distance, there's no reason for that to be true in general, so we allow
-- Arbitrary to create Ranges with negative distance.
instance (Arbitrary r) => Arbitrary (Range r) where
    arbitrary = Range <$> arbitrary <*> arbitrary

-- Don't want to drag in more dependencies for just this.
class ApproxEq a where
    approxEq :: Double -> a -> a -> Bool

instance ApproxEq Double where
    approxEq tol d1 d2 = m == 0.0 || d/m < tol where
      m = max (abs d1) (abs d2)
      d = abs (d1 - d2)

instance (ApproxEq a, ApproxEq b) => ApproxEq (a,b) where
    approxEq tol (l1,r1) (l2,r2) = approxEq tol l1 l2 && approxEq tol r1 r2

infix 4 ===
(===) :: (ApproxEq a) => a -> a -> Bool
(===) = approxEq {-pretty equal-}1.0e-10


type DoubleP = Point (D2V Double Double)


----------------------------------------------------------------------
-- Some orphans


instance AdditiveGroup NominalDiffTime where
    zeroV = 0
    (^+^) = (+)
    negateV = negate
    
-- We want an AffineSpace instance for UTCTime, because
-- then we can use 'Range UTCTime'
instance AffineSpace UTCTime where
    type Diff UTCTime = NominalDiffTime
    (.-.) = diffUTCTime
    (.+^) = flip addUTCTime

-- | Having Scalar NominalDiffTime = Double means that scaling
-- and basis decomposition have to go through Rational.
-- Maybe this should be revisited.
instance VectorSpace NominalDiffTime where
    -- Scalar is Double so we can form a basis like
    -- D2V (DataX, NominalDiffTime)
    type Scalar NominalDiffTime = Double
    s *^ difftime = (realToFrac s) * difftime

instance AffineSpace NominalDiffTime where
    type Diff NominalDiffTime = NominalDiffTime
    (.-.) = (-)
    (.+^) = (+)

instance HasBasis NominalDiffTime where
    type Basis NominalDiffTime = ()
    basisValue () = 1
    decompose dtime = [((), realToFrac dtime)]
    decompose' dtime () = realToFrac dtime

----------------------------------------------------------------------
-- * Range tests

-- | When creating '(s0,s1)', s1 >= 0
orderedBoundsRange :: (Ord a, AffineSpace a) => Range a -> Bool
orderedBoundsRange rng = rmax >= rmin
    where (rmin,rmax) = toBounds rng

-- | A created range should always have a non-negative distance
orderedRangeBounds :: (Ord (Diff t), Ord t, AffineSpace t) => Bounds t -> Bool
orderedRangeBounds bounds = (max1 .-. min1) >= zeroV
    where (min1,max1) = toBounds $ fromBounds bounds

roundTripRange :: (Ord a, ApproxEq a, AffineSpace a) => a -> a -> Bool
roundTripRange s0 s1 =
  if s1 >= s0
    then (s0,s1) === (toBounds $ fromBounds (s0,s1) )
    else (s1,s0) === (toBounds $ fromBounds (s0,s1) )


----------------------------------------------------------------------
-- maskRange tests

maskOuter1D :: (Eq (Basis (Diff t)), Num (Scalar (Diff t)),
                   Ord (Scalar (Diff t)), Ord t, HasBasis (Diff t), AffineSpace t,
                   ApproxEq t) =>
                   t -> t -> t -> t -> Property
maskOuter1D v1 v2 v3 v4 = True
    ==> rng === maskRange maskion rng
    where maskion = fromBounds (r0,r1) -- normalized maskion
          rng = fromBounds (s0,s1)
          [r0,s0,s1,r1] = sort [v1,v2,v3,v4]

maskInner1D :: (Eq (Basis (Diff t)), Num (Scalar (Diff t)),
                   Ord (Scalar (Diff t)), Ord t, HasBasis (Diff t), AffineSpace t,
                   ApproxEq t) =>
                   t -> t -> t -> t -> Property
maskInner1D v1 v2 v3 v4 = True
    ==> maskion === maskRange maskion rng
    where maskion = fromBounds (r0,r1) -- normalized maskion
          rng = fromBounds (s0,s1)
          [s0,r0,r1,s1] = sort [v1,v2,v3,v4]

maskLeft1D :: (Eq (Basis (Diff t)), Num (Scalar (Diff t)), Ord (Scalar (Diff t)),
                  Ord t, HasBasis (Diff t), AffineSpace t, ApproxEq t) =>
                  t -> t -> t -> t -> Property
maskLeft1D v1 v2 v3 v4 = True
    ==> fromBounds (r0,s1)
        === maskRange (fromBounds (r0,r1)) (fromBounds (s0,s1))
   where
      [s0,r0,s1,r1] = sort [v1,v2,v3,v4]

maskRight1D :: (Eq (Basis (Diff t)), Num (Scalar (Diff t)),
                   Ord (Scalar (Diff t)), Ord t, HasBasis (Diff t), AffineSpace t,
                   ApproxEq t) =>
                   t -> t -> t -> t -> Property
maskRight1D v1 v2 v3 v4 = True
    ==> fromBounds (s0,r1)
        === maskRange (fromBounds (r0,r1)) (fromBounds (s0,s1))
    where
      [r0,s0,r1,s1] = sort [v1,v2,v3,v4]

maskNeg :: (Eq (Basis (Diff t)), Num (Scalar (Diff t)), Ord (Scalar (Diff t)),
               Ord t, HasBasis (Diff t), AffineSpace t, ApproxEq t) =>
               Range t -> Range t -> Bool
maskNeg rng1 rng2 = maskRange rng1 rng2 === maskRange rng1' rng2'
    where
        rng1' = fromBounds $ toBounds rng1
        rng2' = fromBounds $ toBounds rng2

maskMiss1D :: (Eq (Basis (Diff t)), Num (Scalar (Diff t)), Ord (Scalar (Diff t)),
                  Ord t, HasBasis (Diff t), AffineSpace t, ApproxEq t) =>
                  t -> t -> t -> t -> Property
maskMiss1D v1 v2 v3 v4 = True
    ==> fromBounds (r0,r0)
        === maskRange (fromBounds (r0,r1)) (fromBounds (s0,s1))
        -- flip the positions to check misses on both sides
        && fromBounds (s0,s0)
        === maskRange (fromBounds (s0,s1)) (fromBounds (r0,r1))
   where
      [r0,r1,s0,s1] = sort [v1,v2,v3,v4]


-- 2D tests

maskD2V :: (Eq (Basis (Diff t1)), Eq (Basis (Diff t)), Num (Scalar (Diff t)),
               Ord (Scalar (Diff t)), Ord t, Ord t1, HasBasis (Diff t1),
               HasBasis (Diff t), AffineSpace t, AffineSpace t1, ApproxEq t1,
               ApproxEq t, Scalar (Diff t1) ~ Scalar (Diff t)) =>
               Range t1 -> Range t1 -> Range t -> Range t -> Bool
maskD2V xr1 xr2 yr1 yr2 =
    rngMin === (D2V minx miny) && rngMax === D2V maxx maxy
    where
        Range rngMin rngMax = maskRange r2d1 r2d2
        (minx,maxx) = toBounds $ maskRange (xr1) (xr2)
        (miny,maxy) = toBounds $ maskRange (yr1) (yr2)
        r2d1 = range2D xr1 yr1
        r2d2 = range2D xr2 yr2

-- union tests

unionRangeBounds :: (Num (Scalar (Diff t)), Ord (Scalar (Diff t)), Ord t,
                    HasBasis (Diff t), AffineSpace t, ApproxEq t)
                 => Range t -> Range t -> Bool
unionRangeBounds r1 r2 =
    toBounds (unionRange r1 r2) === (min min1 min2,max max1 max2)
    where
        (min1,max1) = toBounds r1
        (min2,max2) = toBounds r2

----------------------------------------------------------------------
-- Test harness

main :: IO ()
main = defaultMain tests

-- do a *whole lot* of tests, to make sure that the instances are all correct.
tests :: [Test]
tests =
    [ testGroup "bounds"
      [ testGroup "construction"
        [ testProperty "Double" (orderedBoundsRange  :: Range Double  -> Bool)
        , testProperty "DoubleP" (orderedBoundsRange   :: Range DoubleP   -> Bool)
        ]
      ]
    , testGroup "range"
      [ testGroup "construction"
        [ testProperty "Double" (orderedRangeBounds  :: (Double,Double)->Bool)
        , testProperty "DoubleP" (orderedRangeBounds   :: (DoubleP  ,DoubleP)->Bool)
        ]
      ]
    , testGroup "roundTrip"
      [ testProperty "Double" (roundTripRange :: Double->Double->Bool)
      , testProperty "DoubleP" (roundTripRange :: DoubleP->DoubleP->Bool)
      ]
    , testGroup "union"
    -- only testing with a few types, if there are problems with instances
    -- they'll show up in maskRange tests
    [ testProperty "Double"
        (unionRangeBounds :: Range Double->Range Double->Bool)
    , testProperty "NominalDiffTime"
        (unionRangeBounds :: Range NominalDiffTime->Range NominalDiffTime->Bool)
    ]
    , testGroup "maskRange"
      [ testGroup "maskOuter1D"
        [ testProperty "Double"
            (maskOuter1D  :: Double->Double->Double->Double->Property)
        , testProperty "NominalDiffTime"
            (maskOuter1D :: NominalDiffTime->NominalDiffTime
                                ->NominalDiffTime->NominalDiffTime->Property)
        ]
     , testGroup "maskInner1D"
        [ testProperty "Double"
            (maskInner1D  :: Double->Double->Double->Double->Property)
        , testProperty "NominalDiffTime"
            (maskInner1D :: NominalDiffTime->NominalDiffTime
                                ->NominalDiffTime->NominalDiffTime->Property)
        ]
      , testGroup "maskLeft1D"
        [ testProperty "Double"
            (maskLeft1D :: Double->Double->Double->Double->Property)
        , testProperty "NominalDiffTime"
            (maskLeft1D :: NominalDiffTime->NominalDiffTime
                               ->NominalDiffTime->NominalDiffTime->Property)
        ]
      , testGroup "maskMiss1D"
        [ testProperty "Double"
            (maskMiss1D :: Double->Double->Double->Double->Property)
        ]
      , testGroup "RestrictNeg"
        [ testProperty "Double"
            (maskRight1D :: Double->Double->Double->Double->Property)
        , testProperty "NominalDiffTime"
            (maskRight1D :: NominalDiffTime->NominalDiffTime
                                ->NominalDiffTime->NominalDiffTime->Property)
        ]
      , testGroup "maskNeg"
        [ testProperty "Double"
            (maskNeg :: Range Double->Range Double->Bool)
        , testProperty "NominalDiffTime"
            (maskNeg :: Range NominalDiffTime->Range NominalDiffTime->Bool)
        ]
      , testGroup "mask2D"
        [ testProperty "Double/Double"
            (maskD2V :: Range Double->Range Double->Range Double
                            ->Range Double->Bool)
        , testProperty "Double/NominalDiffTime" (maskD2V ::
            Range Double->Range Double->Range NominalDiffTime
            ->Range NominalDiffTime->Bool)
        ]
      ]
    ]
