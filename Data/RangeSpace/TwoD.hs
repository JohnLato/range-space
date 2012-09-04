{-# LANGUAGE TypeFamilies #-}

module Data.RangeSpace.TwoD (
  D2V (..)
) where

import Data.Basis             as V
import Data.VectorSpace       as V
import Data.AffineSpace       as V

import Control.Arrow (first)

-- | A wrapper for two-dimensional vector types.
data D2V a b = D2V {
    xAxis :: !a
   ,yAxis :: !b
   } deriving (Eq, Ord, Show)

instance (Num a, Num b) => Num (D2V a b) where
    fromInteger n = D2V (fromIntegral n) (fromIntegral n)
    (D2V x1 y1) + (D2V x2 y2) = D2V (x1 + x2) (y1 + y2)
    (D2V x1 y1) * (D2V x2 y2) = D2V (x1 * x2) (y1 * y2)
    negate (D2V x y) = D2V (negate x) (negate y)
    abs (D2V x y) = D2V (abs x) (abs y)
    signum (D2V x y) = D2V (signum x) (signum y)

instance (AdditiveGroup a, AdditiveGroup b) => AdditiveGroup (D2V a b) where
    zeroV = D2V zeroV zeroV
    (D2V x1 y1) ^+^ (D2V x2 y2) = D2V (x1 ^+^ x2) (y1 ^+^ y2)
    negateV (D2V x y) = D2V (negateV x) (negateV y)

instance (AffineSpace a, AffineSpace b) => AffineSpace (D2V a b) where
    type Diff (D2V a b) = D2V (Diff a) (Diff b)
    (D2V x1 y1) .-. (D2V x2 y2) = D2V (x1 .-. x2) (y1 .-. y2)
    (D2V x1 y1) .+^ (D2V x2 y2) = D2V (x1 .+^ x2) (y1 .+^ y2)

instance (VectorSpace a, VectorSpace b, Scalar a ~ Scalar b)
         => VectorSpace (D2V a b) where
    type Scalar (D2V a b) = Scalar a
    s *^ (D2V x y) = D2V (s *^ x) (s *^ y)

instance (HasBasis a, HasBasis b, Scalar a ~ Scalar b)
         => HasBasis (D2V a b) where
    type Basis (D2V a b) = Either (Basis a) (Basis b)
    basisValue = either (\lb -> D2V (basisValue lb) zeroV)
                          (D2V zeroV . basisValue)
    decompose (D2V x y) = map (first Left) (decompose x)
                          ++ map (first Right) (decompose y)
    decompose' (D2V x _) (Left lb)  = decompose' x lb
    decompose' (D2V _ y) (Right lb) = decompose' y lb
