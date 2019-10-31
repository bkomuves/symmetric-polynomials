
-- | Often we want to restrict the number of variables or the degree, or both;
-- resulting in \"truncated\" rings.
--

module Math.Algebra.Polynomial.Symmetric.Truncate where

--------------------------------------------------------------------------------

import Data.List

import GHC.TypeLits

import Math.Combinat.Classes
import Math.Combinat.Partitions.Integer

import Math.Algebra.Polynomial.Symmetric.Types

--------------------------------------------------------------------------------

class Truncate a where
  minReqVars  :: a -> Int        -- ^ minimum number of required variables
  maxDegree   :: a -> Int        -- ^ maximum degree of a /single variable/ (eg x_2)
  totalDegree :: a -> Int

--------------------------------------------------------------------------------

instance Truncate S where
  minReqVars  (S p) = width  p
  maxDegree   (S p) = height p
  totalDegree (S p) = weight p

-- note that E is flipped compared to S !
--
-- E[5] is the 5th elementary symmetric polynomial: 
-- each variables has degree 1 but you need at least 5 of them!
instance Truncate E where
  minReqVars  (E p) = height p     
  maxDegree   (E p) = width  p
  totalDegree (E p) = weight p

-- Same as E but flipped
instance Truncate E' where
  minReqVars  (E' p) = width  p     
  maxDegree   (E' p) = height p
  totalDegree (E' p) = weight p

instance Truncate P where
  minReqVars  (P p) = error "P/minReqVars: it's always 1"
  maxDegree   (P p) = height p
  totalDegree (P p) = weight p

instance Truncate M where
  minReqVars  (M p) = width  p
  maxDegree   (M p) = height p
  totalDegree (M p) = weight p

instance KnownNat n => Truncate (X n) where
  minReqVars   x     = nOfX x
  maxDegree   (X ns) = if null ns then 0 else maximum ns
  totalDegree (X ns) = foldl' (+) 0 ns

--------------------------------------------------------------------------------
