
-- | Complete symmetric polynomials
--
-- See <https://en.wikipedia.org/wiki/Complete_homogeneous_symmetric_polynomial>
--

module Math.Algebra.Polynomial.Symmetric.Bases.H where

--------------------------------------------------------------------------------

import GHC.TypeLits

import qualified Data.Map as Map

import Math.Combinat.Compositions
import Math.Combinat.Partitions.Integer
import Math.Combinat.Tableaux.GelfandTsetlin

import Math.Algebra.Polynomial.Symmetric.Types
import Math.Algebra.Polynomial.Symmetric.Newton
import Math.Algebra.Polynomial.Symmetric.ScalarProd

import Math.Algebra.Polynomial.FreeModule ( ZMod , QMod, FreeMod )
import qualified Math.Algebra.Polynomial.FreeModule as ZMod

import Math.Algebra.Polynomial.Symmetric.Helpers.Tables

--------------------------------------------------------------------------------
-- * Conversions to other bases

convertHtoS :: Ring c => FreeMod c H -> FreeMod c S
convertHtoS = ZMod.flatMap (ZMod.fromZMod . expandHtoS) 

convertHtoP :: CoeffRing c => FreeMod c H -> FreeMod (FieldOfFractions c) P
convertHtoP = ZMod.flatMap (ZMod.fromQMod . expandHtoP) . ZMod.unsafeCoeffChange embedToFractions

-- convertHtoM :: Ring c => FreeMod c H -> FreeMod c M
-- convertHtoM = ZMod.flatMap (ZMod.fromZMod . expandHtoM)

-- convertHtoX :: (Ring c, KnownNat n) => FreeMod c E -> FreeMod c (X n)
-- convertHtoX = ZMod.flatMap (ZMod.fromZMod . expandHtoX)

--------------------------------------------------------------------------------
-- * Expansion of H-monomials into other symmetric functions

expandHtoS :: H -> ZMod S
expandHtoS (H part) = lookupPTable part ptableHinS

expandHtoP :: H -> QMod P
expandHtoP (H part) = lookupPTable part ptableHinP

-- expandHtoM :: H -> ZMod M
-- expandHtoM = 

-- expandHtoX :: (KnownNat n) => M -> ZMod (X n)
-- expandHtoX = 

--------------------------------------------------------------------------------
-- * Expansion of @H_k@

completeSymmPolyM :: (Eq c, Num c) => Int -> FreeMod c M
completeSymmPolyM k = ZMod.fromGeneratorList [ M p | p <- partitions k ]

-- | @completeSymmPolyX k@ is the k-th complete symmetric polynomial in @n@ variables
completeSymmPolyX :: (Eq c, Num c, KnownNat n) => Int -> FreeMod c (X n)
completeSymmPolyX k = poly where
  n = nOfZModX poly
  poly 
    | k <  0     = ZMod.zero
    | k == 0     = ZMod.one
    | otherwise  = ZMod.fromGeneratorList $ map X $ compositions n k

--------------------------------------------------------------------------------
-- * Cached tables

ptableHinS :: PTable (ZMod S)
ptableHinS = makePTable $ \lookup part -> calcExpandHinS (H part)

-- | Expansion of @h[k]@ in P-basis (using the explicit formula)
itableHinP :: ITable (QMod P)
itableHinP = itableFromFun $ calcHkInP

ptableHinP :: PTable (QMod P)
ptableHinP = makePTable $ \lookup part -> case fromPartition part of
  []     -> ZMod.one
  [n]    -> lookupITable n itableHinP
  (n:ks) -> ZMod.mul (lookupITable n itableHinP) (lookup $ toPartitionUnsafe ks)

--------------------------------------------------------------------------------
-- * Uncached computations

-- | Expansion of a H-monom in the Schur basis (using the iterated Pieri rule)
calcExpandHinS :: H -> ZMod S
calcExpandHinS (H part) = ZMod.fromMap $ Map.mapKeys S $ iteratedPieriRule $ reverse $ fromPartition part

-- | Expansion of @h[k]@ in P-basis (using the explicit formula)
calcHkInP :: Int -> QMod P
calcHkInP n = ZMod.fromList 
  [ (P lambda , 1 / fromInteger (zee lambda)) | lambda <- partitions n ]

-- | Expansion of a H-monom in the P-basis (multiplying together 
calcExpandHinP :: H -> QMod P
calcExpandHinP (H part) = ZMod.product [ calcHkInP h | h <- fromPartition part ]

--------------------------------------------------------------------------------
