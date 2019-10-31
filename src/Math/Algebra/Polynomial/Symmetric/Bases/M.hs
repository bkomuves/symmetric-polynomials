
-- | Monomial symmetric polynomials
--
-- See <https://en.wikipedia.org/wiki/Monomial_symmetric_polynomial>
--

{-# LANGUAGE BangPatterns #-}
module Math.Algebra.Polynomial.Symmetric.Bases.M where

--------------------------------------------------------------------------------

import Data.Typeable

import GHC.TypeLits

import Math.Combinat.Sets
import Math.Combinat.Partitions.Integer
import Math.Combinat.Permutations ( permuteMultiset )

import Math.Algebra.Polynomial.Symmetric.Types

import Math.Algebra.Polynomial.FreeModule ( ZMod , QMod , FreeMod )
import qualified Math.Algebra.Polynomial.FreeModule as ZMod

import Math.Algebra.Polynomial.Symmetric.Helpers.Misc
import Math.Algebra.Polynomial.Symmetric.Helpers.Tables

import Math.Algebra.Polynomial.Symmetric.Bases.E ( expandEtoM , convertEtoP )
import Math.Algebra.Polynomial.Symmetric.Bases.Shared

--------------------------------------------------------------------------------
-- * Conversions of polynomials to other bases


convertMtoS :: Ring c => FreeMod c M -> FreeMod c S
convertMtoS = ZMod.flatMap (ZMod.fromZMod . expandMtoS) 

convertMtoE :: Ring c => FreeMod c M -> FreeMod c E
convertMtoE = ZMod.flatMap (ZMod.fromZMod . expandMtoE) 

convertMtoP :: CoeffRing c => FreeMod c M -> FreeMod (FieldOfFractions c) P
convertMtoP = ZMod.flatMap (ZMod.fromQMod . expandMtoP) 
            . ZMod.unsafeCoeffChange embedToFractions

convertMtoX :: (Ring c, KnownNat n) => FreeMod c M -> FreeMod c (X n)
convertMtoX = ZMod.flatMap monomialSymmPolyX

--------------------------------------------------------------------------------

{-
genericDiagonalConvert 
  :: (Ord x, Ord y, Typeable x, Eq c, Num c, Typeable c) 
  => (FreeMod c x -> Maybe (x,c))         -- ^ select term 
  -> (x -> y)                             -- ^ convert selected to the new basis
  -> (y -> ZMod x)                        -- ^ expand in the old basis
  -> FreeMod c x -> FreeMod c y
genericDiagonalConvert select xToY expandY = go [] where
  go !acc !what = case select what of
    Nothing    -> ZMod.fromList acc
    Just (b,c) -> let yb = xToY b 
                  in  go ((yb,c):acc) (ZMod.subScale what c (ZMod.fromZMod $ expandY yb))
-}

--------------------------------------------------------------------------------
-- * Expansion of M-monomials into other symmetric functions

expandMtoS :: M -> ZMod S
expandMtoS (M part) = lookupPTable part ptableMinS

expandMtoE :: M -> ZMod E
expandMtoE (M part) = lookupPTable part ptableMinE

expandMtoP :: M -> QMod P
expandMtoP (M part) = lookupPTable part ptableMinP

expandMtoX :: (KnownNat n) => M -> ZMod (X n)
expandMtoX = monomialSymmPolyX

--------------------------------------------------------------------------------
-- * Expansion to X

-- | @monomialSymmPolyX lambda@ is the corresponding monomial symmetric polynomial in @n@ variables
monomialSymmPolyX :: (Eq c, Num c, KnownNat n) => M -> FreeMod c (X n)
monomialSymmPolyX (M (Partition es)) = poly where
  n = nOfZModX poly
  poly 
    | n < length es  = ZMod.zero
    | otherwise      = ZMod.fromGeneratorList $ map X 
                     $ permuteMultiset $ take n $ es ++ repeat 0

--------------------------------------------------------------------------------
-- * Uncached computations

calcConvertMtoE :: Ring c => FreeMod c M -> FreeMod c E
calcConvertMtoE = genericDiagonalConvert ZMod.findMaxTerm (\(M p) -> E (dualPartition p)) expandEtoM

calcConvertMtoS :: Ring c => FreeMod c M -> FreeMod c S
calcConvertMtoS = genericDiagonalConvert ZMod.findMaxTerm (\(M p) -> S p) expandStoM_shared 

--------------------------------------------------------------------------------
-- * Cached tables

-- | This uses the diagonal conversion algorithm, which in turns uses the opposite
-- expansion, of Schur polynomials in the M-bases
ptableMinS :: PTable (ZMod S)
ptableMinS = makePTable $ \lookup part -> calcConvertMtoS (ZMod.generator $ M part) 

-- | This uses the diagonal conversion algorithm, which again in turns uses the opposite
-- expansion
ptableMinE :: PTable (ZMod E)
ptableMinE = makePTable $ \lookup part -> calcConvertMtoE (ZMod.generator $ M part) 

-- | This done indirectly, first expanding in E then converting that to P (the 
-- latter of which uses Newton's formulas)
ptableMinP :: PTable (QMod P)
ptableMinP = makePTable $ \lookup part -> convertEtoP (expandMtoE $ M part)

--------------------------------------------------------------------------------

