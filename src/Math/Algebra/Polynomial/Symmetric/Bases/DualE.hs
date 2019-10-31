
-- | Elementary symmetric polynomials, indexed by the dual partitions.
--
-- This differs from the \"normal\" elementary symmetric polynomials
-- only by notation. The dual version can be more convenient when working
-- in the ring of symmetric functions in @n@ variables (because the
-- widths of the partitions appearing will be limited by @n@)
--

module Math.Algebra.Polynomial.Symmetric.Bases.DualE where

--------------------------------------------------------------------------------

import GHC.TypeLits

import qualified Data.Map as Map

import Math.Combinat.Sets
import Math.Combinat.Partitions.Integer
import Math.Combinat.Tableaux.GelfandTsetlin

import Math.Algebra.Polynomial.Symmetric.Types
import Math.Algebra.Polynomial.Symmetric.Bases.E

import Math.Algebra.Polynomial.FreeModule ( ZMod , QMod, FreeMod )
import qualified Math.Algebra.Polynomial.FreeModule as ZMod

-- import Math.Algebra.Polynomial.Misc
-- import Math.Algebra.Polynomial.Tables

--------------------------------------------------------------------------------
-- * Conversions to other bases

convertE'toE :: FreeMod c E' -> FreeMod c E
convertE'toE = ZMod.unsafeMapBase f where f (E' p) = E (dualPartition p) 

convertE'toS :: Ring c => FreeMod c E' -> FreeMod c S
convertE'toS = convertEtoS . convertE'toE

convertE'toM :: Ring c => FreeMod c E' -> FreeMod c M
convertE'toM = convertEtoM . convertE'toE

convertE'toP :: CoeffRing c => FreeMod c E' -> FreeMod (FieldOfFractions c) P
convertE'toP = convertEtoP . convertE'toE

--------------------------------------------------------------------------------
-- * Expansions

expandE'toS :: E' -> ZMod S
expandE'toS (E' part) = expandEtoS $ E $ dualPartition part

expandE'toM :: E' -> ZMod M
expandE'toM (E' part) = expandEtoM $ E $ dualPartition part

expandE'toP :: E' -> QMod P
expandE'toP (E' part) = expandEtoP $ E $ dualPartition part

--------------------------------------------------------------------------------


