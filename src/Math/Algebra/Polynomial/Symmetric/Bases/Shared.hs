
-- | Some stuff shared by the other modules, 
-- to avoid cyclic dependencies
--

{-# LANGUAGE BangPatterns #-}
module Math.Algebra.Polynomial.Symmetric.Bases.Shared where

--------------------------------------------------------------------------------

import Data.Typeable

import qualified Data.Map.Strict as Map

import Math.Combinat.Sets
import Math.Combinat.Partitions.Integer
import Math.Combinat.Permutations ( permuteMultiset )
import Math.Combinat.Tableaux.GelfandTsetlin ( kostkaNumbersWithGivenLambda )

import Math.Algebra.Polynomial.Symmetric.Types

import Math.Algebra.Polynomial.FreeModule ( ZMod , QMod , FreeMod )
import qualified Math.Algebra.Polynomial.FreeModule as ZMod

import Math.Algebra.Polynomial.Symmetric.Helpers.Misc
import Math.Algebra.Polynomial.Symmetric.Helpers.Tables

--------------------------------------------------------------------------------
-- * diagonal conversion (hmm hmm?)

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

--------------------------------------------------------------------------------
-- * Schur

expandStoM_shared :: S -> ZMod M
expandStoM_shared (S lambda) = lookupPTable lambda schurTableM_shared

schurTableM_shared :: PTable (ZMod M)
schurTableM_shared = makePTable $ \lookup part -> calcExpandStoM_shared (S part)

-- | Expansion of a Schur polynomials into monomial symmetric polynomials.
-- The coefficients are Kostka numbers.
calcExpandStoM_shared :: S -> ZMod M
calcExpandStoM_shared (S part) = ZMod.FreeMod $ Map.mapKeys M $ kostkaNumbersWithGivenLambda part

--------------------------------------------------------------------------------

