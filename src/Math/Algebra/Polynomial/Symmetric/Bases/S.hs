
-- | Schur polynomials
--
-- See <https://en.wikipedia.org/wiki/Schur_polynomial>

{-# LANGUAGE BangPatterns, ScopedTypeVariables #-}
module Math.Algebra.Polynomial.Symmetric.Bases.S where

--------------------------------------------------------------------------------

import Data.Array
import Data.List
import Data.Maybe

import qualified Data.Map as Map

import GHC.TypeLits

import Math.Combinat.Sets
import Math.Combinat.Partitions.Integer
import Math.Combinat.Partitions.Skew
import Math.Combinat.Tableaux
import Math.Combinat.Tableaux.LittlewoodRichardson
import Math.Combinat.Tableaux.GelfandTsetlin

import Math.Algebra.Polynomial.FreeModule ( ZMod , QMod, FreeMod(..) )
import qualified Math.Algebra.Polynomial.FreeModule as ZMod

import Math.Algebra.Polynomial.Symmetric.Types
import Math.Algebra.Polynomial.Symmetric.Helpers.Determinant
import Math.Algebra.Polynomial.Symmetric.Helpers.Tables
import Math.Algebra.Polynomial.Symmetric.Helpers.Misc

import Math.Algebra.Polynomial.Symmetric.Bases.M ( convertMtoX , convertMtoP )
import Math.Algebra.Polynomial.Symmetric.Bases.Shared

--------------------------------------------------------------------------------
-- * Conversions to other bases

convertStoE :: (Ring c) => FreeMod c S -> FreeMod c E
convertStoE =  ZMod.flatMap (ZMod.fromZMod . expandStoE) 

convertStoH :: (Ring c) => FreeMod c S -> FreeMod c H
convertStoH =  ZMod.flatMap (ZMod.fromZMod . expandStoH)

convertStoM :: (Ring c) => FreeMod c S -> FreeMod c M
convertStoM =  ZMod.flatMap (ZMod.fromZMod . expandStoM) 

convertStoF :: (Ring c) => FreeMod c S -> FreeMod c F
convertStoF =  ZMod.flatMap (ZMod.fromZMod . expandStoF) 

convertStoP :: (CoeffRing c) => FreeMod c S -> FreeMod (FieldOfFractions c) P
convertStoP = ZMod.flatMap (ZMod.fromQMod . expandStoP)
            . ZMod.unsafeCoeffChange embedToFractions

convertStoX :: (Ring c, KnownNat n) => FreeMod c S -> FreeMod c (X n)
convertStoX = ZMod.flatMap  (ZMod.fromZMod . expandStoX)

--------------------------------------------------------------------------------
-- * Expansions of S-monomials (individual Schur polynomials) in other bases

expandStoH :: S -> ZMod H
expandStoH (S lambda) = lookupPTable lambda schurTableH     -- jacobiTrudiH lambda

expandStoE :: S -> ZMod E
expandStoE (S lambda) = ZMod.unsafeMapBase (\(H p) -> E p)
                      $ lookupPTable (dualPartition lambda) schurTableH

expandStoM :: S -> ZMod M
expandStoM = expandStoM_shared
-- expandStoM (S lambda) = lookupPTable lambda schurTableM

expandStoF :: S -> ZMod F
expandStoF (S lambda) = ZMod.unsafeMapBase (\(M p) -> F p)
                      $ lookupPTable (dualPartition lambda) schurTableM

-- | Note: this is done indirectly, first expand in M and then converting that to P.
-- (but the latter is /also/ done indirectly, via E...)
expandStoP :: S -> QMod P
expandStoP (S lambda) = lookupPTable lambda schurTableP

expandStoX :: KnownNat n => S -> ZMod (X n)
expandStoX = convertMtoX . expandStoM

--------------------------------------------------------------------------------
-- * Multiplication

-- | Multiplication using the Littlewood-Richardson rule
mulS :: (Ring c) => FreeMod c S -> FreeMod c S -> FreeMod c S 
mulS a b = ZMod.sum
  [ ZMod.scale (c*d) (ZMod.fromZMod $ expandProductS p q)
  | (p, c) <- ZMod.toList a 
  , (q, d) <- ZMod.toList b
  ] 

expandProductS :: S -> S -> ZMod S
expandProductS (S lambda) (S mu)
  = ZMod.mapCoeff (fromIntegral :: Int -> Integer)  
  $ ZMod.FreeMod $ Map.mapKeys S $ lrMult lambda mu 

--------------------------------------------------------------------------------
-- * Jacobi-Trudi formulas

jacobiTrudiE :: Partition -> ZMod E
jacobiTrudiE part = 
  if isEmptyPartition part
    then ZMod.one
    else clowDeterminant $ jacobiTrudiMatrix f (dualPartition part) 
  where
    f !k | k <  0    = ZMod.zero
         | k == 0    = ZMod.one
         | otherwise = ZMod.generator $ E $ toPartitionUnsafe [k]

jacobiTrudiH :: Partition -> ZMod H
jacobiTrudiH part = 
  if isEmptyPartition part
    then ZMod.one
    else clowDeterminant $ jacobiTrudiMatrix f part 
  where
    f !k | k <  0    = ZMod.zero
         | k == 0    = ZMod.one
         | otherwise = ZMod.generator $ H $ toPartitionUnsafe [k]

jacobiTrudiMatrix :: (Int -> a) -> Partition -> Matrix a
jacobiTrudiMatrix elem part = array ((1,1),(n,n)) [ (ij , f ij) | i<-[1..n] , j<-[1..n] , let ij = (i,j) ] where
  n = partitionWidth part
  f (!i,!j) = elem (arr!i + j - i)          
  arr  = listArray (1,n) $ fromPartition part

--------------------------------------------------------------------------------
-- * Cached tables

schurTableM :: PTable (ZMod M)
schurTableM = schurTableM_shared
-- schurTableM = makePTable $ \lookup part -> calcExpandStoM (S part)

-- | We cache the Schur-expansions, because computing the determinants for large matrices is slow.
-- We only store the H-version (from H and E), because they are dual to each other
schurTableH :: PTable (ZMod H)
schurTableH = makePTable $ \lookup part -> jacobiTrudiH part

schurTableP :: PTable (QMod P)
schurTableP = makePTable $ \lookup part -> convertMtoP (expandStoM (S part))

--------------------------------------------------------------------------------
-- * Uncached computations

-- | Expansion of a Schur polynomials into monomial symmetric polynomials.
-- The coefficients are Kostka numbers.
calcExpandStoM :: S -> ZMod M
calcExpandStoM = calcExpandStoM_shared
-- calcExpandStoM (S part) = ZMod.FreeMod $ Map.mapKeys M $ kostkaNumbersWithGivenLambda part

calcExpandStoE :: S -> ZMod E
calcExpandStoE (S lambda) = jacobiTrudiE lambda

calcExpandStoH :: S -> ZMod H
calcExpandStoH (S lambda) = jacobiTrudiH lambda

--------------------------------------------------------------------------------
-- * Expansion via semistandard Young tableaux

-- | Schur polynomials are a sum over semistandard yount tableaux.
-- This is useful for testing, but it is slow.
--
-- c.f. 'expandStoX'
schurToX_SSYT :: forall n. KnownNat n => S -> ZMod (X n) 
schurToX_SSYT (S lambda) = poly where
  n     = nOfZModX poly
  poly  = FreeMod table
  table = Map.fromListWith (+) $ map (h . f) $ semiStandardYoungTableaux n lambda
 
  xx es = X $ take n $ es ++ repeat 0

  h :: [(Int,Int)] -> (X n, Integer)
  h ies = ( xx (go 1 ies) , 1 ) where
    go :: Int -> [(Int,Int)] -> [Int]
    go !j [] = []
    go !j ((i,e):rest) = replicate (i-j) 0 ++ e : go (i+1) rest 

  f :: Tableau Int -> [(Int,Int)]
  f xs     = map g $ group $ sort $ tableauContent xs
  g (i:is) = (i , 1 + length is) 

{-

-- | Converts a symmetric polynomial to a polynomial of elementary symmetric
-- polynomials
--
-- If the input was not symmetric, we return a symmetric part with 
-- the non-symmetric remainder.
--
{-# SPECIALIZE symmetricReductionSchur :: ZMod XX -> Either (ZMod Schur, ZMod XX) (ZMod Schur) #-}
{-# SPECIALIZE symmetricReductionSchur :: QMod XX -> Either (QMod Schur, QMod XX) (QMod Schur) #-}
symmetricReductionSchur :: forall c. (Eq c, Num c) => FreeMod c XX -> Either (FreeMod c Schur, FreeMod c XX) (FreeMod c Schur)
symmetricReductionSchur = genericSymmetricReduction (Schur . mkPartition)

-}

