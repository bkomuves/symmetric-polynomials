
-- | Elementary symmetric polynomials
--
-- See <https://en.wikipedia.org/wiki/Elementary_symmetric_polynomial>
--

{-# LANGUAGE BangPatterns #-}
module Math.Algebra.Polynomial.Symmetric.Bases.E where

--------------------------------------------------------------------------------

import GHC.TypeLits

import qualified Data.Map as Map

import Math.Combinat.Sets
import Math.Combinat.Numbers
import Math.Combinat.Permutations ( permuteMultiset )
import Math.Combinat.Partitions.Integer
import Math.Combinat.Partitions.Skew
import Math.Combinat.Tableaux.GelfandTsetlin

import Math.Algebra.Polynomial.Symmetric.Types
import Math.Algebra.Polynomial.Symmetric.Newton
import Math.Algebra.Polynomial.Symmetric.ScalarProd

import Math.Algebra.Polynomial.FreeModule ( ZMod , QMod, FreeMod )
import qualified Math.Algebra.Polynomial.FreeModule as ZMod

import Math.Algebra.Polynomial.Symmetric.Helpers.Misc
import Math.Algebra.Polynomial.Symmetric.Helpers.Tables

--------------------------------------------------------------------------------
-- * Conversions to other bases

convertEtoS :: Ring c => FreeMod c E -> FreeMod c S
convertEtoS = ZMod.flatMap (ZMod.fromZMod . expandEtoS) 

convertEtoM :: Ring c => FreeMod c E -> FreeMod c M
convertEtoM = ZMod.flatMap (ZMod.fromZMod . expandEtoM) 

convertEtoP :: CoeffRing c => FreeMod c E -> FreeMod (FieldOfFractions c) P
convertEtoP = ZMod.flatMap (ZMod.fromQMod . expandEtoP) 
            . ZMod.unsafeCoeffChange embedToFractions

-- convertEtoX :: (Ring c, KnownNat n) => FreeMod c E -> FreeMod c (X n)
-- convertEtoX = ZMod.flatMap (ZMod.fromZMod . expandEtoX)

convertEtoE' :: FreeMod c E -> FreeMod c E'
convertEtoE' = ZMod.unsafeMapBase f where f (E p) = E' (dualPartition p) 

--------------------------------------------------------------------------------
-- * Expansion of E-monomials into other symmetric functions

expandEtoS :: E -> ZMod S
expandEtoS (E part) = lookupPTable part ptableEinS

expandEtoM :: E -> ZMod M
expandEtoM (E part) = lookupPTable part ptableEinM

expandEtoP :: E -> QMod P
expandEtoP (E part) = lookupPTable part ptableEinP

-- expandEtoX :: (KnownNat n) => M -> ZMod (X n)
-- expandEtoX = 

--------------------------------------------------------------------------------
-- * Expansion of @e_i@

elementarySymmPolyM :: Num c => Int -> FreeMod c M
elementarySymmPolyM k = ZMod.generator $ M $ toPartitionUnsafe $ replicate k 1

-- | @elementarySymmPolyX k@ is the @k@-th elementary symmetric polynomial in @n@ variables
elementarySymmPolyX :: (Eq c, Num c, KnownNat n) => Int -> FreeMod c (X n)
elementarySymmPolyX k = poly where
  n = nOfZModX poly
  poly 
    | k <  0     = ZMod.zero
    | k == 0     = ZMod.one
    | k >  n     = ZMod.zero
    | otherwise  = ZMod.fromGeneratorList $ map X $ chooseWith (const 0) (const 1) k (replicate n ())

--------------------------------------------------------------------------------
-- * Cached tables

-- | Expansion of an E-monom in the Schur basis 
ptableEinS :: PTable (ZMod S)
ptableEinS = makePTable $ \lookup part -> calcExpandEinS (E part) 

-- | Expansion of @e[k]@ in P-basis 
itableEinP :: ITable (QMod P)
itableEinP = itableFromFun $ calcEkInP

-- | Expansion of an E-monom in the P-basis 
ptableEinP :: PTable (QMod P)
ptableEinP = makePTable $ \lookup part -> case fromPartition part of
  []     -> ZMod.one
  [n]    -> lookupITable n itableEinP
  (n:ks) -> ZMod.mul (lookupITable n itableEinP) (lookup $ toPartitionUnsafe ks)

-- | This uses the below expansion of @m[lambda]*e[k]@  recursively
ptableEinM :: PTable (ZMod M)
ptableEinM = makePTable $ \lookup (Partition ps) -> case ps of
  []     -> ZMod.generator (M emptyPartition)
  (r:rs) -> ZMod.flatMap f (lookup $ toPartitionUnsafe rs) where
    f mm = calcExpandMtimesEk mm r

--------------------------------------------------------------------------------
-- * The expansion of @m[lambda] * e[k]@

-- | The expansion of @m[lambda] * e[k]@. This can be understood combinatorially,
-- and is quite fast
calcExpandMtimesEk :: M -> Int -> ZMod M
calcExpandMtimesEk (M part) n = result where
  dpart@(Partition es')   = dualPartition part
  support = dualPieriRule part n
  result  = ZMod.fromList [ (M q, coeff q) | q <- support ]
  coeff q = product factors where
    SkewPartition pairs = mkSkewPartition (dualPartition q, dpart)
    factors   = zipWith f pairs (tail pairs ++ repeat (0,0))
    f (!a,!k) (!b,!l) = binomial (a+k-b-l) k  

-- | The monomial symmetric polynomial is by definition the sum over all permutations 
-- of the multiset of exponents; multiplying this by an elementary symmetric polynomial,
-- we add 1 to a subset of each exponent. This allows to compute this expansion.
--
-- This naive implementation is very slow !!!
calcExpandMtimesEkNaive :: M -> Int -> ZMod M
calcExpandMtimesEkNaive (M (Partition es)) n = ZMod.fromGeneratorList list where

  list = 
    [ M r     
    | p <- perms
    , q <- addExpos n p
    , ispartition q
    , let r = toPartitionUnsafe $ filter (/=0) q 
    ]

  -- adding the n zeros is important also for the multiplicities !!!
  perms = filter precond $ permuteMultiset (es ++ replicate n 0) 

  addExpos !k ps = chooseWith id (+1) k ps

  -- we want to final sequences to be non-increasing, but we only add at most 1
  precond :: [Int] -> Bool
  precond (x:rest@(y:_)) = (x >= y-1) && precond rest
  precond []  = True
  precond [x] = x >= 0

  -- for the final check
  ispartition :: [Int] -> Bool
  ispartition (x:rest@(y:_)) = (x >= y) && ispartition rest
  ispartition []  = True
  ispartition [x] = x >= 0

--------------------------------------------------------------------------------
-- * Uncached computations

-- | Expansion of an E-monom in the Schur basis (using the iterated Pieri rule)
calcExpandEinS :: E -> ZMod S
calcExpandEinS (E part) = ZMod.FreeMod $ Map.mapKeys S $ iteratedDualPieriRule $ reverse $ fromPartition part

-- | Expansion of @e[k]@ in P-basis (using the explicit formula)
calcEkInP :: Int -> QMod P
calcEkInP n = ZMod.fromList 
  [ (P lambda , fromInteger (epsilon lambda) / fromInteger (zee lambda)) | lambda <- partitions n ]

-- | Expansion of an E-monom in the P basis (multiplying together the explicit formula)
calcExpandEtoP :: E -> QMod P
calcExpandEtoP (E part) = ZMod.product [ calcEkInP e | e <- fromPartition part ]

--------------------------------------------------------------------------------
