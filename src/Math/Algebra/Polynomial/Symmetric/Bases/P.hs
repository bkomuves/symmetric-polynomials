
-- | Power symmetric polynomials
-- 
-- See eg. <https://en.wikipedia.org/wiki/Power_sum_symmetric_polynomial>
--
{-# LANGUAGE BangPatterns #-}
module Math.Algebra.Polynomial.Symmetric.Bases.P where

--------------------------------------------------------------------------------

import Data.List
-- import Data.Ord

import GHC.TypeLits

import Math.Combinat.Sets
import Math.Combinat.Permutations ( permuteMultiset )
import Math.Combinat.Partitions.Integer
import Math.Combinat.Partitions.Skew ( outerPartition )

import Math.Algebra.Polynomial.Symmetric.Types
import Math.Algebra.Polynomial.Symmetric.Newton

import Math.Algebra.Polynomial.FreeModule ( ZMod , QMod, FreeMod )
import qualified Math.Algebra.Polynomial.FreeModule as ZMod

import Math.Algebra.Polynomial.Symmetric.Helpers.Tables
import Math.Algebra.Polynomial.Symmetric.Helpers.Misc ( chooseWith , equating )

import Math.Combinat.Partitions.Skew.Ribbon

--------------------------------------------------------------------------------
-- * Conversions to different bases

convertPtoE :: (Ring c) => FreeMod c P -> FreeMod c E
convertPtoE =  ZMod.flatMap (ZMod.fromZMod . expandPtoE) 

convertPtoH :: (Ring c) => FreeMod c P -> FreeMod c H
convertPtoH =  ZMod.flatMap (ZMod.fromZMod . expandPtoH)

convertPtoS :: (Ring c) => FreeMod c P -> FreeMod c S
convertPtoS =  ZMod.flatMap (ZMod.fromZMod . expandPtoS)

convertPtoM :: (Ring c) => FreeMod c P -> FreeMod c M
convertPtoM =  ZMod.flatMap (ZMod.fromZMod . expandPtoM)

--------------------------------------------------------------------------------
-- * Expansions of P-monomials into other bases

expandPtoE :: P -> ZMod E
expandPtoE (P part) = lookupPTable part ptablePinE

-- | Note: by duality, the coefficients of these are the same as the E-expansion, modulo signs.
expandPtoH :: P -> ZMod H 
expandPtoH (P part) = lookupPTable part ptablePinH

expandPtoS :: P -> ZMod S
expandPtoS (P part) = lookupPTable part ptablePinS

expandPtoM :: P -> ZMod M
expandPtoM (P part) = lookupPTable part ptablePinM

--------------------------------------------------------------------------------
-- * Expansion of @p_k@

-- | @powerSymmPolyX k@ is the @k@-th power symmetric polynomial in @n@ variables
powerSymmPolyX :: (Eq c, Num c, KnownNat n) => Int -> FreeMod c (X n)
powerSymmPolyX k = poly where
  n = nOfZModX poly
  poly 
    | k <  0     = ZMod.zero
    | k == 0     = ZMod.konst (fromIntegral n)
    | otherwise  = ZMod.fromGeneratorList $ map X $ [ f i | i <- [1..n] ]
  f i = replicate (i-1) 0 ++ k : replicate (n-i) 0

powerSymmPolyM :: Num c => Int -> FreeMod c M
powerSymmPolyM k 
  | k > 0      = ZMod.generator $ M $ toPartitionUnsafe [k]
  | otherwise  = error "powerSymmPolyM: k > 0 is required"

--------------------------------------------------------------------------------
-- * Cached tables

ptablePinE :: PTable (ZMod E)
ptablePinE = makePTable $ \lookup (Partition ps) -> case ps of
  []     -> ZMod.generator (E emptyPartition)
  (r:rs) -> ZMod.mul (lookupITable r newtonTablePinE) (lookup $ toPartitionUnsafe rs)
 
ptablePinH :: PTable (ZMod H)
ptablePinH = makePTable $ \lookup (Partition ps) -> case ps of
  []     -> ZMod.generator (H emptyPartition)
  (r:rs) -> ZMod.mul (lookupITable r newtonTablePinH) (lookup $ toPartitionUnsafe rs)

-- | This uses the border strip (or ribbon) expansion @s[mu]*p[k]@  recursively
ptablePinS :: PTable (ZMod S)
ptablePinS = makePTable $ \lookup (Partition ps) -> case ps of
  []     -> ZMod.generator (S emptyPartition)
  (r:rs) -> ZMod.flatMap f (lookup $ toPartitionUnsafe rs) where
    f s = calcExpandStimesPk s r

-- | This uses the expansion of @m[mu]*p[k]@ recursively
ptablePinM :: PTable (ZMod M)
ptablePinM = makePTable $ \lookup (Partition ps) -> case ps of
  []     -> ZMod.generator (M emptyPartition)
  (r:rs) -> ZMod.flatMap f (lookup $ toPartitionUnsafe rs) where
    f s = calcExpandMtimesPk s r

--------------------------------------------------------------------------------
-- * Expansion to power symmetric polynomials via border strips

-- | The expansion o the product @s[mu]*p[k]@ in terms of Schur polynomials
-- is a signed sum over border strips of length @k@.
calcExpandStimesPk :: S -> Int -> ZMod S
calcExpandStimesPk (S mu) k = ZMod.fromList
  [ (S lambda, cf) 
  | Ribbon shape _ ht _ <- outerRibbonsOfLength mu k 
  , let lambda = outerPartition shape
  , let cf = if odd ht then -1 else 1
  ]

-- | Expansion of @m[lambda] * p[k]@ in terms of M-monomials
calcExpandMtimesPk :: M -> Int -> ZMod M
calcExpandMtimesPk (M (Partition part0)) k = ZMod.fromList list where
  n    = length part0
  part = part0 ++ [0]
  idxs = map fst $ map head $ groupBy (equating snd) $ zip [0..] part
  list = [ (M lambda, coeff) 
         | i<-idxs 
         , let lambda = mkPartition (add_ith i part k) 
         , let u = (part!!i) + k
         , let coeff = sum [ 1 | x <- fromPartition lambda , x == u ]
         ]

  add_ith :: Int -> [Int] -> Int -> [Int]
  add_ith !i part !k  = take i part ++ add_head (drop i part) k

  add_head :: [Int] -> Int -> [Int]
  add_head []      !k = [k]
  add_head (!x:xs) !k = (x+k : xs)

-- | Naive (and very slow) implementation of @m[lambda] * p[k]@ for reference
calcExpandMtimesPkNaive :: M -> Int -> ZMod M
calcExpandMtimesPkNaive (M (Partition part)) k = ZMod.fromList list where
  list = [ (M (mkPartition fs) , 1) 
         | es <- permuteMultiset (part ++ [0])
         , fs <- chooseWith id (+k) 1 es 
         , isDecreasing fs 
         ]
  
  isDecreasing :: [Int] -> Bool  
  isDecreasing = go where
    go (x:rest@(y:_)) = x >= y && go rest
    go [x]            = x >= 0
    go []             = True
                    

--------------------------------------------------------------------------------
-- * Uncached computations

-- | This simply multiplies together elements looked up from tables of Newton identities
calcExpandPtoE :: P -> ZMod E
calcExpandPtoE (P part) = ZMod.product [ lookupITable k newtonTablePinE | k <- fromPartition part ]

-- | This also just multiplies together elements looked up from tables of Newton identities
calcExpandPtoH :: P -> ZMod H 
calcExpandPtoH (P part) = ZMod.product [ lookupITable k newtonTablePinH | k <- fromPartition part ]

--------------------------------------------------------------------------------
