
-- | Newton's identities, which recursively express @p[i]@ 
-- in @e[j]@-s and vica versa (and similarly for @h[j]@ instead of @e[j]@).
--
-- See <https://en.wikipedia.org/wiki/Newton's_identities>
--
module Math.Algebra.Polynomial.Symmetric.Newton 
  ( -- * Newton's identities for the elementary symmetric polynomials
    newtonTablePinE
  , newtonTableEinP
    -- * Newton's identities for the complete symmetric olynomials
  , newtonTablePinH
  , newtonTableHinP
  )
  where

--------------------------------------------------------------------------------

import Math.Combinat.Partitions.Integer

import Math.Algebra.Polynomial.Symmetric.Types

import Math.Algebra.Polynomial.FreeModule ( ZMod , QMod, FreeMod )
import qualified Math.Algebra.Polynomial.FreeModule as ZMod

import Math.Algebra.Polynomial.Symmetric.Helpers.Tables

--------------------------------------------------------------------------------

-- | @p[i]@ expanded in elementary symmetric polynomials. Note: @i>0@ is required!
--
-- See eg. <https://en.wikipedia.org/wiki/Newton%27s_identities>
--
newtonTablePinE :: ITable (ZMod E)
newtonTablePinE = makeITable calc where
  calc lookup n
    | n <= 0    = error "newtonTablePinE: this requires n > 0"
    | n == 1    = ZMod.generator (mkE1 1)
    | otherwise = ZMod.add hd tl where
        hd = ZMod.singleton (mkE1 n) (fromIntegral $ if odd n then n else negate n)
        tl = ZMod.sum [ negateIfOdd (n-1+j) $ insertE (n-j) (lookup j) | j<-[1..n-1] ]

--------------------------------------------------------------------------------

-- | @p[i]@ expanded in complete symmetric polynomials. Note: @i>0@ is required!
newtonTablePinH :: ITable (ZMod H)
newtonTablePinH = makeITable calc where
  calc lookup n 
    | n <= 0    = error "newtonTablePinH: this requires n > 0"
    | n == 1    = ZMod.generator (mkH1 1)
    | otherwise = ZMod.sub hd tl where
        hd = ZMod.singleton (mkH1 n) (fromIntegral n)
        tl = ZMod.sum [ insertH (n-j) (lookup j) | j<-[1..n-1] ]

--------------------------------------------------------------------------------

-- | @e[k]@ expaned in power symmetric polynomials. We also have an explicit formula for these:
--
-- > e[k] == sum [ (epsilon lambda / zee lambda) * p[lambda] | lambda <- partitions k ]
--
-- which should be faster to use (see 'itableEinP' for that)
--
newtonTableEinP :: ITable (QMod P)
newtonTableEinP = makeITable calc where
  calc lookup n 
    | n == 0    = ZMod.generator p_empty
    | n == 1    = ZMod.generator (mkP1 1)
    | otherwise = ZMod.scale (1 / fromIntegral n) $ ZMod.add hd tl where
        hd = ZMod.singleton (mkP1 n) (fromIntegral $ if odd n then 1 else (-1))
        tl = ZMod.sum [ negateIfOdd (j-1) $ insertP j (lookup (n-j)) | j<-[1..n-1] ]

--------------------------------------------------------------------------------

-- | @h[k]@ expaned in power symmetric polynomials. We also have an explicit formula for these:
--
-- > h[k] == sum [ (1 / zee lambda) * p[lambda] | lambda <- partitions k ]
--
-- which should be faster to use (see 'itableHinP' for that).
--
newtonTableHinP :: ITable (QMod P)
newtonTableHinP = makeITable calc where
  calc lookup n 
    | n == 0    = ZMod.generator p_empty
    | n == 1    = ZMod.generator (mkP1 1)
    | otherwise = ZMod.scale (1 / fromIntegral n) $ ZMod.add hd tl where
        hd = ZMod.generator (mkP1 n) 
        tl = ZMod.sum [ insertP j (lookup (n-j)) | j<-[1..n-1] ]

--------------------------------------------------------------------------------

negateIfOdd :: (Ord b, Num c) => Int -> FreeMod c b -> FreeMod c b
negateIfOdd k = if odd k then ZMod.neg else id

mkE1 :: Int -> E
mkE1 n = E (toPartitionUnsafe [n]) 

mkH1 :: Int -> H
mkH1 n = H (toPartitionUnsafe [n]) 

mkP1 :: Int -> P
mkP1 n = P (toPartitionUnsafe [n]) 

p_empty :: P
p_empty = P (toPartitionUnsafe [])
 
insertE :: Int -> ZMod E -> ZMod E
insertE j = ZMod.unsafeMapBase f where
  f (E es) = E $ mkPartition (j : fromPartition es)    -- this is an injective operation, so it's safe to do

insertH :: Int -> ZMod H -> ZMod H
insertH j = ZMod.unsafeMapBase f where
  f (H es) = H $ mkPartition (j : fromPartition es)

insertP :: Int -> QMod P -> QMod P
insertP j = ZMod.unsafeMapBase f where
  f (P es) = P $ mkPartition (j : fromPartition es)

--------------------------------------------------------------------------------


