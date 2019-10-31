
-- | Lazy infinite tables indexed by nonnegative integers and partitions

module Math.Algebra.Polynomial.Symmetric.Helpers.Tables where

--------------------------------------------------------------------------------

import Data.List
import Data.Array

import Math.Combinat.Partitions.Integer

import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map

--------------------------------------------------------------------------------

arrSize :: Int
arrSize = 32

--------------------------------------------------------------------------------
-- * Tables indexed by integers

-- | A table indexed by nonnegative integers, with efficient lookup for small indices
newtype ITable a = ITable [Array Int a] 

indexITable :: ITable a -> Int -> a
indexITable = flip lookupITable

lookupITable :: Int -> ITable a -> a
lookupITable n (ITable list) = (list!!k) ! r where
  (k,r) = divMod n arrSize

makeITable :: ((Int -> a) -> (Int -> a)) -> ITable a 
makeITable f = table where
  table = itableFromFun (f lkp)
  lkp i = lookupITable i table

itableFromFun :: (Int -> a) -> ITable a
itableFromFun f = itableFromList $ map f [0..]

itableFromList :: [a] -> ITable a
itableFromList list = ITable (go list) where
  go xs = let (this,rest) = splitAt arrSize xs 
          in  listArray (0,arrSize-1) this : go rest

--------------------------------------------------------------------------------
-- * Tables indexed by partitions

-- | A table indexed by partitions. Note: because internally it is a sequence
-- of lazy 'Map'-s, and the spine of even the lazy 'Map' is strict, it is not recommended
-- to use this structure for partitions of weight over, say, 40-50.
--
newtype PTable a = PTable (ITable (Map Partition a)) 

indexPTable :: PTable a -> Partition -> a
indexPTable = flip lookupPTable

lookupPTable :: Partition -> PTable a -> a
lookupPTable p (PTable table) = (Map.!) (lookupITable n table) p  where
  n = partitionWeight p

makePTable :: ((Partition -> a) -> (Partition -> a)) -> PTable a 
makePTable f = table where
  table = ptableFromFun (f lkp)
  lkp p = lookupPTable p table

ptableFromFun :: (Partition -> a) -> PTable a
ptableFromFun f = PTable $ itableFromList [ Map.fromList [ (p, f p) | p <- partitions n ] | n<-[0..] ] 

--------------------------------------------------------------------------------
