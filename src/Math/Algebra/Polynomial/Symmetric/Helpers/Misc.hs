
-- | Some auxilary functions

{-# LANGUAGE BangPatterns, TypeSynonymInstances, FlexibleInstances, DeriveFunctor #-}
module Math.Algebra.Polynomial.Symmetric.Helpers.Misc where

--------------------------------------------------------------------------------

import Data.List
import Data.Monoid
import Data.Ratio

import Control.Monad

import System.Random

import Math.Combinat.Numbers
import Math.Combinat.Sign
import Math.Combinat.Partitions.Integer 
import Math.Combinat.Partitions.Integer.Count 
import Math.Combinat.Partitions.Set
import Math.Combinat.Sets

import qualified Data.Map.Strict as Map
import Data.Map (Map)

--------------------------------------------------------------------------------

{-
-- * Pairs

data Pair a 
  = Pair a a 
  deriving (Eq,Ord,Show,Functor)
-}

--------------------------------------------------------------------------------

equating :: Eq b => (a -> b) -> a -> a -> Bool  
equating f x y = (f x == f y)

--------------------------------------------------------------------------------
-- * Lists

{-# SPECIALIZE unique :: [Partition] -> [Partition] #-}
unique :: Ord a => [a] -> [a]
unique = map head . group . sort

-- | Synonym for histogram
count :: Ord b => [b] -> Map b Integer
count = histogram

{-# SPECIALIZE histogram :: [Partition] -> Map Partition Integer #-}
histogram :: Ord b => [b] -> Map b Integer
histogram xs = foldl' f Map.empty xs where
  f old x = Map.insertWith (+) x 1 old

--------------------------------------------------------------------------------
-- * Maps
  
deleteLookup :: Ord a => a -> Map a b -> (Maybe b, Map a b)
deleteLookup k table = (Map.lookup k table, Map.delete k table)  

unsafeDeleteLookup :: Ord a => a -> Map a b -> (b, Map a b)
unsafeDeleteLookup k table = (fromJust (Map.lookup k table), Map.delete k table) where
  fromJust mb = case mb of
    Just y  -> y
    Nothing -> error "unsafeDeleteLookup: key not found"

-- | Example usage: @insertMap (:[]) (:) ...@
insertMap :: Ord k => (b -> a) -> (b -> a -> a) -> k -> b -> Map k a -> Map k a
insertMap f g k y = Map.alter h k where
  h mb = case mb of
    Nothing -> Just (f y)
    Just x  -> Just (g y x)    

-- | Example usage: @buildMap (:[]) (:) ...@
buildMap :: Ord k => (b -> a) -> (b -> a -> a) -> [(k,b)] -> Map k a
buildMap f g xs = foldl' worker Map.empty xs where
  worker !old (k,y) = Map.alter h k old where
    h mb = case mb of
      Nothing -> Just (f y)
      Just x  -> Just (g y x)    

--------------------------------------------------------------------------------
-- * Partitions

-- | @aut(mu)@ is the number of symmetries of the partition mu:
--
-- > aut(mu) = prod_r (e_r)!
--
-- where @mu = (1^e1 2^e2 .. k^ek)@
aut :: Partition -> Integer
aut part = product $ map factorial es where
  es = map snd $ toExponentialForm part   

--------------------------------------------------------------------------------
-- * Partition functions  (TODO: move into combinat)

conjugateLexicographicCompare :: Partition -> Partition -> Ordering
conjugateLexicographicCompare p q = compare (dualPartition q) (dualPartition p) 

newtype ConjLex = ConjLex Partition deriving (Eq,Show)

fromConjLex :: ConjLex -> Partition
fromConjLex (ConjLex p) = p

instance Ord ConjLex where
  compare (ConjLex p) (ConjLex q) = conjugateLexicographicCompare p q

-- {- CONJUGATE LEXICOGRAPHIC ordering is a refinement of dominance partial ordering -}
-- let test n = [ ConjLex p >= ConjLex q | p <- partitions n , q <-partitions n ,  p `dominates` q ]
-- and (test 20)

-- | Dominance partial ordering as a partial ordering.
dominanceCompare :: Partition -> Partition -> Maybe Ordering
dominanceCompare p q  
  | p==q             = Just EQ
  | p `dominates` q  = Just GT
  | q `dominates` p  = Just LT
  | otherwise        = Nothing

-- {- LEXICOGRAPHIC ordering is a refinement of dominance partial ordering -}
-- let test n = [ p >= q | p <- partitions n , q <-partitions n ,  p `dominates` q ]
-- and (test 20)

--------------------------------------------------------------------------------

-- | Uniform distribution on the partitions of weight at most @n@
randomPartitionOfSizeAtMost :: RandomGen g => Int -> g -> (Partition, g) 
randomPartitionOfSizeAtMost n g0 = randomPartition k g1 where
  (j,g1) = randomR (0,m-1) g0
  m = partitionCountPartialSums !! (n+1)
  k = -1 + (length $ takeWhile (<=j) partitionCountPartialSums)

-- partitionCountList :: [Integer]
-- partitionCountList = [ countPartitions n | n<-[0..] ]

partitionCountPartialSums :: [Integer]
partitionCountPartialSums = scanl (+) 0 partitionCountList

liftRandomElemOfSize :: RandomGen g => (Partition -> a) -> Int -> g -> (a,g)
liftRandomElemOfSize con n g = let (p,g') = randomPartition n g in (con p, g') 

liftRandomElemOfSizeAtMost :: RandomGen g => (Partition -> a) -> Int -> g -> (a,g)
liftRandomElemOfSizeAtMost con n g = let (p,g') = randomPartitionOfSizeAtMost n g in (con p, g')

 
{-
-- {- already defined in Math.Combinat -} 
-- histogram :: Ord a => [a] -> [(a,Int)]
-- histogram = map f . group . sort where
--   f xs = (fst xs, length xs)

testRndPart1 m k = liftM histogram $ replicateM m $ getStdRandom (randomPartition k)
testRndPart  m k = liftM histogram $ replicateM m $ getStdRandom (randomPartitionOfSizeAtMost k)
-}

--------------------------------------------------------------------------------
-- * Set partitions
 
-- | Makes set partition from a partition (simply filling up from left to right)
-- with the shape giving back the input partition
defaultSetPartition :: Partition -> SetPartition
defaultSetPartition = SetPartition . linearIndices

-- | Produce linear indices from a partition @nu@ (to encode the diagonal map @Delta_nu@).
linearIndices :: Partition -> [[Int]]
linearIndices (Partition ps) = go 0 ps where
  go _  []     = []
  go !k (a:as) = [k+1..k+a] : go (k+a) as

--------------------------------------------------------------------------------
-- * Signs

class IsSigned a where
  signOf :: a -> Maybe Sign

signOfNum :: (Ord a, Num a) => a -> Maybe Sign 
signOfNum x = case compare x 0 of
  LT -> Just Minus
  GT -> Just Plus
  EQ -> Nothing

instance IsSigned Int      where signOf = signOfNum
instance IsSigned Integer  where signOf = signOfNum
instance IsSigned Rational where signOf = signOfNum

--------------------------------------------------------------------------------
-- * Numbers

fromRat :: Rational -> Integer
fromRat r = case denominator r of
  1 -> numerator r
  _ -> error "fromRat: not an integer"    

safeDiv :: Integer -> Integer -> Integer
safeDiv a b = case divMod a b of
  (q,0) -> q
  (q,r) -> error $ "saveDiv: " ++ show a ++ " = " ++ show b ++ " * " ++ show q ++ " + " ++ show r

--------------------------------------------------------------------------------
-- * Combinatorics

-- | @chooseWith f g k xs@ chooses @k@ elements from xs, and
-- then for those selected applies @g@, for those unselected applies @f@,
-- and returns the resulting list of lists.
chooseWith :: (a -> b) -> (a -> b) -> Int -> [a] -> [[b]]
chooseWith f g n = (map . map) (either f g) . chooseTagged n 

-- | Chooses (n-1) elements out of n
chooseN1 :: [a] -> [[a]]
chooseN1 = go where
  go (x:xs) = xs : map (x:) (go xs)
  go []     = []
  
symPolyNum :: Num a => Int -> [a] -> a
symPolyNum k xs = sum' (map prod' $ choose k xs) where
  sum'  = foldl' (+) 0
  prod' = foldl' (*) 1

--------------------------------------------------------------------------------
