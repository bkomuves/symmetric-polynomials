
{-# LANGUAGE ScopedTypeVariables, BangPatterns, FlexibleContexts, NoOverloadedLists #-}
module Math.Algebra.Polynomial.Symmetric.Helpers.Determinant where

--------------------------------------------------------------------------------

import Control.Monad
import Control.Monad.ST

import Data.Array.IArray
import Data.Array.ST
import Data.List
import Data.Ratio
import Data.STRef

import Math.Combinat.Permutations as Perm
import System.Random

-- import Misc

-- import Debug.Trace
-- debug x y = trace ("-- " ++ show x ++ " --") y

--------------------------------------------------------------------------------

type Matrix a = Array (Int,Int) a

randMatrix :: Int -> IO (Matrix Integer)
randMatrix n = do
  xs <- replicateM (n*n) $ randomRIO (-100,100) 
  return $ listArray ((1,1),(n,n)) xs

{-
mat2 = listArray ((1,1),(2,2)) [13,17,19,37] :: Matrix Integer
mat3 = listArray ((1,1),(3,3)) [13,17,19,37,21,56,12,88,137] :: Matrix Integer
-}

--------------------------------------------------------------------------------
-- * CLOW (division-free) determinant algorithm

-- | O(n^4) general division-free determinant algorithm, based
-- on /closed ordered walks/ (clows).
--
-- See: 
--
-- * Gunter Rote: Division-Free Algorithms for the Determinant and the Pfaﬃan: Algebraic and Combinatorial Approaches 
--
clowDeterminant :: forall a. (Eq a, Num a) => Matrix a -> a
clowDeterminant mat = 
  case fst (snd bnds) of
    0 -> 0             -- it's an empty sum (over permutations of the empty set)
    1 -> mat!(1,1)
    2 -> mat!(1,1) * mat!(2,2) - mat!(1,2) * mat!(2,1)
    _ -> go 1 initial 
  where
    ((1,1),(n,m)) = bounds mat
    bnds = if n==m 
      then ((1,1),(n,n)) 
      else error "clowDeterminant: matrix is not square"
  
    iniSign = if odd n then -1 else 1
    initial = accumArray (flip const) 0 bnds [ ((j,j),iniSign) | j<-[1..n] ]
   
    go :: Int -> Matrix a -> a
    go !k !prev 
      | k == n     =  {- debug (k,prev) $ -} final prev
      | otherwise  =  {- debug (k,prev) $ -} go (k+1) (next prev) 
   
    next :: Matrix a -> Matrix a
    next prev = accumArray (+) 0 bnds (arcs1 ++ arcs2) where
    
      arcs1 = [ ( (c',c0), old*cost ) 
              | c0<-[1..n-1], c<-[c0..n] 
              , let !old = prev!(c,c0)
              , old /= 0
              , c'<-[c0+1..n] 
              , let !cost = mat!(c,c')
              ]
              
      arcs2 = [ ( (c0',c0'), old*cost ) 
              | c0<-[1..n-1], c<-[c0..n] 
              , let !old = prev!(c,c0)
              , old /= 0
              , c0'<-[c0+1..n] 
              , let !cost = - mat!(c,c0)   -- c0' ????
              ]
            
    final :: Matrix a -> a  
    final prev = foldl' (+) 0
      [ old*cost  
      | c0<-[1..n], c<-[c0..n] 
      , let !old = prev!(c,c0)
      , old /= 0
      , let !cost = - mat!(c,c0)   -- c0' ???
      ]
  
--------------------------------------------------------------------------------
-- * Naive determinant algorithm

-- | Naive (n!) determinant algorithm, for testing purposes
naiveDeterminant :: Num a => Matrix a -> a
naiveDeterminant mat = det where

  ((1,1),(n,_)) = bounds mat
 
  det = sum 
    [ signValue sgn * product [ mat!(i,j) | (i,j) <- zip [1..] ps ]
    | p<-perms 
    , let sgn = signOfPermutation p 
    , let ps  = fromPermutation p
    ]
    
  perms = Perm.permutations n
    
--------------------------------------------------------------------------------
-- * Bareiss determinant algorithm for integers

type STMatrix s a = STArray s (Int,Int) a

-- | Works only if the top-left minors all have nonzero determinants
bareissDeterminantFullRank :: forall a . Integral a => Matrix a -> a
bareissDeterminantFullRank mat = 
  if n>0 
    then runST $ do
      ar1   <- thaw mat       :: ST s (STMatrix s a)  
      ar2   <- newArray_ siz  :: ST s (STMatrix s a)
      last  <- newSTRef 1     :: ST s (STRef s a)
      (ar,_) <- foldM (worker last) (ar1,ar2) [1..n-1] 
      readArray ar (n,n) 
    else 1  -- determinant of the empty matrix is 1
  where 
    siz@((1,1),(n,_)) = bounds mat
    worker last (ar1,ar2) k = do
      q <- readSTRef last             
      forM_ [k+1..n] $ \i -> 
        forM_ [k+1..n] $ \j -> do
          a <- readArray ar1 (k,k)
          b <- readArray ar1 (i,k)
          c <- readArray ar1 (k,j)
          d <- readArray ar1 (i,j)
          writeArray ar2 (i,j) $ (a*d - b*c) `div` q      
      readArray ar1 (k,k) >>= writeSTRef last 
      return (ar2,ar1)
      
--------------------------------------------------------------------------------
-- * Symbolic Gauss elimination

data FreeField a 
  = Add (FreeField a) (FreeField a)
  | Sub (FreeField a) (FreeField a)
  | Mul (FreeField a) (FreeField a)
  | Div (FreeField a) (FreeField a)
  | Atom a 
  | Zero
  deriving (Eq,Ord,Show)

instance Num (FreeField a) where
  (+) = Add
  (-) = Sub
  (*) = Mul
  fromInteger  = error "FreeField/fromInteger"
  abs          = error "FreeField/abs"
  signum       = error "FreeField/signum"

instance Fractional (FreeField a) where
  (/) = Div
  fromRational = error "FreeField/fromRational"
  
symbolicGaussElim :: forall a. (Eq a, Num a) => Matrix a -> [FreeField a]
symbolicGaussElim orig = diagonal where  
  siz@((1,1),(n,_)) = bounds orig
  fmatrix = amap Atom orig :: Matrix (FreeField a)
  
  diagonal = runST $ do
    mat <- thaw fmatrix :: ST s (STMatrix s (FreeField a))
    sequence [ gauss mat k         | k<-[1..n-1] ]
    sequence [ readArray mat (k,k) | k<-[1..n  ] ]
 
  gauss :: STMatrix s (FreeField a) -> Int -> ST s ()
  gauss mat k = do
    d <- readArray mat (k,k)
    forM_ [k+1..n] $ \j -> do
      b <- readArray mat (k,j)
      let q = b/d
      forM_ [k+1..n] $ \i -> do
        y <- readArray mat (i,k)
        x <- readArray mat (i,j)
        writeArray mat (i,j) (x - q*y)
      writeArray mat (k,j) Zero 

--------------------------------------------------------------------------------

{-      
data X = X [Int] | Z deriving (Eq,Show)

pp :: (FreeField X) -> String
pp = go where
  go (Atom Z) = "0"
  go (Atom (X ks)) = "h[" ++ intercalate "," (map show ks) ++ "]"
  go (Add x y) = "(" ++ go x ++ "+" ++ go y ++ ")"
  go (Sub x y) = "(" ++ go x ++ "-" ++ go y ++ ")"
  go (Mul x y) = "(" ++ go x ++ "*" ++ go y ++ ")"
  go (Div x y) = "(" ++ go x ++ "/" ++ go y ++ ")"
  go Zero = "0"
  
-- testfile = writeFile "testmat_det" $ intercalate " * " (map pp $ symbolicGaussElim testmat)

instance Num X where
  (*) (X a) (X b) = X (a++b)
        
testmat :: Matrix X        
testmat = array ((1,1),(n,n)) [ ( (i,j), h i j ) | i<-[1..n] , j<-[1..n] ] where
  lam = [6,3,1,1]
  n = length lam
  h i j = let k = lam!!(i-1) + j - i 
          in  if k<0 then Z else X [k]
-}

--------------------------------------------------------------------------------
