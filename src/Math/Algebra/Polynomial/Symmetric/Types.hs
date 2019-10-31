
{-# LANGUAGE 
      BangPatterns, DataKinds, KindSignatures, TypeFamilies,
      ConstraintKinds, FlexibleContexts, FlexibleInstances, TypeSynonymInstances
  #-}
module Math.Algebra.Polynomial.Symmetric.Types where

--------------------------------------------------------------------------------

import Data.List

-- Semigroup became a superclass of Monoid
#if MIN_VERSION_base(4,11,0)     
import Data.Foldable
import Data.Semigroup
#endif

import Data.Typeable
import Data.Proxy

import GHC.TypeLits
import GHC.Exts

import Math.Combinat.Partitions.Integer

import Math.Algebra.Polynomial.Pretty
import Math.Algebra.Polynomial.Symmetric.Helpers.Misc

import Math.Algebra.Polynomial.FreeModule ( FreeMod )
import qualified Math.Algebra.Polynomial.FreeModule as ZMod

--------------------------------------------------------------------------------
-- * Coefficient rings

type Ring  c = (Eq c, Num c, Show c, Typeable c) 
type Field c = (Ring c, Fractional c)

-- | A class for coefficient rings
class (Ring c, Field (FieldOfFractions c)) => CoeffRing c where
  type FieldOfFractions c :: *
  embedToFractions :: c -> FieldOfFractions c

instance CoeffRing Integer where
  type FieldOfFractions Integer = Rational
  embedToFractions = fromInteger

instance CoeffRing Rational where
  type FieldOfFractions Rational = Rational
  embedToFractions = id

--------------------------------------------------------------------------------
-- * Different bases

-- | Elementary symmetric polynomials @e[4,2,2,1] = e[4]*e[2]^2*e[1]@
newtype E = E Partition deriving (Eq,Ord,Show)

-- | Elementary symmetric polynomials, indexed by the dual partition
-- @e'[5,4,1] = e[3,2,2,2,1] = e[3]*e[2]^3*e[1]@.
--
-- This convention can be more convenient when working in the ring @\Lambda_n@
newtype E' = E' Partition deriving (Eq,Ord,Show)

-- | Complete symmetric polynomials @h[4,2,2,1] = h[4]*h[2]^2*h[1]@
newtype H = H Partition deriving (Eq,Ord,Show)

-- | Power symmetric polynomials @p[4,2,2,1] = p[4]*p[2]^2*p[1]@
newtype P = P Partition deriving (Eq,Ord,Show)

-- | Schur polynomials, eg. @s[3,2,1,1]@
newtype S = S Partition deriving (Eq,Ord,Show)

-- | Monomial symmetric polynomials, eg. @m[3,2,1,1] = x1^3*x2^2*x3*x4 + ...@
newtype M = M Partition deriving (Eq,Ord,Show)

-- | The \"forgotten\" symmetric polynomials (duals to the elementary symmetric polynomials)
newtype F = F Partition deriving (Eq,Ord,Show)

--------------------------------------------------------------------------------

-- | Monomials of the variables @x1,x2,...,xn@. The internal representation is the
-- list of exponents: @x1^e1*x2^e2*...*xn^en@ is represented by @[e1,e2,...,en]@.
--
-- Note that we require here that the list has always length @n@!
newtype X (n :: Nat) = X [Int] deriving (Eq,Show)

-- because of how we encode it (list of exponents), the opposite order 
-- is more natural for printing out terms
instance Ord (X n) where compare (X a) (X b) = compare b a

nOfX :: KnownNat n => X n -> Int
nOfX = fromInteger . natVal . natProxy where
  natProxy :: X n -> Proxy n
  natProxy _ = Proxy

nOfZModX :: KnownNat n => FreeMod c (X n) -> Int
nOfZModX = fromInteger . natVal . natProxy where
  natProxy :: FreeMod c (X n) -> Proxy n
  natProxy _ = Proxy

--------------------------------------------------------------------------------
-- * Smart constructors

mkE :: [Int] -> E
mkE xs = E (mkPartition xs)

mkE' :: [Int] -> E'
mkE' xs = E' (mkPartition xs)

mkH :: [Int] -> H
mkH xs = H (mkPartition xs)

mkP :: [Int] -> P
mkP xs = P (mkPartition xs)

mkM :: [Int] -> M
mkM xs = M (mkPartition xs)

mkF :: [Int] -> F
mkF xs = F (mkPartition xs)

-- | Note: @mkS@ only accepts valid partitions as input. The reason for this
-- is that while Schur polynomials can be defined for any sequence, they
-- are not necessarily \"standard\" Schur polynomials but can be zero or
-- minus 1 times a \"standard\" one.
mkS :: [Int] -> S
mkS xs = S (toPartition xs)

--------------------------------------------------------------------------------
-- overloaded list instances

{-

-- LAW: @fromList . toList = id@
-- which we satisfy

class IsList l where
  type Item l
  fromList  :: [Item l] -> l
  toList    :: l -> [Item l]     

  fromListN :: Int -> [Item l] -> l
  fromListN _ = fromList  
-}

instance IsList Partition where
  type Item Partition = Int
  fromList = mkPartition
  toList   = fromPartition

instance IsList E where
  type Item E = Int
  fromList = mkE 
  toList (E p) = fromPartition p

instance IsList E' where
  type Item E' = Int
  fromList = mkE' 
  toList (E' p) = fromPartition p

instance IsList H where
  type Item H = Int
  fromList = mkH
  toList (H p) = fromPartition p

instance IsList P where
  type Item P = Int
  fromList = mkP
  toList (P p) = fromPartition p

instance IsList M where
  type Item M = Int
  fromList = mkM
  toList (M p) = fromPartition p

instance IsList F where
  type Item F = Int
  fromList = mkF
  toList (F p) = fromPartition p

instance IsList S where
  type Item S = Int
  fromList = mkS
  toList (S p) = fromPartition p       -- because reordering changes the sign !!!

--------------------------------------------------------------------------------
-- monoid instances

-- Semigroup became a superclass of Monoid
#if MIN_VERSION_base(4,11,0)        

instance Semigroup E where
  (<>) (E xs) (E ys) = E $ mkPartition (fromPartition xs ++ fromPartition ys)

instance Semigroup E' where
  (<>) (E' xs) (E' ys) 
    = E' 
    $ dualPartition 
    $ mkPartition  
    $ fromPartition (dualPartition xs) ++ fromPartition (dualPartition ys)

instance Semigroup H where
  (<>) (H xs) (H ys) = H $ mkPartition (fromPartition xs ++ fromPartition ys)

instance Semigroup P where
  (<>) (P xs) (P ys) = P $ mkPartition (fromPartition xs ++ fromPartition ys)

instance KnownNat n => Semigroup (X n) where
  (<>) (X es) (X fs) = X $ zipWith (+) es fs

--------

instance Monoid E where
  mempty = E $ Partition []

instance Monoid E' where
  mempty = E' $ Partition []

instance Monoid H where
  mempty = H $ Partition []

instance Monoid P where
  mempty = P $ Partition []

instance KnownNat n => Monoid (X n) where
  mempty = xx where 
    xx = X (replicate n 0)
    n  = nOfX xx

#else

instance Monoid E where
  mempty = E $ Partition []
  mappend (E xs) (E ys) = E $ mkPartition (fromPartition xs ++ fromPartition ys)

instance Monoid E' where
  mempty = E' $ Partition []
  mappend (E' xs) (E' ys) 
    = E' 
    $ dualPartition 
    $ mkPartition  
    $ fromPartition (dualPartition xs) ++ fromPartition (dualPartition ys)

instance Monoid H where
  mempty = H $ Partition []
  mappend (H xs) (H ys) = H $ mkPartition (fromPartition xs ++ fromPartition ys)

instance Monoid P where
  mempty = P $ Partition []
  mappend (P xs) (P ys) = P $ mkPartition (fromPartition xs ++ fromPartition ys)

instance KnownNat n => Monoid (X n) where
  mempty = xx where 
    xx = X (replicate n 0)
    n  = nOfX xx
  mappend (X es) (X fs) = X $ zipWith (+) es fs

#endif

--------------------------------------------------------------------------------
-- pretty instances

instance Pretty E  where pretty (E  p) = "e"  ++ show (fromPartition p)
instance Pretty E' where pretty (E' p) = "e'" ++ show (fromPartition p)
instance Pretty H  where pretty (H  p) = "h"  ++ show (fromPartition p)
instance Pretty P  where pretty (P  p) = "p"  ++ show (fromPartition p)
instance Pretty M  where pretty (M  p) = "m"  ++ show (fromPartition p)
instance Pretty F  where pretty (F  p) = "f"  ++ show (fromPartition p)
instance Pretty S  where pretty (S  p) = "s"  ++ show (fromPartition p)

instance Pretty (X n) where 
  pretty (X es) = 
    case [ showXPow i e | (i,e) <- zip [1..] es , e /= 0 ] of 
      [] -> "(1)"
      xs -> intercalate "*" xs
    where
      showXPow !i !e = case e of
        0 -> "1"
        1 -> "x" ++ show i
        _ -> "x" ++ show i ++ "^" ++ show e

--------------------------------------------------------------------------------
