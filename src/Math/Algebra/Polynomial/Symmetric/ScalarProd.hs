
-- | The standard scalar product on the ring of symmetric functions

{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
module Math.Algebra.Polynomial.Symmetric.ScalarProd where

--------------------------------------------------------------------------------

import Data.List
import Math.Combinat.Numbers
import Math.Combinat.Sign
import Math.Combinat.Partitions.Integer

import Math.Algebra.Polynomial.Symmetric.Types

import Math.Algebra.Polynomial.FreeModule ( ZMod , QMod , FreeMod )
import qualified Math.Algebra.Polynomial.FreeModule as ZMod

--------------------------------------------------------------------------------
-- * The functions @z[lambda]@ and @epsilon[lambda]@

-- | The normalization factor @z[lambda]@ appearing in the standard scalar product
--
-- > < h[lambda] , m[mu] > = 1 / (z[lambda]) * < p[lambda] , p[mu] > = < s[lambda] , s[mu] > = delta(lambda,mu)
--
-- Note: the name @zee@ comes from Stembridge's SF package (my alternative would be @zz@, which is not an improvement).
zee :: Partition -> Integer
zee lambda = product [ factorial e * (fromIntegral i)^e | (i,e) <- toExponentialForm lambda ] 

-- | The sign factor
--
-- > epsilon = (-1) ^ ( |lambda| - len(lambda) )
--
epsilon :: Partition -> Integer
epsilon lambda = if odd k then -1 else 1 where
  k = partitionWeight lambda - partitionWidth lambda

epsilonSign :: Partition -> Sign
epsilonSign lambda = paritySign (partitionWeight lambda - partitionWidth lambda)

--------------------------------------------------------------------------------
-- * The scalar product

-- | The standard scalar product on the ring of symmetric functions.
--
-- Some properties:
--
-- > < s[lambda] , s[mu] > = delta(lambda,mu)
-- > < p[lambda] , p[mu] > = delta(lambda,mu) * z[lambda]
-- > < h[lambda] , m[mu] > = delta(lambda,mu)
-- > < e[lambda] , f[mu] > = delta(lambda,mu)
--
class ScalarProd a b where
  scalarProd  :: (Eq c, Num c) => FreeMod c a -> FreeMod c b -> c

--------------------------------------------------------------------------------

instance ScalarProd S S where
  scalarProd left right = if ZMod.size left <= ZMod.size right 
    then foldl' (+) 0 [ ZMod.coeffOf p left * ZMod.coeffOf p right | p <- ZMod.supportList left  ]
    else foldl' (+) 0 [ ZMod.coeffOf p left * ZMod.coeffOf p right | p <- ZMod.supportList right ]

instance ScalarProd P P where
  scalarProd left right = if ZMod.size left <= ZMod.size right 
    then foldl' (+) 0 [ fromInteger (zee q) * ZMod.coeffOf p left * ZMod.coeffOf p right | p@(P q) <- ZMod.supportList left  ]
    else foldl' (+) 0 [ fromInteger (zee q) * ZMod.coeffOf p left * ZMod.coeffOf p right | p@(P q) <- ZMod.supportList right ]

instance ScalarProd H M where
  scalarProd left right = if ZMod.size left <= ZMod.size right 
    then foldl' (+) 0 [ ZMod.coeffOf (H p) left * ZMod.coeffOf (M p) right | H p <- ZMod.supportList left  ]
    else foldl' (+) 0 [ ZMod.coeffOf (H p) left * ZMod.coeffOf (M p) right | M p <- ZMod.supportList right ]

instance ScalarProd E F where
  scalarProd left right = if ZMod.size left <= ZMod.size right 
    then foldl' (+) 0 [ ZMod.coeffOf (E p) left * ZMod.coeffOf (F p) right | E p <- ZMod.supportList left  ]
    else foldl' (+) 0 [ ZMod.coeffOf (E p) left * ZMod.coeffOf (F p) right | F p <- ZMod.supportList right ]

instance ScalarProd M H where scalarProd left right = scalarProd right left
instance ScalarProd F E where scalarProd left right = scalarProd right left
  
--------------------------------------------------------------------------------


