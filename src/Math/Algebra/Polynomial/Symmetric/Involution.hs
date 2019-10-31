
-- | The involution on the ring of symmetric functions

{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
module Math.Algebra.Polynomial.Symmetric.Involution where

--------------------------------------------------------------------------------

import Data.List
import Math.Combinat.Numbers
import Math.Combinat.Sign
import Math.Combinat.Partitions.Integer

import Math.Algebra.Polynomial.Symmetric.Types
import Math.Algebra.Polynomial.Symmetric.ScalarProd

import Math.Algebra.Polynomial.FreeModule ( ZMod , QMod , FreeMod )
import qualified Math.Algebra.Polynomial.FreeModule as ZMod

--------------------------------------------------------------------------------
-- * The involution

-- | The involution on the ring of symmetric functions, defined by
-- @omega(e[k]) = h[k]@
--
-- Some properties:
--
-- > omega( s[lambda]) = s[lambda']
-- > omega( e[lambda]) = h[lambda]
-- > omega( m[lambda]) = f[lambda]
-- > omega( p[lambda]) = epsilon(lambda) * p[lambda]
--
class Involution a b | a->b , b->a where
  omega :: (Eq c, Num c) => FreeMod c a -> FreeMod c b

--------------------------------------------------------------------------------

-- omega( s[lambda] ) == s[lambda']
instance Involution S S where
  omega = ZMod.unsafeMapBase $ \(S lambda) -> S (dualPartition lambda)

-- omega( p[lambda] ) == +- p[lambda]
instance Involution P P where
  omega = ZMod.mapCoeffWithKey f where 
    f (P part) c = case epsilonSign part of { Plus -> c ; Minus -> negate c }

--------------------------------------------------------------------------------

-- omega( e[lambda] ) == h[lambda]
instance Involution E H where
  omega = ZMod.unsafeMapBase $ \(E lambda) -> (H lambda)

-- e[lambda] == omega( omega( e[lambda] )) == omega( h[lambda] )
instance Involution H E where
  omega = ZMod.unsafeMapBase $ \(H lambda) -> (E lambda)

-- omega( m[lambda] ) == f[lambda]
instance Involution M F where
  omega = ZMod.unsafeMapBase $ \(M lambda) -> (F lambda)

-- m[lambda] == omega( omega( m[lambda] )) == omega( f[lambda] )
instance Involution F M where
  omega = ZMod.unsafeMapBase $ \(F lambda) -> (M lambda)

--------------------------------------------------------------------------------
