{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Lenses for vector viewing functions
module VectorsLens where

import Prelude hiding (splitAt, (++), zipWith, take, drop )

import Control.Lens
import Control.Monad.ST

import Data.Constraint

import Data.STRef


import Naturals
import VectorsBase
import TensorsBase
import SingBase
import Unsafe.Coerce (unsafeCoerce)


-- | Extract the segment from @n@ until @n + m@ from @v@
segment :: forall k n m a. Nat n -> Nat m -> Vec (n + m + k) a -> Vec m a
segment n m v = take @k m . drop @n n $ v \\ plusAssoc n m k' where
    e :: (n + m + k) - (n + m) :~: k
    e = addCancel (n +| m)
    k' :: Nat k
    k' = size v -| (n +| m) \\ e

-- | Embed a vector in the segment from @n@ until @n + m@
putSegment :: forall k n m a. Nat n -> Nat m -> Vec (n + m + k) a -> Vec m a -> Vec (n + m + k) a
putSegment n m v w = v1 ++ w ++ v3 where
    (v1, w1) = splitAt @(m + k) @n @a n (v \\ plusAssoc n m k')
    (_, v3) = splitAt @k @m @a m w1
    e :: (n + m + k) - (n + m) :~: k
    e = addCancel (n +| m)
    k' :: Nat k
    k' = size v -| (n +| m) \\ e

-- | Take each @m@th element of @v@
subseq :: forall n m a. m !~ 'Z => Nat n -> Nat m -> Vec (n :* m) a -> Vec n a
subseq n m = subseq' n m neq

subseq' :: forall n m a. Nat n -> Nat m -> Neq m 'Z -> Vec (n :* m) a -> Vec n a
subseq' _ NZ p _                 = exFalso (p Refl)
subseq' n m p VN                 = VN \\ rightOrCancel p (factorZ n m Refl)
subseq' (NS n) (NS m) p (VC a v) = VC a $ subseq' n (NS m) p (drop m v)

-- | Embed a vector in the subsequence spanned by the multiples of @m@
putSubseq :: forall n m a. m !~ 'Z => Nat n -> Nat m -> Vec (n :* m) a -> Vec n a -> Vec (n :* m) a
putSubseq n m = putSubseq' n m neq

putSubseq' :: forall n m a. Nat n -> Nat m -> Neq m 'Z -> Vec (n :* m) a -> Vec n a -> Vec (n :* m) a
putSubseq' _ _ _ VN _ = VN
putSubseq' _ NZ p (VC _ _) (VC _ _) = exFalso (p Refl)
putSubseq' (NS (n :: Nat n')) (NS m) p (VC _ v) (VC b w) = VC b (take @(n' :* m) m v) ++ putSubseq' n (NS m) p (drop m v) w

-- | Slice @v@, returning @k@ elements @m@ steps apart after @n@. 
slice :: forall n m k l a. (k !~ 'Z) => Nat n -> Nat m -> Nat k -> Nat l -> Vec (n + (m :* k) + l) a -> Vec m a
slice n m k l v = subseq m k $ segment @l n (m *| k) v \\ know l

-- | Embed a vector in a slice
putSlice :: forall n m k l a. k !~ 'Z => Nat n -> Nat m -> Nat k -> Nat l -> Vec (n + (m :* k) + l) a -> Vec m a -> Vec (n + (m :* k) + l) a
putSlice n m k l v w = putSegment @l n (m *| k) v seg' \\ know l where
    seg' = putSubseq m k seg w
    seg = segment @l n (m *| k) v \\ know l -- putSlice is only ever going to look nice if we resort to type division


-- let us forgo the numpy sentiment of absurd slices
-- and write a[start:stop]
-- a[start:steps:step]

-- | Boolean mask extraction
mask :: Vec (Length bs) a -> SList bs -> Vec (Count bs) a
mask VN XNil = VN
mask (VC a v) (XCons BT bv) = VC a (mask v bv)
mask (VC _ v) (XCons BF bv) = mask v bv

-- | Embed a vector in a masked region
putMask :: Vec (Length bs) a -> SList bs -> Vec (Count bs) a -> Vec (Length bs) a
putMask VN XNil VN = VN
putMask (VC _ v) (XCons BT bs) (VC y w) = VC y $ putMask v bs w
putMask (VC x v) (XCons BF bs) w        = VC x $ putMask v bs w

-- | Multi-indexing; given a vector of indices, return a vector of the indexed values
multiGet :: Vec n a -> Vec m (Fin n) -> Vec m a
multiGet v fs = get v <$> fs

-- | Multi-index assignment; given a vector of indices and a vector of values, update a vector at all indices with the provided values. Later values overwrite earlier values.
multiPut :: Vec n a -> Vec m (Fin n) -> Vec m a -> Vec n a
multiPut v VN VN = v
multiPut v (VC f fs) (VC x w) = multiPut (put v f x) fs w

-- | Analog of 'Control.Lens.At.at' for @Vec n a@
vAt :: Fin n -> Lens' (Vec n a) a
vAt f = lens (`get` f) (`put` f)

-- | Given a set of indices, return a lens pointing to the elements under the multi-index
vMulti :: Vec m (Fin n) -> Lens' (Vec n a) (Vec m a)
vMulti fs = lens (`multiGet` fs) (`multiPut` fs)

-- | Given a mask @bs@, @vMask bs@ is a lens pointing to the the region masked by @bs@.
vMask :: SList bs -> Lens' (Vec (Length bs) a) (Vec (Count bs) a)
vMask bs = lens (`mask` bs) (`putMask` bs)

-- | A lens pointing to the segment from @n@ to @n + m@.
vSeg :: forall n m k a. Nat n -> Nat m -> Lens' (Vec (n + m + k) a) (Vec m a)
vSeg n m = lens (segment @k n m) (putSegment @k n m)

-- | Given slicing information, return a lens pointing to the specified slice.
vSlice ::  forall n m k l a. k !~ 'Z => Nat n -> Nat m -> Nat k -> Nat l -> Lens' (Vec (n + (m :* k) + l) a) (Vec m a)
vSlice n m k l = lens g' p' where
    g' :: Vec ((n + (m :* k)) + l) a -> Vec m a
    g' = slice n m k l
    p' :: Vec ((n + (m :* k)) + l) a -> Vec m a -> Vec ((n + (m :* k)) + l) a
    p' = putSlice n m k l

-- | Variant of @Control.Lens.Operators.(.=)@ for @ST@.
(.:=) :: ASetter' t a -> a -> STRef s t -> ST s ()
(.:=) s a r = modifySTRef r (s .~ a)

-- | A lens viewing a tensor with two dimensions transposed.
vTranspose :: (KnownNatList ix, KnownNatList iy, Swapped' ix i j iy) => Nat i -> Nat j -> Lens' (Tensor iy a) (Tensor ix a)
vTranspose i j = lens (transpose i j) (const $ transpose' i j)
