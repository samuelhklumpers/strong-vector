{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PartialTypeSignatures #-}

-- | This module defines a fixed-size vector datatype,
-- and includes the instances and tools to allow for user-friendly manipulation.
module Vectors where

import Prelude hiding (splitAt, (++), zipWith, take, drop )
import Data.List hiding (splitAt, (++), (\\), zipWith, take, drop, delete )
import qualified Prelude as P hiding (splitAt)

import Control.Applicative
import Control.Comonad
import Control.Lens
import Control.Monad.ST

import Data.Constraint
import Data.Distributive
import Data.Functor.Rep
import Data.STRef


import Naturals


-- | The type for vectors with known size
data Vec n a where
    VN :: Vec 'Z a
    VC ::  a -> Vec n a -> Vec ('S n) a

-- | The list of natural numbers type
data L = Nil | Cons N L
-- restricted to N for now
-- refer to SingKind for generalized stuff.

-- | The vector of booleans type
data BV = BNil | BCons Bool BV

-- | The singleton type for vectors of booleans
data BVec n xs where
    BN :: BVec 'Z 'BNil
    BC :: Boolean b -> BVec n xs -> BVec ('S n) ('BCons b xs)

-- | The singleton type for lists of natural numbers
data List xs where
    LN :: List 'Nil
    LC :: Nat n -> List xs -> List ('Cons n xs)

-- | The list length type family
type family Length (xs :: [k]) :: N where
    Length '[]       = 'Z
    Length (_ ': xs) = 'S (Length xs)


-- | The singleton type for heterogeneous type-level lists of kind @k@
data HList (xs :: [*]) where
    HN :: HList '[]
    HC :: a -> HList xs -> HList (a ': xs)

instance Eq (HList '[]) where
    HN == HN = True

deriving instance (Eq a, Eq (HList xs)) => Eq (HList (a ': xs))

instance Show (HList '[]) where
    show HN = "HN"

deriving instance (Show a, Show (HList xs)) => Show (HList (a ': xs))


-- | The type for tensors with known dimensions
data Tensor ix a where
    TV :: Vec n a -> Tensor ('Cons n 'Nil) a
    TC :: Vec n (Tensor ix a) -> Tensor ('Cons n ix) a


-- | The list product type family
type family Prod (ns :: L) :: N where
    Prod 'Nil         = 'S 'Z
    Prod ('Cons n ns) = n :* Prod ns

-- | The element containment type family for lists
type family Elem (x :: k) (xs :: [k]) :: Bool where
    Elem x '[]        = 'False
    Elem x (x ': _) = 'True
    Elem x (y ': v) = Elem x v


{-
-- a block tensor is described by a list of lists of dimensions
-- so we have 2 levels of stacking operations
data Block ix a where
    BLV :: Vec n a -> Block (': (': n '[]) '[]) a   -- a vector is a "column block"
    BLC :: Vec n (Block ix a) -> Block (': iy ix) a -> Block (': (': n iy) ix) a -- n blocks + a chain of vectors of blocks (of the same shape) -> longer chain of blocks
    BLS :: Vec n (Block ix a) -> Block (': (': n '[]) ix) a -- n blocks -> block of higher dimension

type Sparse (ix :: HL N) a = M.Map (HList ix) a

type family Sing :: k -> Type

data SomeSing k where
    SomeSing :: Sing (a :: k) -> SomeSing k

class SingKind k where
    type Demote k = (r :: Type) | r -> k

    fromSing :: Sing (a :: k) -> Demote k
    toSing :: Demote k -> SomeSing k

getL :: HList (xs :: HL k) -> Fin (Length xs) -> Demote k
getL (HC x _) FZ = x
getL xs (FS fin) = _wd
-}


-- | The boolean counting type family
type family Count (bs :: BV) :: N where
    Count 'BNil = 'Z
    Count ('BCons 'True bs) = 'S (Count bs)
    Count ('BCons 'False bs) = Count bs

instance Show (BVec n xs) where
    show v = "{" P.++ intercalate "," (map show $ toList $ toVec v) P.++ "}"

instance Show a => Show (Vec n a) where
    show v = "<" P.++ intercalate "," (map show $ toList v) P.++ ">"

instance Eq a => Eq (Vec n a) where
    VN     == VN     = True
    VC x v == VC y w = x == y && v == w

instance Functor (Vec n) where
    fmap _ VN       = VN
    fmap f (VC x v) = VC (f x) (fmap f v)

-- | Note that this instance is forced to use @full@ for @pure@,
-- unlike unsized vectors of lists which use the singleton @pure x = [x]@.
instance KnownNat n => Applicative (Vec n) where
    pure x = full x nat

    liftA2 = zipWith

instance KnownNat n => Monad (Vec n) where
    return = pure

    v >>= f = diag . fmap f $ v

instance Foldable (Vec n) where
  foldMap _ VN = mempty
  foldMap f (VC x v) = f x <> foldMap f v

instance KnownNat n => Traversable (Vec n) where
  sequenceA VN       = pure VN
  sequenceA (VC x v) = VC <$> x <*> (sequenceA v \\ lower (Dict @(KnownNat n)))

-- | Note that only non-empty vectors are comonads due to @extract@
instance Comonad (Vec ('S n)) where
    extract (VC x _) = x
    duplicate = square

instance KnownNat n => Distributive (Vec n) where
    distribute = distributeRep
    -- this gives us nice(r) transposes I think
    -- or at least we can now transpose through [] or so

-- | A vector of size @n@ with elements of type @a@ is isomorphic to a function from a type with @n@ values into @a@.
instance KnownNat n => Representable (Vec n) where
    type Rep (Vec n) = Fin n

    tabulate = generate
    index = get

instance (KnownNat n, Num a) => Num (Vec n a) where
    (+) = liftA2 (+) -- this is numpy
    (*) = liftA2 (*)

    abs = fmap abs
    signum = fmap signum
    negate = fmap negate

    fromInteger = pure . fromInteger

-- | Safely index a vector with an appropriate index
get :: Vec n a -> Fin n -> a
get (VC a _) FZ     = a
get (VC _ v) (FS f) = get v f

-- | Update the element at the given index
put :: Vec n a -> Fin n -> a -> Vec n a
put VN       _      _ = VN
put (VC _ v) FZ     y = VC y v
put (VC x v) (FS f) y = VC x (put v f y)

-- | @take n v@ returns a prefix of size @n@ from @v@
take :: forall m n a. Nat n -> Vec (n + m) a -> Vec n a
take NZ     _                   = VN
take (NS (n :: Nat k)) (VC a v) = VC a $ take @m n v -- we need to use take @m here to disambiguate m, since it is ambiguous because GHC does not recognize injectivity of n + m over m

-- | @drop n v@ returns the suffix after @n@ elements of @v@
drop :: forall n m a. Nat n -> Vec (n + m) a -> Vec m a
drop NZ v = v
drop (NS k) (VC _ v) = drop k v

-- | @splitAt n v@ returns a tuple where the first element is a prefix of length @n@ of @v@, and the second element is the remainder of @v@.
splitAt :: forall m n a. Nat n -> Vec (n + m) a -> (Vec n a, Vec m a)
splitAt n v = (take @m n v, drop n v)

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

-- | Given slicing information, return a lens pointing to the specified slice.
vSlice ::  forall n m k l a. k !~ 'Z => Nat n -> Nat m -> Nat k -> Nat l -> Lens' (Vec (n + (m :* k) + l) a) (Vec m a)
vSlice n m k l = lens g' p' where
    g' :: Vec ((n + (m :* k)) + l) a -> Vec m a
    g' = slice n m k l
    p' :: Vec ((n + (m :* k)) + l) a -> Vec m a -> Vec ((n + (m :* k)) + l) a
    p' = putSlice n m k l

-- | Boolean mask extraction
mask :: Vec n a -> BVec n bs -> Vec (Count bs) a
mask VN BN = VN
mask (VC a v) (BC BT bv) = VC a (mask v bv)
mask (VC _ v) (BC BF bv) = mask v bv

-- | Embed a vector in a masked region
putMask :: Vec n a -> BVec n bs -> Vec (Count bs) a -> Vec n a
putMask VN BN VN = VN
putMask (VC _ v) (BC BT bs) (VC y w) = VC y $ putMask v bs w
putMask (VC x v) (BC BF bs) w        = VC x $ putMask v bs w

-- | Multi-indexing; given a vector of indices, return a vector of the indexed values
multiGet :: Vec n a -> Vec m (Fin n) -> Vec m a
multiGet v fs = get v <$> fs

-- | Multi-index assignment; given a vector of indices and a vector of values, update a vector at all indices with the provided values. Later values overwrite earlier values.
multiPut :: Vec n a -> Vec m (Fin n) -> Vec m a -> Vec n a
multiPut v VN VN = v
multiPut v (VC f fs) (VC x w) = multiPut (put v f x) fs w

-- | Given a set of indices, return a lens pointing to the elements under the multi-index
vMulti :: Vec m (Fin n) -> Lens' (Vec n a) (Vec m a)
vMulti fs = lens (`multiGet` fs) (`multiPut` fs)

-- | Split vector into @n@ pieces
split :: forall n m a. Nat n -> Nat m -> Vec (n :* m) a -> Vec n (Vec m a)
split NZ _ _     = VN
split n NZ _     = full VN n
split (NS (n :: Nat k)) m v = VC (take @(k :* m) m v) (split n m $ drop m v)

-- | Convert a type-level boolean vector to a vector of @Bool@
toVec :: BVec n xs -> Vec n Bool
toVec BN = VN
toVec (BC b bv) = VC (toB b) (toVec bv)


-- let us forgo the numpy sentiment of absurd slices
-- and write a[start:stop]
-- a[start:steps:step]

-- | Analog of 'Control.Lens.At.at' for @Vec n a@
vAt :: Fin n -> Lens' (Vec n a) a
vAt f = lens (`get` f) (`put` f)

-- | Given a mask @bs@, @vMask bs@ is a lens pointing to the the region masked by @bs@.
vMask :: BVec n bs -> Lens' (Vec n a) (Vec (Count bs) a)
vMask bs = lens (`mask` bs) (`putMask` bs)

-- | A lens pointing to the segment from @n@ to @n + m@.
vSeg :: forall n m k a. Nat n -> Nat m -> Lens' (Vec (n + m + k) a) (Vec m a)
vSeg n m = lens (segment @k n m) (putSegment @k n m)

{-
vSub :: Nat m -> Lens' (Vec (n :* m) a) (Vec n a)
vSub m = lens (subseq _ m) _
-}

-- | Variant of @Control.Lens.Operators.(.=)@ for @ST@.
(.:=) :: ASetter' t a -> a -> STRef s t -> ST s ()
(.:=) s a r = modifySTRef r (s .~ a)

-- | Flatten a vector of vectors
concatenate :: Vec n (Vec m a) -> Vec (n :* m) a
concatenate VN = VN
concatenate (VC v vs) = v ++ concatenate vs

{-
-- | Flatten a tensor into a vector.
flatten :: Tensor ix a -> Vec (Prod ix) a
flatten (TV v) = v \\ mulRightId (size v)
flatten (TC vs) = concatenate $ fmap flatten vs
-}

{-
toShape :: Vec (Prod ix) a -> List ix -> Neg (ix :~: 'Nil) -> Tensor ix a
toShape VN (LC n LN) c          = undefined -- TV VN
toShape VN (LC n (LC nat li)) c = undefined -- _wy
toShape (VC a vec) ns c         = undefined -- _wt

reshape :: Tensor ix a -> List ix' -> Neg (ix' :~: 'Nil) -> Prod ix :~: Prod ix' -> Tensor ix' a
reshape t ns c pf = toShape (flatten t \\ pf) ns c
-}

-- | Generate a vector by applying a function to a range of indices
generateN :: Nat n -> (Fin n -> a) -> Vec n a
generateN NZ _     = VN
generateN (NS n) f = VC (f FZ) (generateN n (f . finS \\ know n))

-- | Generate a vector by applying a function to a range of indices, inferring the size from the type
generate :: KnownNat n => (Fin n -> a) -> Vec n a
generate = generateN nat

-- | Build a vector by repeatedly applying a function to a seed
unfoldN :: Nat n -> (s -> (a, s)) -> s -> Vec n a
unfoldN NZ _ _ = VN
unfoldN (NS n) f z = VC a (unfoldN n f s) where
    (a, s) = f z

-- | Build a vector by repeatedly applying a function to a seed, inferring the size from the type
unfold :: KnownNat n => (s -> (a, s)) -> s -> Vec n a
unfold = unfoldN nat

-- | @iterateN n f x@ returns a vector of size @n@ of repeated applications of @f@ to @x@
iterateN :: Nat n -> (a -> a) -> a -> Vec n a
iterateN NZ     _ _ = VN
iterateN (NS n) f z = VC z (iterateN n f (f z))

-- | @iterate f x@ returns a vector of repeated applications of @f@ to @x@, inferring the size from the type
iterate :: KnownNat n => (a -> a) -> a -> Vec n a
iterate = iterateN nat

-- | @linspace x y n@ returns a vector of @n@ points uniformly spaced in the interval @[x, y)@.
linspace :: Fractional a => a -> a -> Nat n -> Vec n a
linspace x y n = iterateN n step x where
    step z = z + (y - x) / fromIntegral (toInt n)

-- | Safely return the first element of a non-empty vector
head :: Vec ('S n) a -> a
head (VC a _) = a

-- | Safely return the tail of a non-empty vector
tail :: Vec ('S n) a -> Vec n a
tail (VC _ v) = v

-- | Zip two equally long vectors with a binary function
zipWith :: (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
zipWith _ VN       VN = VN
zipWith f (VC a v) (VC b w) = VC (f a b) (zipWith f v w)

-- | Return the diagonal of a square matrix
diag :: Vec n (Vec n a) -> Vec n a
diag v = zipWith get v (enumFin $ size v)

-- | Square a functorial value.
-- For container-like functors, this tends to actually make square containers.
square :: Functor f => f b -> f (f b)
square v = fmap (const v) v

-- | Convert a vector to a list
toList :: Vec n a -> [a]
toList = foldr (:) []

-- | @full x n@ returns a vector of @n@ copies of @x@
full :: a -> Nat n -> Vec n a
full _ NZ     = VN
full a (NS n) = VC a (full a n)

-- | Concatenate two vectors
(++) :: Vec n a -> Vec m a -> Vec (n + m) a
VN     ++ w = w
VC x v ++ w = VC x (v ++ w)

-- | Return the number of elements of a vector
size :: Vec n a -> Nat n
size VN = NZ
size (VC _ v) = NS (size v)

-- | @enumFin n@ returns a vector of size @n@, enumerating from @0@ to @n@ in @Fin n@
enumFin :: Nat n -> Vec n (Fin n)
enumFin NZ          = VN
enumFin (NS NZ)     = VC FZ VN
enumFin (NS (NS n)) = VC (toFZ $ NS n) (fmap FS (enumFin (NS n)))

-- | Tuple the elements of a vector with their indices
enumerate :: Vec n a -> Vec n (Fin n, a)
enumerate v = zipWith (,) (enumFin $ size v) v

-- | @delete n v@ safely returns @v@ with the @n@th element deleted, provided @v@ is non-empty
delete :: Fin ('S n) -> Vec ('S n) a -> Vec n a
delete FZ (VC _ v)    = v
delete (FS f) (VC x v) = VC x $ delete f v

-- | @subMatrix n m x@ returns the submatrix obtained by deleting the @n@th row and @m@th column, provided @x@ is non-empty
subMatrix :: Fin ('S n) -> Fin ('S m) -> Vec ('S n) (Vec ('S m) a) -> Vec n (Vec m a)
subMatrix f g v = delete g <$> delete f v

-- | Return the determinant of a square matrix
det :: forall a n. Num a => Vec n (Vec n a) -> a
det VN               = 0
det (VC (VC x _) VN) = x
det v@(VC _ w)       = sum $ cof <$> enumerate v
    where
    cof (j, VC x _) = sign j * x * minor (toFZ $ size w) j v

    sign :: Fin m -> a
    sign FZ = 1
    sign (FS FZ) = -1
    sign (FS (FS f)) = sign f

-- | Return the minor of a non-empty square matrix
minor :: Num a => Fin ('S n) -> Fin ('S n) -> Vec ('S n) (Vec ('S n) a) -> a
minor i j v = det (subMatrix i j v)

