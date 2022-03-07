{-# LANGUAGE DataKinds, TypeFamilies, GADTs, ScopedTypeVariables, FlexibleInstances, TypeOperators, FlexibleContexts, TypeApplications, AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | This module defines a fixed-size vector datatype,
-- and includes the instances and tools to allow for user-friendly manipulation.
module Vectors where

import Control.Applicative ( liftA2 )
import Control.Comonad ( Comonad(extract, duplicate) )

import Data.Constraint ( (\\), Dict(..) )
import Data.Constraint.Deferrable
import Data.Functor.Rep ( distributeRep, Representable(..) )
import Data.Distributive ( Distributive(distribute) )
import Data.List ( intercalate )
import Control.Lens

import Prelude hiding ((++), zipWith, take, drop )
import qualified Prelude as P

import qualified Data.Map as M

import Naturals
import Data.Kind (Type)
import Control.Monad.ST
import Data.STRef



-- | The type for vectors with known size
data Vec n a where
    VN :: Vec 'Z a
    VC ::  a -> Vec n a -> Vec ('S n) a

-- | The list of natural numbers type
data L = Nil | Cons N L
-- restricted to N for now
-- refer to SingKind for generalized stuff.

-- | The vector of booleans type
data BV = BNil | BCons B BV

-- | The singleton type for vectors of booleans
data BVec n xs where
    BN :: BVec 'Z 'BNil
    BC :: Boolean b -> BVec n xs -> BVec ('S n) ('BCons b xs)

toVec :: BVec n xs -> Vec n B
toVec BN = VN
toVec (BC b bv) = VC (toB b) (toVec bv)

-- | The singleton type for lists of natural numbers
data List xs where
    LN :: List 'Nil
    LC :: Nat n -> List xs -> List ('Cons n xs)

data HL a = HNil | HCons a (HL a)

type family Length (xs :: HL k) :: N where
    Length 'HNil         = 'Z
    Length ('HCons _ xs) = 'S (Length xs)

data HList (xs :: HL k) where
    HN :: HList 'HNil
    HC :: a -> HList xs -> HList ('HCons a xs)


-- | The type for tensors with known dimensions
data Tensor ix a where
    TV :: Vec n a -> Tensor ('Cons n 'Nil) a
    TC :: Vec n (Tensor ix a) -> Tensor ('Cons n ix) a

-- a block tensor is described by a list of lists of dimensions
-- so we have 2 levels of stacking operations
data Block ix a where
    BLV :: Vec n a -> Block ('HCons ('HCons n 'HNil) 'HNil) a   -- a vector is a "column block"
    BLC :: Vec n (Block ix a) -> Block ('HCons iy ix) a -> Block ('HCons ('HCons n iy) ix) a -- n blocks + a chain of vectors of blocks (of the same shape) -> longer chain of blocks
    BLS :: Vec n (Block ix a) -> Block ('HCons ('HCons n 'HNil) ix) a -- n blocks -> block of higher dimension

-- | The list product type family
type family Prod (ns :: L) :: N where
    Prod 'Nil         = 'S 'Z
    Prod ('Cons n ns) = n :* Prod ns

concatenate :: Vec n (Vec m a) -> Vec (n :* m) a
concatenate VN = VN
concatenate (VC v vs) = v ++ concatenate vs

type Sparse (ix :: HL N) a = M.Map (HList ix) a

type family Elem (x :: k) (xs :: HL k) :: B where
    Elem x 'HNil        = 'F
    Elem x ('HCons x _) = 'T
    Elem x ('HCons y v) = Elem x v

type family Sing :: k -> Type

data SomeSing k where
    SomeSing :: Sing (a :: k) -> SomeSing k

class SingKind k where
    type Demote k = (r :: Type) | r -> k

    fromSing :: Sing (a :: k) -> Demote k
    toSing :: Demote k -> SomeSing k

{-
getL :: HList (xs :: HL k) -> Fin (Length xs) -> Demote k
getL (HC x _) FZ = x
getL xs (FS fin) = _wd
-}



vAt :: Fin n -> Lens' (Vec n a) a
vAt f = lens (`get` f) (`put` f)

type N0 = 'Z
type N1 = 'S N0
type N2 = 'S N1
type N3 = 'S N2
type N4 = 'S N3
type N5 = 'S N4
type N6 = 'S N5
type N7 = 'S N6
type N8 = 'S N7
type N9 = 'S N8

(.:=) :: ASetter' t a -> a -> STRef s t -> ST s ()
(.:=) s a r = modifySTRef r (s .~ a)

test :: Vec N4 Int
test = runST $ do
    v <- newSTRef $ full (1 :: Int) (nat :: Nat N4)
    
    let w = full (3 :: Int) (nat :: Nat N2)
    let m = BC BF $ BC BT $ BC BF $ BC BT BN

    v & vAt FZ  .:= 2
    v & vMask m .:= w

    readSTRef v

vMask :: BVec n bs -> Lens' (Vec n a) (Vec (Count bs) a)
vMask bs = lens (`mask` bs) (`putMask` bs)

{-
vSlice ::  forall n m k l a. Nat n -> Nat m -> Nat k -> Nat l -> 'Z <? k -> Lens' (Vec (n + (m :* k) + l) a) (Vec m a)
vSlice n m k l p = lens g' p' where
    g' :: Vec ((n + (m :* k)) + l) a -> Vec m a
    g' = slice n m k l p
    p' = _
-}

flatten :: Tensor ix a -> Vec (Prod ix) a
flatten (TV v) = v \\ mulRightId (size v)
flatten (TC vs) = concatenate $ fmap flatten vs

toShape :: Vec (Prod ix) a -> List ix -> Neg (ix :~: 'Nil) -> Tensor ix a
toShape VN (LC n LN) c          = undefined -- TV VN
toShape VN (LC n (LC nat li)) c = undefined -- _wy
toShape (VC a vec) ns c         = undefined -- _wt

reshape :: Tensor ix a -> List ix' -> Neg (ix' :~: 'Nil) -> Prod ix :~: Prod ix' -> Tensor ix' a
reshape t ns c pf = toShape (flatten t \\ pf) ns c

-- | The boolean counting type family
type family Count (bs :: BV) :: N where
    Count 'BNil = 'Z
    Count ('BCons 'T bs) = 'S (Count bs)
    Count ('BCons 'F bs) = Count bs



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

-- | Extract the segment from @n@ until @n + m@ from @v@
segment :: forall n m k a. KnownNat k => Nat n -> Nat m -> Vec (n + m + k) a -> Vec m a
segment n m = take @k m . drop @n n \\ plusAssoc n m (nat @k)

-- | Take each @m@th element of @v@
subseq :: Nat n -> Nat m -> 'Z <? m -> Vec (n :* m) a -> Vec n a
subseq n m p VN                 = VN \\ rightOrCancel (ltNeq NZ m p) (factorZ n m Refl)
subseq (NS n) (NS m) p (VC a v) = VC a $ subseq n (NS m) p (drop m v)

-- | Split vector into @n@ pieces
split :: forall n m a. Nat n -> Nat m -> Vec (n :* m) a -> Vec n (Vec m a)
split NZ _ _     = VN
split n NZ _     = full VN n
split (NS (n :: Nat k)) m v = VC (take @(k :* m) m v) (split n m $ drop m v)

-- | Boolean mask extraction
mask :: Vec n a -> BVec n bs -> Vec (Count bs) a
mask VN BN = VN
mask (VC a v) (BC BT bv) = VC a (mask v bv)
mask (VC _ v) (BC BF bv) = mask v bv

put :: Vec n a -> Fin n -> a -> Vec n a
put VN       _      _ = VN
put (VC _ v) FZ     y = VC y v
put (VC x v) (FS f) y = VC x (put v f y)

putMask :: Vec n a -> BVec n bs -> Vec (Count bs) a -> Vec n a
putMask VN BN VN = VN
putMask (VC _ v) (BC BT bs) (VC y w) = VC y $ putMask v bs w
putMask (VC x v) (BC BF bs) w        = VC x $ putMask v bs w

-- | Slice @v@, returning @k@ elements @m@ steps apart after @n@. 
slice :: forall n m k l a. Nat n -> Nat m -> Nat k -> Nat l -> 'Z <? k -> Vec (n + (m :* k) + l) a -> Vec m a
slice n m k l p v = subseq m k p $ segment @n @(m :* k) @l n (m *| k) v \\ know l

{-
putSlice :: forall n m k l a. Nat n -> Nat m -> Nat k -> Nat l -> 'Z <? k -> Vec m a -> Vec (n + (m :* k) + l) a -> Vec m a
putSlice n m k l p v w = _ --subseq m k p $ segment @n @(m :* k) @l n (m *| k) v \\ know l
-}

-- let us forgo the numpy sentiment of absurd slices
-- and write a[start:stop]
-- a[start:steps:step]

-- | @take n v@ returns a prefix of size @n@ from @v@
take :: forall m n a. Nat n -> Vec (n + m) a -> Vec n a
take NZ     _                   = VN
take (NS (n :: Nat k)) (VC a v) = VC a $ take @m n v -- we need to use take @m here to disambiguate m, since it is ambiguous because GHC does not recognize injectivity of n + m over m

-- | @drop n v@ returns the suffix after @n@ elements of @v@
drop :: forall n m a. Nat n -> Vec (n + m) a -> Vec m a
drop NZ v = v
drop (NS k) (VC _ v) = drop k v

splitAt :: forall m n a. Nat n -> Vec (n + m) a -> (Vec n a, Vec m a)
splitAt n v = (take @m n v, drop n v)

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

