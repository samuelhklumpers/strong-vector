{-# LANGUAGE DataKinds, TypeFamilies, GADTs, ScopedTypeVariables, FlexibleInstances, TypeOperators, FlexibleContexts, TypeApplications, AllowAmbiguousTypes #-}

-- | This module defines a fixed-size vector datatype,
-- and includes the instances and tools to allow for user-friendly manipulation.
module Vectors where

import Control.Applicative ( liftA2 )
import Control.Comonad ( Comonad(extract, duplicate) )

import Data.Constraint ( (\\), Dict(..) )
import Data.Functor.Rep ( distributeRep, Representable(..) )
import Data.Distributive ( Distributive(distribute) )
import Data.List ( intercalate )

import Prelude hiding ((++), zipWith, take, drop )
import qualified Prelude as P


import Naturals ( type (+), Fin(..), Nat(..), N(S, Z), KnownNat (nat), lower, toFZ, finS, know, toInt )


-- | The singleton type for vectors
data Vec n a where
    VN :: Vec 'Z a
    VC ::  a -> Vec n a -> Vec ('S n) a

-- | The list of natural numbers type
data L = Nil | Cons N L
-- restricted to N for now
-- refer to SingKind for generalized stuff.

-- | The singleton type for lists of natural numbers
data List xs where
    LN :: List 'Nil
    LC :: Nat n -> List xs -> List ('Cons n xs)

{-
data Tensor ix a where
    TN :: Tensor 'Nil a
    TC :: Vec n (Tensor ix a) -> Tensor ('Cons n ix) a
-}


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

-- | @take n v@ returns a prefix of size @n@ from @v@
take :: forall m n a. Nat n -> Vec (n + m) a -> Vec n a
take NZ     _                   = VN
take (NS (n :: Nat k)) (VC a v) = VC a $ take @m n v -- we need to use take @m here to disambiguate m, since it is ambiguous because GHC does not recognize injectivity of n + m over m

-- | @drop n v@ returns the suffix after @n@ elements of @v@
drop :: forall n m a. Nat n -> Vec (n + m) a -> Vec m a
drop NZ v = v
drop (NS k) (VC _ v) = drop k v

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
toList = foldl (flip (:)) []

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

