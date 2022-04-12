{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}

-- | Vectors, basic operations, and construction/extraction functions.
module VectorsBase where

import Prelude hiding (splitAt, (++), zipWith, take, drop )
import Data.List hiding (splitAt, (++), (\\), zipWith, take, drop, delete )
import qualified Prelude as P hiding (splitAt)

import Control.Applicative
import Control.Comonad


import Data.Constraint
import Data.Distributive
import Data.Functor.Rep


import Naturals
import SingBase
import Data.Proxy (Proxy)
import Data.Void


-- | The type for vectors with known size
data Vec n a where
    VN :: Vec 'Z a
    VC :: a -> Vec n a -> Vec ('S n) a

data XVec :: forall n k. (k ~> *) -> Vec n k -> * where
    XN  :: XVec f 'VN
    XC  :: Apply f x -> XVec f xs -> XVec f ('VC x xs)

type SVec = XVec SingSym
type TVec tc = XVec (TyCon tc)
 
type instance Sing x = SVec x

type family ToVec (xs :: [k]) :: Vec (Length xs) k where
    ToVec '[] = 'VN
    ToVec (x ': xs) = 'VC x (ToVec xs)

type family FromVec (xs :: Vec n k) :: [k] where
    FromVec 'VN        = '[] 
    FromVec ('VC x xs) = x ': FromVec xs

toXVec :: XList f xs -> XVec f (ToVec xs)
toXVec XNil         = XN
toXVec (XCons x xs) = XC x $ toXVec xs

instance Show a => Show (Vec n a) where
    show v = "<" P.++ intercalate "," (map show $ toList v) P.++ ">"

instance Eq a => Eq (Vec n a) where
    VN     == VN     = True
    VC x v == VC y w = x == y && v == w

instance Functor (Vec n) where
    fmap _ VN       = VN
    fmap f (VC x v) = VC (f x) (fmap f v)

-- | Note that this instance is forced to use @full@ for @pure@,
-- unlike unsized vectors or lists which use the singleton @pure x = [x]@.
instance Known n => Applicative (Vec n) where
    pure x = full x auto

    liftA2 = zipWith

instance Known n => Monad (Vec n) where
    return = pure

    v >>= f = diag . fmap f $ v

instance Foldable (Vec n) where
  foldMap _ VN = mempty
  foldMap f (VC x v) = f x <> foldMap f v

instance Known n => Traversable (Vec n) where
  sequenceA VN       = pure VN
  sequenceA (VC x v) = VC <$> x <*> (sequenceA v \\ lower (Dict @(Known n)))

-- | Note that only non-empty vectors are comonads due to @extract@
instance Comonad (Vec ('S n)) where
    extract (VC x _) = x
    duplicate = square

instance Known n => Distributive (Vec n) where
    distribute = distributeRep
    -- this gives us nice(r) transposes I think
    -- or at least we can now transpose through [] or so

-- | A vector of size @n@ with elements of type @a@ is isomorphic to a function from a type with @n@ values into @a@.
instance Known n => Representable (Vec n) where
    type Rep (Vec n) = Fin n

    tabulate = generate
    index = get

instance (Known n, Num a) => Num (Vec n a) where
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

-- | Split vector into @n@ pieces
split :: forall n m a. Nat n -> Nat m -> Vec (n :* m) a -> Vec n (Vec m a)
split NZ _ _     = VN
split n NZ _     = full VN n
split (NS (n :: Nat k)) m v = VC (take @(k :* m) m v) (split n m $ drop m v)

-- | Convert a type-list to a vector
toVec :: SingKind k => SList (xs :: [k]) -> Vec (Length xs) (Demote k)
toVec XNil = VN
toVec (XCons x xs) = VC (fromSing x) (toVec xs)

-- | Flatten a vector of vectors
concatenate :: Vec n (Vec m a) -> Vec (n :* m) a
concatenate VN = VN
concatenate (VC v vs) = v ++ concatenate vs

-- | Generate a vector by applying a function to a range of indices
generateN :: Nat n -> (Fin n -> a) -> Vec n a
generateN n f = f <$> enumFin n

-- | Generate a vector by applying a function to a range of indices, inferring the size from the type
generate :: Known n => (Fin n -> a) -> Vec n a
generate = generateN auto

-- | Build a vector by repeatedly applying a function to a seed
unfoldN :: Nat n -> (s -> (a, s)) -> s -> Vec n a
unfoldN NZ _ _ = VN
unfoldN (NS n) f z = VC a (unfoldN n f s) where
    (a, s) = f z

-- | Build a vector by repeatedly applying a function to a seed, inferring the size from the type
unfold :: Known n => (s -> (a, s)) -> s -> Vec n a
unfold = unfoldN auto

-- | Dependent vector fold. If @f :: N ~> *@ represents a natural index family and @v :: Vec n a@, then folding @dfold@ applies the folding function @n@ times,
-- resulting in a value of the type @f@ applied to @n@.
dfold :: Proxy f -> (forall k. Nat k -> a -> Apply f k -> Apply f ('S k)) -> Vec n a -> Apply f N0 -> Apply f n
dfold _ _ VN z = z
dfold p f (VC a v) z = f (size v) a (dfold p f v z)

-- | @iterateN n f x@ returns a vector of size @n@ of repeated applications of @f@ to @x@
iterateN :: Nat n -> (a -> a) -> a -> Vec n a
iterateN NZ     _ _ = VN
iterateN (NS n) f z = VC z (iterateN n f (f z))

-- | @iterate f x@ returns a vector of repeated applications of @f@ to @x@, inferring the size from the type
iterate :: Known n => (a -> a) -> a -> Vec n a
iterate = iterateN auto

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


type family Base (t :: N -> * -> *) :: N -> * -> * -> *

class IxRFunctor f where
    rmap :: forall a b c (n :: N). (b -> c) -> f n a b -> f n a c 

instance (forall (n :: N) a. Functor (f n a)) => IxRFunctor f where
    rmap f x = fmap f x

type family Pred (n :: N) :: N where
    Pred 'Z     = 'Z
    Pred ('S n) = n

class IxRFunctor (Base t) => Linear t where
    project :: t n a -> Base t n a (t (Pred n) a) 

data VecF n a b where
    Nil  :: VecF 'Z a b
    Cons :: forall n a b. a -> b -> VecF ('S n) a b

instance Functor (VecF n a) where
    fmap _ Nil = Nil
    fmap f (Cons a b) = Cons a (f b)

type instance Base Vec = VecF

instance Linear Vec where
    project VN        = Nil
    project (VC x xs) = Cons x xs

lcata :: Linear t => (forall n. Base t n a b -> b) -> t m a -> b
lcata f = f . rmap (lcata f) . project

size' :: Vec n a -> Int
size' = lcata \case
    Nil       -> 0
    Cons _ xs -> 1 + xs
