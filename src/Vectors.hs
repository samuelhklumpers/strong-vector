{-# LANGUAGE DataKinds, TypeFamilies, GADTs, ScopedTypeVariables, FlexibleInstances, TypeOperators, FlexibleContexts, TypeApplications, AllowAmbiguousTypes #-}

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


data L = Nil | Cons N L -- restricted to N for now
-- refer to SingKind for generalized stuff.

data List xs where
    LN :: List 'Nil
    LC :: Nat n -> List xs -> List ('Cons n xs)

data Vec n a where
    VN :: Vec 'Z a
    VC ::  a -> Vec n a -> Vec ('S n) a

data Tensor ix a where
    TN :: Tensor 'Nil a
    TC :: Vec n (Tensor ix a) -> Tensor ('Cons n ix) a

instance Show a => Show (Vec n a) where
    show v = "<" P.++ intercalate "," (map show $ toList v) P.++ ">"

instance Eq a => Eq (Vec n a) where
    VN == VN         = True
    VC x v == VC y w = x == y && v == w

instance Functor (Vec n) where
    fmap _ VN       = VN
    fmap f (VC x v) = VC (f x) (fmap f v)

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
  sequenceA VN = pure VN
  sequenceA (VC x v) = VC <$> x <*> (sequenceA v \\ lower (Dict @(KnownNat n)))

instance Comonad (Vec ('S n)) where
    extract (VC x _) = x
    duplicate v = fmap (const v) v

instance KnownNat n => Distributive (Vec n) where
    distribute = distributeRep -- this gives us nice(r) transposes I think
    -- or at least we can now transpose through [] or so

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


get :: Vec n a -> Fin n -> a
get (VC a _) FZ     = a
get (VC _ v) (FS f) = get v f


generateN :: Nat n -> (Fin n -> a) -> Vec n a
generateN NZ _     = VN
generateN (NS n) f = VC (f FZ) (generateN n (f . finS \\ know n))

generate :: KnownNat n => (Fin n -> a) -> Vec n a
generate = generateN nat


unfoldN :: Nat n -> (s -> (a, s)) -> s -> Vec n a
unfoldN NZ _ _ = VN
unfoldN (NS n) f z = VC a (unfoldN n f s) where
    (a, s) = f z

unfold :: KnownNat n => (s -> (a, s)) -> s -> Vec n a
unfold = unfoldN nat


iterateN :: Nat n -> (a -> a) -> a -> Vec n a
iterateN NZ     _ _ = VN
iterateN (NS n) f z = VC z (iterateN n f (f z))

iterate :: KnownNat n => (a -> a) -> a -> Vec n a
iterate = iterateN nat


linspace :: Fractional a => a -> a -> Nat n -> Vec n a
linspace x y n = iterateN n step x where
    step z = z + (y - x) / fromIntegral (toInt n)


take :: forall m n a. Nat n -> Vec (n + m) a -> Vec n a
take NZ     _                   = VN
take (NS (n :: Nat k)) (VC a v) = VC a $ take @m n v

drop :: forall n m a. Nat n -> Vec (n + m) a -> Vec m a
drop NZ v = v
drop (NS k) (VC _ v) = drop k v


head :: Vec ('S n) a -> a
head (VC a _) = a

tail :: Vec ('S n) a -> Vec n a
tail (VC _ v) = v


zipWith :: (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
zipWith _ VN       VN = VN
zipWith f (VC a v) (VC b w) = VC (f a b) (zipWith f v w)

diag :: Vec n (Vec n a) -> Vec n a
diag v = zipWith get v (enumFin $ size v)

toList :: Vec n a -> [a]
toList = foldl (flip (:)) []

full :: a -> Nat n -> Vec n a
full _ NZ     = VN
full a (NS n) = VC a (full a n)

(++) :: Vec n a -> Vec m a -> Vec (n + m) a
VN ++ w     = w
VC x v ++ w = VC x (v ++ w)

size :: Vec n a -> Nat n
size VN = NZ
size (VC _ v) = NS (size v)

enumFin :: Nat n -> Vec n (Fin n)
enumFin NZ          = VN
enumFin (NS NZ)     = VC FZ VN
enumFin (NS (NS n)) = VC (toFZ $ NS n) (fmap FS (enumFin (NS n)))

enumerate :: Vec n a -> Vec n (Fin n, a)
enumerate v = zipWith (,) (enumFin $ size v) v

delete :: Fin ('S n) -> Vec ('S n) a -> Vec n a
delete FZ (VC _ v)    = v
delete (FS f) (VC x v) = VC x $ delete f v

subMatrix :: Fin ('S n) -> Fin ('S m) -> Vec ('S n) (Vec ('S m) a) -> Vec n (Vec m a)
subMatrix f g v = delete g <$> delete f v

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

minor :: Num a => Fin ('S n) -> Fin ('S n) -> Vec ('S n) (Vec ('S n) a) -> a
minor i j v = det (subMatrix i j v)

