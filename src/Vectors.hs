{-# LANGUAGE DataKinds, TypeFamilies, GADTs, ScopedTypeVariables, FlexibleInstances, TypeOperators, FlexibleContexts, TypeApplications, AllowAmbiguousTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Vectors where

import Data.List ( intercalate )
import Control.Applicative ( liftA2 )
import Control.Comonad


import Naturals ( type (+), Fin(..), Nat(..), N(S, Z), KnownNat (nat), lower, toFZ, finS, know, toInt, plusRightInj, plusRightRev, ExistNat (Witness) )
import Data.Constraint ( (\\), Dict(..) )
import Data.Functor.Rep
import Data.Distributive

import Prelude hiding ( take )
import Data.Constraint.Deferrable


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
    show v = "<" ++ intercalate "," (map show $ vList v) ++ ">"

instance Eq a => Eq (Vec n a) where
    VN == VN         = True
    VC x v == VC y w = x == y && v == w

instance Functor (Vec n) where
    fmap _ VN       = VN
    fmap f (VC x v) = VC (f x) (fmap f v)

instance KnownNat n => Applicative (Vec n) where
    pure x = full x nat

    liftA2 _ VN VN = VN
    liftA2 f (VC a v) (VC b w) = VC (f a b) (liftA2 f v w \\ lower (Dict @(KnownNat n)))

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

generate :: KnownNat n => (Fin n -> a) -> Vec n a
generate = h nat where
    h :: Nat n -> (Fin n -> a) -> Vec n a
    h NZ _     = VN
    h (NS n) f = VC (f FZ) (h n (f . finS \\ know n)) -- :(

unfoldN :: Nat n -> (s -> (a, s)) -> s -> Vec n a
unfoldN NZ _ _ = VN
unfoldN (NS n) f z = VC a (unfoldN n f s) where
    (a, s) = f z

iterateN :: Nat n -> (a -> a) -> a -> Vec n a
iterateN NZ     _ _ = VN
iterateN (NS n) f z = VC z (iterateN n f (f z))

linspace :: Fractional a => a -> a -> Nat n -> Vec n a
linspace x y n = iterateN n step x where
    step z = z + (y - x) / fromIntegral (toInt n)

-- :))

class (k ~ (n + m)) => T k n m where
    witness :: k :~: n + m

instance (k ~ (n + m)) => T k n m where
    witness = Refl

{- 
-- :')
take :: (KnownNat m) => Nat n -> Vec (n + m) a -> Vec n a
take (n :: Nat n) (v :: Vec k a) = case ex of
    Witness m Dict -> take' n m v

    where
        npm :: Nat k
        npm = vLen v

        m :: Nat (k - n)
        m = npm -| n

        ex :: ExistNat (T k n)
        ex = Witness _ws _wt
-}
{-
    (f :: Nat m -> Vec (n + m) a -> Vec n a) -> f nat (v \\ pf)
        where
        pf :: npm :~: n + m
        pf = _ 
-}

take' :: forall n m a. Nat n -> Nat m -> Vec (n + m) a -> Vec n a
take' NZ     _ _        = VN
take' (NS n) m (VC a v) = VC a $ take' n m v

vHead :: Vec ('S n) a -> a
vHead (VC a _) = a

diag :: KnownNat n => Vec n (Vec n a) -> Vec n a
diag v = liftA2 get v (enumF $ vLen v)

vList :: Vec n a -> [a]
vList = vFold (flip (:)) []

full :: a -> Nat n -> Vec n a
full _ NZ     = VN
full a (NS n) = VC a (full a n)

vFold :: (a -> b -> a) -> a -> Vec n b -> a
vFold _ x VN = x
vFold f x (VC b vec) = f (vFold f x vec) b

vConc :: Vec n a -> Vec m a -> Vec (n + m) a
vConc VN w     = w
vConc (VC x v) w = VC x (vConc v w)

vLen :: Vec n a -> Nat n
vLen VN = NZ
vLen (VC _ v) = NS (vLen v)

enumF :: Nat n -> Vec n (Fin n)
enumF NZ          = VN
enumF (NS NZ)     = VC FZ VN
enumF (NS (NS n)) = VC (toFZ $ NS n) (fmap FS (enumF (NS n)))

vSum :: Num a => Vec n a -> a
vSum = vFold (+) 0

delete :: Fin ('S n) -> Vec ('S n) a -> Vec n a
delete FZ (VC _ v)    = v
delete (FS f) (VC x v) = VC x $ delete f v

subMatrix :: Fin ('S n) -> Fin ('S m) -> Vec ('S n) (Vec ('S m) a) -> Vec n (Vec m a)
subMatrix f g v = delete g <$> delete f v

det :: (KnownNat n, Num a) => Vec n (Vec n a) -> a
det VN             = 0
det (VC (VC x _) VN) = x
det (v@(VC _ w) :: Vec n (Vec n a)) = vSum $ (liftA2 \\ lower (Dict @(KnownNat n))) f (enumF $ vLen v) v where
    f j (VC x _) = (if even' j then 1 else -1) * x * (minor  \\ lower (Dict @(KnownNat n))) (toFZ $ vLen w) j v

    even' :: Fin m -> Bool
    even' FZ     = True
    even' (FS g) = not $ even' g

minor :: (KnownNat n, Num a) => Fin ('S n) -> Fin ('S n) -> Vec ('S n) (Vec ('S n) a) -> a
minor i j v = det (subMatrix i j v)

