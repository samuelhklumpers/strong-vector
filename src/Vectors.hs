{-# LANGUAGE DataKinds, TypeFamilies, GADTs, ScopedTypeVariables, FlexibleInstances, TypeOperators, FlexibleContexts, TypeApplications #-}

module Vectors where

import Data.List ( intercalate )
import Control.Applicative ( liftA2 )

import Naturals ( type (+), Fin(..), Nat(..), N(S, Z), KnownNat (nat), lower )
import Data.Constraint ( (\\), Dict(..) )


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
  sequenceA (VC x v) = VC <$> x <*> (sequenceA v  \\ lower (Dict @(KnownNat n)))


get :: Vec n a -> Fin n -> a
get (VC a _) FI     = a
get (VC a _) (FZ _) = a
get (VC _ v) (FS f) = get v f

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

toFin :: Nat n -> Fin ('S n)
toFin NZ     = FI
toFin (NS n) = FZ $ toFin n

enumF :: Nat n -> Vec n (Fin n)
enumF NZ          = VN
enumF (NS NZ)     = VC FI VN
enumF (NS (NS n)) = VC (toFin $ NS n) (fmap FS (enumF (NS n)))

vSum :: Num a => Vec n a -> a
vSum = vFold (+) 0

delete :: Fin ('S n) -> Vec ('S n) a -> Vec n a
delete FI (VC _ VN)    = VN
delete (FZ _) (VC _ v) = v
delete (FS f) (VC x v) = VC x $ delete f v

subMatrix :: Fin ('S n) -> Fin ('S m) -> Vec ('S n) (Vec ('S m) a) -> Vec n (Vec m a)
subMatrix f g v = delete g <$> delete f v

det :: (KnownNat n, Num a) => Vec n (Vec n a) -> a
det VN             = 0
det (VC (VC x _) VN) = x
det (v@(VC _ w) :: Vec n (Vec n a)) = vSum $ (liftA2 \\ lower (Dict @(KnownNat n))) f (enumF $ vLen v) v where
    f j (VC x _) = (if even' j then 1 else -1) * x * (minor  \\ lower (Dict @(KnownNat n))) (toFin $ vLen w) j v

    even' :: Fin m -> Bool
    even' FI     = True
    even' (FZ g) = even' g
    even' (FS g) = not $ even' g

minor :: (KnownNat n, Num a) => Fin ('S n) -> Fin ('S n) -> Vec ('S n) (Vec ('S n) a) -> a
minor i j v = det (subMatrix i j v)

