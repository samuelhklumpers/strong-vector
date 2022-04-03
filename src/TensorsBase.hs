{-# LANGUAGE UndecidableInstances #-}
-- | Tensors and basic operations
module TensorsBase where

import Data.Distributive
import Data.Functor.Rep
import GHC.Base (Any)

import Naturals
import VectorsBase
import SingBase
import Data.Proxy (Proxy (Proxy))
import Unsafe.Coerce (unsafeCoerce)


-- | The type for tensors with known dimensions.
-- NB: the constructor @TZ a@ represents the fact that the 0-tensor has 1 element,
-- since a tensor with dimensions @ns@ has @prod ns@ elements, and the nullary product is 1.
data Tensor ix a where
    TZ :: a -> Tensor '[] a
    TC :: Vec n (Tensor ix a) -> Tensor (n ': ix) a

deriving instance Eq a => Eq (Tensor ix a)

deriving instance Show a => Show (Tensor ix a)

instance Functor (Tensor ix) where
    fmap f (TZ a) = TZ (f a)
    fmap f (TC vs) = TC (fmap (fmap f) vs)

instance KnownNatList ix => Distributive (Tensor ix) where
    distribute = distributeRep

instance KnownNatList ix => Representable (Tensor ix) where
    type Rep (Tensor ix) = TList Fin ix

    tabulate = tabulateT
    index = getT

-- | Index a tensor with a list of indices
getT :: Tensor ix a -> TList Fin ix -> a
getT (TZ a)  XNil         = a
getT (TC vs) (XCons i ix) = getT (get vs i) ix

-- | Create a tensor from a generating function, provided the resulting dimensions are known
tabulateT :: KnownNatList ix => (TList Fin ix -> a) -> Tensor ix a
tabulateT = tabulateTN nats

-- | Generalization of @curry@ to @XList@.
-- Converts a @(n+1)@-ary list function into a function taking one value which returns a @n@-ary list function.
xCurry :: (XList f (x ': xs) -> a) -> Apply f x -> XList f xs -> a
xCurry f x xs = f (XCons x xs)

-- | Create a tensor from a generating function, given the dimensions
tabulateTN :: TList Nat ix -> (TList Fin ix -> a) -> Tensor ix a
tabulateTN ns f = fmap f (enumT ns)
--tabulateTN XNil f = TZ (f XNil)
--tabulateTN (XCons n ns) f = TC $ fmap (tabulateTN ns) (generateN n (xCurry f))

-- | The finite singleton type, refer to @Fin@ for the simpler finite type.
-- @Fin2@ extends @Fin@ by also carrying the index in a type parameter.
data Fin2 :: N -> N -> * where
    Fz :: Fin2 N0 ('S n)
    Fs :: Fin2 n m -> Fin2 ('S n) ('S m)

-- | List indexing type family. Is @Any@ when @i@ is invalid.
type family Get (xs :: [k]) (i :: N) :: k where
    Get '[] i            = Any
    Get (x ': xs) N0     = x
    Get (x ': xs) ('S i) = Get xs i

-- | List updating type family. Is @Any@ when @i@ is invalid.
type family Put (xs :: [k]) (i :: N) (x :: k) :: [k] where
    Put '[] i x            = '[]
    Put (_ ': xs) N0 x     = x ': xs
    Put (x ': xs) ('S i) y = x ': Put xs i y

-- | Swapping type family, @Swap i j xs@ is @xs@ with the elements at @i@ and @j@ swapped.
-- Is @Any@ when @i@ or @j@ is invalid.
type family Swap (i :: N) (j :: N) (xs :: [k]) :: [k] where
    Swap i j xs = Put (Put xs j (Get xs i)) i (Get xs j)

-- | Index an @XList@ with a @Fin2@
getX :: XList f xs -> Fin2 i (Length xs) -> Apply f (Get xs i)
getX (XCons x _) Fz      = x
getX (XCons _ xs) (Fs i) = getX xs i

-- | Unsafely index an @XList@ with a @Nat@
getX' :: XList f xs -> Nat i -> Apply f (Get xs i)
getX' XNil _              = undefined
getX' (XCons x _) NZ      = x
getX' (XCons _ xs) (NS n) = getX' xs n

-- | Typeclass encoding the result of the @Put@ family
class (ys ~ Put xs i x) => Putted xs i x ys where -- give this a better name
    putX :: Proxy x -> XList f xs -> Fin2 i (Length xs) -> Apply f x -> XList f ys

-- | Typeclass encoding the result of the @Put@ family. NB: @putX'@ is unsafe.
class (ys ~ Put xs i x) => Putted' xs i x ys where
    putX' :: Proxy x -> XList f xs -> Nat i -> Apply f x -> XList f ys

-- | Typeclass encoding the result of the @Swap@ family. NB: @swap@ is unsafe.
class (ys ~ Swap i j xs) => Swapped' xs i j ys where
    swap :: Nat i -> Nat j -> XList f xs -> XList f ys

instance (ys ~ Put xs i x) => Putted xs i x ys where
    putX _ (XCons _ xs) Fz y     = XCons y xs
    putX p (XCons x xs) (Fs i) y = XCons x (putX p xs i y)

instance (ys ~ Put xs i x) => Putted' xs i x ys where
    putX' _ XNil _ _              = undefined 
    putX' _ (XCons _ xs) NZ y     = XCons y xs
    putX' p (XCons x xs) (NS i) y = XCons x (putX' p xs i y)

instance (ys ~ Swap i j xs) => Swapped' xs i j ys where
    swap i j xs = putX' (Proxy @(Get xs j)) (putX' (Proxy @(Get xs i)) xs j (getX' xs i)) i (getX' xs j)

-- | Axiom: @length (put xs i x) == length xs@. Is absurd when @i@ or @j@ is invalid.
lengthLemma :: forall xs x i f. Proxy f -> Proxy x -> Proxy xs -> Proxy i -> Apply f (Length xs) -> Apply f (Length (Put xs i x))
lengthLemma _ _ _ _ = unsafeCoerce

-- | Safe @XList@ swap, @swapX i j xs@ is @xs@ with the elements at @i@ and @j@ swapped.
swapX :: forall i j xs ys f. (ys ~ Swap i j xs) => Fin2 i (Length xs) -> Fin2 j (Length xs) -> XList f xs -> XList f ys
swapX i j xs = putX (Proxy @(Get xs j)) (putX (Proxy @(Get xs i)) xs j (getX xs i)) i' (getX xs j) where
    i' :: Fin2 i (Length (Put xs j (Get xs i)))
    i' = lengthLemma (Proxy @(TyCon (Fin2 i))) (Proxy @(Get xs i)) (Proxy @xs) (Proxy @j) i

-- | Unsafely transpose two dimensions of a tensor, where the dimensions of the input tensor are assumed to be swapped.
transpose :: forall ix iy i j a. (KnownNatList ix, Swapped' ix i j iy) => Nat i -> Nat j -> Tensor iy a -> Tensor ix a
transpose i j t = tabulateT $ getT t . swap i j

-- | Axiom: @swap i j . swap i j == id@
swapLemma :: Swapped' ix i j iy => Nat i -> Nat j -> Tensor ix a -> Tensor (Swap i j iy) a
swapLemma _ _ = unsafeCoerce

-- | Unsafely transpose two dimensions of a tensor, where the dimensions of the output tensor are swapped.
-- Tends to behave more nicely with respect to ambiguity.
transpose' :: forall ix iy i j a. (KnownNatList iy, Swapped' ix i j iy) => Nat i -> Nat j -> Tensor ix a -> Tensor iy a
transpose' i j t = transpose @iy i j $ swapLemma i j t

-- | Safely transpose two dimensions of a tensor, where the dimensions of the input tensor are assumed to be swapped.
transpose2 :: forall ix iy i j a. (KnownNatList ix, Swapped' ix i j iy) => Fin2 i (Length ix) -> Fin2 j (Length ix) -> Tensor iy a -> Tensor ix a
transpose2 i j t = tabulateT $ getT t . swapX i j

-- | Flatten a tensor into a vector.
flatten :: Tensor ix a -> Vec (Prod ix) a
flatten (TZ a) = VC a VN
flatten (TC vs) = concatenate (flatten <$> vs)

-- | Given a list of dimensions, convert a vector into a tensor with those dimensions
enshape :: Vec (Prod ix) a -> SList ix -> Tensor ix a
enshape (VC a VN) XNil = TZ a
enshape v (XCons n ns) = TC $ flip enshape ns <$> split n (prod ns) v

-- | Given a list of dimensions, reshape a tensor to those dimensions
reshape :: Prod ix ~ Prod iy => Tensor ix a -> SList iy -> Tensor iy a
reshape t = enshape (flatten t)

enumT :: TList Nat ns -> Tensor ns (TList Fin ns)
enumT XNil         = TZ XNil
enumT (XCons n ns) = TC $ fmap (flip fmap (enumT ns) . XCons) (enumFin n)