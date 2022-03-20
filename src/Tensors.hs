{-# LANGUAGE UndecidableInstances #-}


module Tensors where

import Data.Distributive
import Data.Functor.Rep
import GHC.Base (Any)

import Naturals
import VectorsBase
import SingBase
import Data.Proxy (Proxy (Proxy))
import Unsafe.Coerce (unsafeCoerce)


-- | The type for tensors with known dimensions
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


getT :: Tensor ix a -> TList Fin ix -> a
getT (TZ a)  XNil         = a
getT (TC vs) (XCons i ix) = getT (get vs i) ix

tabulateT :: KnownNatList ix => (TList Fin ix -> a) -> Tensor ix a
tabulateT = tabulateTN nats

xCurry :: (XList f (x ': xs) -> a) -> Apply f x -> XList f xs -> a
xCurry f x xs = f (XCons x xs)

tabulateTN :: TList Nat ix -> (TList Fin ix -> a) -> Tensor ix a
tabulateTN XNil f = TZ (f XNil)
tabulateTN (XCons n ns) f = TC $ fmap (tabulateTN ns) (generateN n (xCurry f))

data Fin2 :: N -> N -> * where
    Fz :: Fin2 N0 ('S n)
    Fs :: Fin2 n m -> Fin2 ('S n) ('S m)

type family Get (xs :: [k]) (i :: N) :: k where
    Get '[] i            = Any -- Is there a type level "undefined"? -- yes
    Get (x ': xs) N0     = x
    Get (x ': xs) ('S i) = Get xs i

type family Put (xs :: [k]) (i :: N) (x :: k) :: [k] where
    Put '[] i x            = '[] -- TODO, shouldn't happen? -- we may switch to the FFin families in deprecate\SwapH, but these are problematic for other reasons
    Put (_ ': xs) N0 x     = x ': xs
    Put (x ': xs) ('S i) y = x ': Put xs i y

{-
type family Insert (xs :: [k]) (i :: N) (x :: k) = result | result -> xs i k where
    Insert xs N0 x            = x ': xs                 -- yet another family falls due to partial injectivity :(
    Insert (x ': xs) ('S i) y = x ': Insert xs i y
-}


getX :: XList f xs -> Nat i -> Apply f (Get xs i)
getX XNil _              = undefined -- Good? -- no but we can't do much about this
getX (XCons x _) NZ      = x
getX (XCons _ xs) (NS n) = getX xs n

getX' :: XList f xs -> Fin2 i (Length xs) -> Apply f (Get xs i)
getX' (XCons x _) Fz      = x
getX' (XCons _ xs) (Fs i) = getX' xs i

class (ys ~ Put xs i x) => Putted xs i x ys where -- give this a better name
    putX :: Proxy x -> XList f xs -> Nat i -> Apply f x -> XList f ys

--putX :: Putted xs i x ys => Proxy x -> XList f xs -> Nat i -> Apply f x -> XList f ys
instance (ys ~ Put xs i x) => Putted xs i x ys where
    putX _ XNil _ _              = undefined -- Good?
    putX _ (XCons _ xs) NZ y     = XCons y xs
    putX p (XCons x xs) (NS i) y = XCons x (putX p xs i y)


class (ys ~ Put xs i x) => Putted' xs i x ys where -- give this a better name
    putX' :: Proxy x -> XList f xs -> Fin2 i (Length xs) -> Apply f x -> XList f ys

instance (ys ~ Put xs i x) => Putted' xs i x ys where
    putX' _ (XCons _ xs) Fz y     = XCons y xs
    putX' p (XCons x xs) (Fs i) y = XCons x (putX' p xs i y)


type family Swap (i :: N) (j :: N) (xs :: [k]) :: [k] where
    Swap i j xs = Put (Put xs j (Get xs i)) i (Get xs j)

class (ys ~ Swap i j xs) => Swapped' xs i j ys where
    swap :: Nat i -> Nat j -> XList f xs -> XList f ys

instance (ys ~ Swap i j xs) => Swapped' xs i j ys where
    swap i j xs = putX (Proxy @(Get xs j)) (putX (Proxy @(Get xs i)) xs j (getX xs i)) i (getX xs j)

lengthLemma :: forall xs x i f. Proxy f -> Proxy x -> Proxy xs -> Proxy i -> Apply f (Length xs) -> Apply f (Length (Put xs i x))
lengthLemma _ _ _ _ = unsafeCoerce


swapX :: forall i j xs ys f. (ys ~ Swap i j xs) => Fin2 i (Length xs) -> Fin2 j (Length xs) -> XList f xs -> XList f ys
swapX i j xs = putX' (Proxy @(Get xs j)) (putX' (Proxy @(Get xs i)) xs j (getX' xs i)) i' (getX' xs j) where
    i' :: Fin2 i (Length (Put xs j (Get xs i)))
    i' = lengthLemma (Proxy @(TyCon (Fin2 i))) (Proxy @(Get xs i)) (Proxy @xs) (Proxy @j) i

    

transpose :: forall ix iy i j a. (KnownNatList ix, Swapped' ix i j iy) => Nat i -> Nat j -> Tensor iy a -> Tensor ix a
transpose i j t = tabulateT $ getT t . swap i j

transpose2 :: forall ix iy i j a. (KnownNatList ix, Swapped' ix i j iy) => Fin2 i (Length ix) -> Fin2 j (Length ix) -> Tensor iy a -> Tensor ix a
transpose2 i j t = tabulateT $ getT t . swapX i j

swapLemma :: Swapped' ix i j iy => Nat i -> Nat j -> Tensor ix a -> Tensor (Swap i j iy) a
swapLemma _ _ = unsafeCoerce

transpose' :: forall ix iy i j a. (KnownNatList iy, Swapped' ix i j iy) => Nat i -> Nat j -> Tensor ix a -> Tensor iy a
transpose' i j t = transpose @iy i j $ swapLemma i j t

{-
insX :: forall x y f xs i. XList f (Insert xs i y) -> Nat i -> Apply f x -> XList f (Insert xs i x)
insX = _


swapX :: forall i j f xs. Nat i -> Nat j -> XList f xs -> XList f (Swap xs i j)
swapX i j xs = putX @(Get xs j) (putX @(Get xs i) xs j (getX xs i)) i (getX xs j)


transpose' :: forall i j ix a. KnownNatList (Swap ix i j) => Tensor ix a -> Nat i -> Nat j -> Tensor (Swap ix i j) a
transpose' t i j = tabulateT $ getT t . unsafeCoerce . swapX i j
-}
