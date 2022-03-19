{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}


module Tensors where

import Data.Distributive
import Data.Functor.Rep
import GHC.Base (Any)

import Naturals
import Vectors
import SingBase


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

type family Get (xs :: [k]) (i :: N) :: k where
    Get '[] i            = Any -- Is there a type level "undefined"? -- yes
    Get (x ': xs) N0     = x
    Get (x ': xs) ('S i) = Get xs i

type family Put (xs :: [k]) (i :: N) (x :: k) :: [k] where
    Put '[] i x            = '[] -- TODO, shouldn't happen? -- we may switch to the FFin families in deprecate\SwapH, but these are problematic for other reasons
    Put (_ ': xs) N0 x     = x ': xs
    Put (x ': xs) ('S i) y = x ': Put xs i y

type family Swap (xs :: [k]) (i :: N) (j :: N) :: [k] where
    Swap xs i j = Put (Put xs j (Get xs i)) i (Get xs j)

getX :: XList f xs -> Nat i -> Apply f (Get xs i)
getX XNil _              = undefined -- Good? -- no but we can't do much about this
getX (XCons x _) NZ      = x
getX (XCons _ xs) (NS n) = getX xs n

putX :: forall x f xs i. XList f xs -> Nat i -> Apply f x -> XList f (Put xs i x)
putX XNil _ _              = undefined -- Good?
putX (XCons _ xs) NZ y     = XCons y xs
putX (XCons x xs) (NS i) y = XCons x (putX @x xs i y)

swapX :: forall i j f xs. Nat i -> Nat j -> XList f xs -> XList f (Swap xs i j)
swapX i j xs = putX @(Get xs j) (putX @(Get xs i) xs j (getX xs i)) i (getX xs j)

transpose :: forall i j ix a. KnownNatList ix => Tensor (Swap ix i j) a -> Nat i -> Nat j -> Tensor ix a
transpose t i j = tabulate $ getT t . swapX @i @j i j
