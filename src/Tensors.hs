module Tensors where

import Data.Distributive
import Data.Functor.Rep

import Naturals
import Vectors
import SingBase


-- | The type for tensors with known dimensions
data Tensor ix a where
    TZ :: a -> Tensor '[] a
    TC :: Vec n (Tensor ix a) -> Tensor (n ': ix) a

instance Functor (Tensor ix) where
    fmap f (TZ a) = TZ (f a)
    fmap f (TC vs) = TC (fmap (fmap f) vs)

instance Distributive (Tensor ix) where
    distribute = distributeRep

instance Representable (Tensor ix) where
    type Rep (Tensor ix) = TList Fin ix

    tabulate = undefined

    index (TZ a) XNil = a
    index (TC vs) (XCons ap xl) = undefined


{-
vec2 :: Int -> Int -> Vec N2 Int
vec2 a b = VC a (VC b VN)

myTensor11 :: Tensor (N1 ': N1 ': '[]) Int -- 1x1 tensor equals 1x1 matrix
myTensor11 = TC $ VC (TV (VC 5 VN)) VN

myTensor2 :: Tensor (N2 ': '[]) Int  -- 2 tensor equals 2-vector
myTensor2 = TV (vec2 5 8)

myTensor22 :: Tensor (N2 ': N2 ': '[]) Int  -- 2x2 tensor
myTensor22 = TC $ VC (TV (vec2 1 2)) (VC (TV $ vec2 3 4) VN)



-- | Return the transpose of a matrix
transpose :: KnownNat m => Vec n (Vec m a) -> Vec m (Vec n a)
transpose = transpose' nat
    where transpose' :: Nat m -> Vec n (Vec m a) -> Vec m (Vec n a)
          transpose' m VN                = full VN m -- We want a vector of length m with VN elements
          transpose' NZ (VC VN _)         = VN
          transpose' (NS m') v@(VC (VC _ _) _) = VC (Vectors.head <$> v) (transpose' m' (Vectors.tail <$> v))

transposeT :: Tensor ix a -> Nat i -> Nat j -> Tensor (Swap ix i j) a
transposeT x i j = undefined -- tabulate (swap'' (Data.Functor.Rep.index x) i j)

type family Get (l :: [k]) (i :: N) :: k where
    Get '[] i             = N0 -- TODO; Is there a type level "undefined"?
    Get (n ': l) N0     = n
    Get (n ': l) ('S i') = Get l i'

type family Put (l :: [k]) (i :: N) (n :: k) :: [k] where
    Put '[] i n = '[] -- TODO, shouldn't happen?
    Put (n' ': l) N0 n = n ': l
    Put (n' ': l) ('S i') n = n' ': Put l i' n

type family Swap (l :: [k]) (i :: N) (j :: N) :: [k] where
    Swap l i j = Put (Put l j (Get l i)) i (Get l j)

get'' :: forall (xs :: [*]) i. HList xs -> Nat i -> Get xs i
get'' HN _             = undefined -- Good?
get'' (HC x _) NZ      = x
get'' (HC _ xs) (NS n) = get'' xs n

put'' :: forall (xs :: [*]) i x. HList xs -> Nat i -> x -> HList (Put xs i x)
put'' HN _ _             = undefined -- Good?
put'' (HC _ xs) NZ y     = HC y xs
put'' (HC x xs) (NS n) y = HC x $ put'' xs n y

swap'' :: forall (xs :: [*]) i j. HList xs -> Nat i -> Nat j -> HList (Swap xs i j)
swap'' xs i j = put'' (put'' xs j (get'' xs i)) i (get'' xs j)

-- Suppose we transpose Index 0 and 1 (0-indexed) of myTensor22

myTensor22' :: Tensor (N2 ': N2 ': '[]) Int  -- 2x2 tensor
myTensor22' = TC $ VC (TV (vec2 5 6)) (VC (TV $ vec2 7 8) VN)

myTensor222 :: Tensor (N2 ': N2 ': N2 ': '[]) Int -- 2x2x2 tensor
myTensor222 = TC $ VC myTensor22 (VC myTensor22' VN)
-}
