{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Streams where

import SingBase
import Naturals



-- * Types

-- | The heterogeneous stream type, where the types in the stream are indexed by the @f :: N ~> *@ symbol.
-- Note that unlike how @XList@ has the @SList@ variant, there is no possible singleton equivalent @SStream@;
-- If this were a singleton type, then the underlying kind should be
-- @data Stream a = Next a (Stream a)@,
-- but all types inhabiting @Stream k@ would be infinite.
data XStream' :: (N ~> *) -> N -> * where
    XNext :: Apply f n -> XStream' f ('S n) -> XStream' f n

-- | The heterogeneous stream type, restricted to start counting from 0.
type XStream f = XStream' f N0


-- * Families

-- | @Fib n@ is the @n@th Fibonacci number.
type family Fib (n :: N) :: N where
    Fib N0          = N1
    Fib N1          = N1
    Fib ('S ('S n)) = Fib n + Fib ('S n)

-- | @RangeFrom n m@ is the list ranging from @n@ to @n + m@ excl.
type family RangeFrom (n :: N) (m :: N) :: [N] where
    RangeFrom n 'Z     = '[]
    RangeFrom n ('S m) = n ': RangeFrom ('S n) m


-- * Symbols

data ConstSym1 :: k1 -> k2 ~> k1
type instance Apply (ConstSym1 x) _ = x

data FibSym1 :: N ~> *
type instance Apply FibSym1 n = Nat (Fib n)


-- * Instances

instance (Show (Apply f n), Show (Apply f ('S n)), Show (Apply f ('S ('S n)))) => Show (XStream' f n) where
    show (XNext x (XNext y (XNext z _))) = "{" ++ show x ++ "," ++ show y ++ "," ++ show z ++ ",..."


-- * Functions

-- | @shead xs@ returns the head of @xs@
shead :: XStream' f n -> Apply f n
shead (XNext x _) = x

-- | @stail xs@ returns the tail stream of @xs@
stail :: XStream' f n -> XStream' f ('S n)
stail (XNext _ xs) = xs

-- | @stake n xs@ returns the list formed by taking @n@ elements of @xs@
stake :: Nat n -> XStream' f m -> XList f (RangeFrom m n)
stake NZ _ = XNil
stake (NS n) (XNext x xs) = XCons x (stake n xs)

-- | @fibonacci n@ is the @n@th Fibonacci @Nat@
fibonacci :: Nat n -> Nat (Fib n)
fibonacci NZ = na1
fibonacci (NS NZ) = na1
fibonacci (NS (NS n)) = fibonacci n +| fibonacci (NS n)

-- | @inf x@ is the stream of @x@s
inf :: a -> XStream' (ConstSym1 a) n
inf x = XNext x (inf x)

-- | @count@ is the @Nat@ stream counting from 0 onwards
count :: XStream (TyCon Nat)
count = help NZ where
    help :: Nat n -> XStream' (TyCon Nat) n
    help n = XNext n (help $ NS n)

-- | @fib@ is the stream of fibonacci @Nat@s
fib :: XStream FibSym1
fib = help NZ where
    help :: Nat n -> XStream' FibSym1 n
    help n = XNext (fibonacci n) (help $ NS n)