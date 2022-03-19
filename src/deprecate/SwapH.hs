{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}


module SwapH where

import Naturals
import Vectors
import Data.Void

type family Pred (n :: N) :: N where
    Pred 'Z     = 'Z
    Pred ('S n) = n

type family Ok (n :: N) :: * where
    Ok 'Z     = Void
    Ok ('S n) = ()

data F n = InF (Ok n) | UpF (Ok n, F (Pred n))

type family IsInF (i :: F n) :: Bool where
    IsInF ('InF _) = 'True
    IsInF ('UpF _) = 'False

type family DownF (i :: F ('S n)) :: F n where
    DownF ('UpF '(_, f)) = f

type family ITE (i :: Bool) (t :: k) (e :: k) :: k where
    ITE 'True  t _ = t
    ITE 'False _ e = e

type family Get (xs :: [k]) (i :: F (Length xs)) :: k where
    Get (x ': ys) i = ITE (IsInF i) x (Get ys (DownF i))

type family Put (xs :: [k]) (i :: F (Length xs)) (x :: k) :: [k] where
    Put (x ': ys) f x' = ITE (IsInF f) (x' ': ys) (x ': Put ys (DownF f) x')

type family Put2 (xs :: [k]) (i :: F (Length xs)) (j :: F (Length xs)) (x :: k) (y :: k) :: [k] where
    Put2 (x ': ys) i j x' y' = ITE (IsInF i) (x' ': ITE (IsInF j) ys (Put ys (DownF j) y')) (ITE (IsInF j) (y' : Put ys (DownF i) x') (x ': Put2 ys (DownF i) (DownF j) x' y'))

type family Swap (xs :: [k]) (i :: F (Length xs)) (j :: F (Length xs)) :: [k] where
    Swap xs i j = Put2 xs j i (Get xs i) (Get xs j)

data FFin (n :: N) (i :: F n) where
    FFZ :: FFin ('S n) ('InF @('S n) '())
    FFS :: FFin ('S n) f -> FFin ('S ('S n)) ('UpF '( '(), f))

getH :: HList xs -> FFin (Length xs) i -> Get xs i
getH (HC a _) FFZ = a
getH (HC _ hl) (FFS ff) = getH hl ff

putH :: HList xs -> FFin (Length xs) i -> x -> HList (Put xs i x)
putH (HC _ hl) FFZ x'      = HC x' hl
putH (HC x hl) (FFS ff) x' = HC x $ putH hl ff x'

putH2 :: forall xs i j x y. HList xs -> FFin (Length xs) i -> FFin (Length xs) j -> x -> y -> HList (Put2 xs i j x y)
putH2 (HC _ hl) FFZ FFZ x _ = HC x hl
putH2 (HC _ hl) FFZ (FFS ff) x y = HC x $ putH hl ff y
putH2 (HC _ hl) (FFS ff) FFZ x y = HC y $ putH hl ff x
putH2 (HC a hl) (FFS ff) (FFS ff') x y = HC a $ putH2 hl ff ff' x y


swapH :: forall (xs :: [*]) i j. HList xs -> FFin (Length xs) i -> FFin (Length xs) j -> HList (Swap xs i j)
swapH hs i j = putH2 @xs @j @i @(Get xs i) @(Get xs j) hs j i (getH hs i) (getH hs j)
