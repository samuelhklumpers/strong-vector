{-# LANGUAGE DataKinds, TypeFamilies, GADTs, ScopedTypeVariables, FlexibleInstances, TypeOperators, FlexibleContexts #-}

module Main where

import Data.List ( intercalate )


data N = Z | S N

data Nat n where
    NZ :: Nat 'Z
    NS :: Nat n -> Nat ('S n)

data Fin n where
    FI :: Fin ('S 'Z)
    FZ :: Fin ('S n) -> Fin ('S ('S n))
    FS :: Fin ('S n) -> Fin ('S ('S n))

data Vec a n where -- the order of the params makes Vec not a Functor oops
    VN :: Vec a 'Z
    VC ::  a -> Vec a n -> Vec a ('S n)

vList :: Vec a n -> [a]
vList = vFold (flip (:)) []

instance Show a => Show (Vec a n) where
    show v = "<" ++ intercalate "," (map show $ vList v) ++ ">"


type family (n :: N) + (m :: N) :: N
type instance 'Z + m     = m
type instance ('S n) + m = 'S (n + m)

(+|) :: Nat n -> Nat m -> Nat (n + m)
NZ +| n     = n
(NS n) +| m = NS (n +| m)


toInt :: Nat n -> Int
toInt NZ = 0
toInt (NS n) = 1 + toInt n

instance Show (Nat n) where
    show n = "Nat " ++ show (toInt n)

fromFin :: Fin ('S n) -> Nat ('S n)
fromFin FI     = NS NZ
fromFin (FZ f) = NS (fromFin f)
fromFin (FS f) = NS (fromFin f)

finToTup :: Fin ('S n) -> (Int, Int)
finToTup FI     = (0, 1)
finToTup (FZ f) = (0, 1 + toInt (fromFin f))
finToTup (FS f) = (x + 1, y + 1) where
    (x, y) = finToTup f

instance Show (Fin ('S n)) where
    show f = "Fin " ++ show x ++ "/" ++ show y where
        (x, y) = finToTup f

full :: a -> Nat n -> Vec a n
full _ NZ     = VN
full a (NS n) = VC a (full a n)

vZip :: (a -> b -> c) -> Vec a n -> Vec b n -> Vec c n
vZip _ VN VN = VN
vZip f (VC a vec) (VC b vec') = VC (f a b) (vZip f vec vec')

vFold :: (a -> b -> a) -> a -> Vec b n -> a
vFold _ x VN = x
vFold f x (VC b vec) = f (vFold f x vec) b

vMap :: (a -> b) -> Vec a n -> Vec b n
vMap _ VN     = VN
vMap f (VC x v) = VC (f x) (vMap f v)

vConc :: Vec a n -> Vec a m -> Vec a (n + m)
vConc VN w     = w
vConc (VC x v) w = VC x (vConc v w)

vLen :: Vec a n -> Nat n
vLen VN = NZ
vLen (VC _ v) = NS (vLen v)

toFin :: Nat n -> Fin ('S n)
toFin NZ     = FI
toFin (NS n) = FZ $ toFin n

enumF :: Nat n -> Vec (Fin n) n
enumF NZ          = VN
enumF (NS NZ)     = VC FI VN
enumF (NS (NS n)) = VC (toFin $ NS n) (vMap FS (enumF (NS n)))

vSum :: Num a => Vec a n -> a
vSum = vFold (+) 0

delete :: Fin ('S n) -> Vec a ('S n) -> Vec a n
delete FI (VC _ VN)    = VN
delete (FZ _) (VC _ v) = v
delete (FS f) (VC x v) = VC x $ delete f v

subMatrix :: Fin ('S n) -> Fin ('S m) -> Vec (Vec a ('S m)) ('S n) -> Vec (Vec a m) n
subMatrix f g v = vMap (delete g) $ delete f v

det :: Num a => Vec (Vec a n) n -> a
det VN             = 0
det (VC (VC x _) VN) = x
det v@(VC _ w) = vSum $ vZip f (enumF $ vLen v) v where
    f j (VC x _) = (if even' j then 1 else -1) * x * minor (toFin $ vLen w) j v

    even' :: Fin n -> Bool
    even' FI     = True
    even' (FZ g) = even' g
    even' (FS g) = not $ even' g

minor :: Num a => Fin ('S n) -> Fin ('S n) -> Vec (Vec a ('S n)) ('S n) -> a
minor i j v = det (subMatrix i j v)

main :: IO ()
main = putStrLn "hoi"
