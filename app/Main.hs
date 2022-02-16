{-# LANGUAGE DataKinds, TypeFamilies, GADTs, ScopedTypeVariables, FlexibleInstances, TypeOperators, FlexibleContexts #-}

module Main where

import Data.Constraint ( (\\), unmapDict, type (:-), Dict(..) )
import Data.List ( intercalate )


data N = Z | S N

data Nat n where
    NZ :: Nat 'Z
    NS :: Nat n -> Nat ('S n)

data Fin n where
    FZ :: Fin ('S n)
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

fromFin :: forall n. Known ('S n) => Fin ('S n) -> Nat ('S n)
fromFin FZ     = nat
fromFin (FS _) = nat \\ (Dict :: Dict (Known ('S ('S n))))
-- ^ why does this not need a @down@?????

finToTup :: forall n. Known ('S n) => Fin ('S n) -> (Int, Int)
finToTup f@FZ  = (0, toInt $ fromFin f)
finToTup (FS f) = (x + 1, y + 1) where
    (x, y) = finToTup f \\ (down Dict :: Dict (Known n))

instance Known ('S n) => Show (Fin ('S n)) where
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

vLen :: Known n => Vec a n -> Nat n
vLen VN = NZ
vLen (VC _ _) = nat

enumF :: Nat n -> Vec (Fin n) n
enumF NZ     = VN
enumF (NS NZ) = VC FZ VN
enumF (NS (NS n)) = VC FZ (vMap FS (enumF (NS n)))

vSum :: Num a => Vec a n -> a
vSum = vFold (+) 0

delete :: Fin ('S n) -> Vec a ('S n) -> Vec a n
delete FZ (VC  _ v)        = v
delete (FS  FZ) (VC _ v) = v
delete (FS  (FS f)) (VC x v) = VC x (delete (FS f) v)

subMatrix :: Fin ('S n) -> Fin ('S m) -> Vec (Vec a ('S m)) ('S n) -> Vec (Vec a m) n
subMatrix f g v = vMap (delete g) $ delete f v

-- | not quite the determinant, put (-1) ** x here when implemented
det :: (Known n, Num a) => Vec (Vec a n) n -> a
det VN             = 0
det (VC (VC x _) VN) = x
det v@VC {} = vSum $ vZip f (enumF $ vLen v) v where
    f j (VC x _) = (if even' j then 1 else -1) * x * minor FZ j v

    even' :: Fin n -> Bool
    even' FZ = True
    even' (FS n) = not $ even' n

minor :: forall n a. (Known ('S n), Num a) => Fin ('S n) -> Fin ('S n) -> Vec (Vec a ('S n)) ('S n) -> a
minor i j v = det (subMatrix i j v) \\ (down Dict :: Dict (Known n))

main :: IO ()
main = putStrLn "hoi"


class Known n where
    nat :: Nat n

instance Known 'Z where
    nat = NZ

instance Known n => Known ('S n) where
    nat = NS nat

know :: Nat n -> Dict (Known n)
know NZ = Dict
know (NS n) = case know n of
    Dict -> Dict

down :: Dict (Known ('S n)) -> Dict (Known n)
down Dict = h nat where
    h :: Nat ('S n) -> Dict (Known n)
    h (NS n) = know n

down' :: Known ('S n) :- Known n -- turns out this one is less useful than the one above
down' = unmapDict down              -- or is it?

test :: forall n. Known ('S n) => Nat n
test = case down Dict of
    (Dict :: Dict (Known n)) -> nat
