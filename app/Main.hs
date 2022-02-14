{-# LANGUAGE LambdaCase, DataKinds, PolyKinds, TypeFamilies, GADTs,
    ScopedTypeVariables, EmptyCase, UndecidableInstances,
    FlexibleInstances, TypeApplications, TemplateHaskell,
    StandaloneKindSignatures, DataKinds, TypeOperators,
    FlexibleContexts, ConstraintKinds, MultiParamTypeClasses  #-}


module Main where

import GHC.Exts (Constraint)
import Data.Constraint


data N = Z | S N

data Nat n where
    NZ :: Nat Z
    NS :: Nat n -> Nat (S n)
    
data Fin n where
    FZ :: Fin n
    FS :: Fin n -> Fin (S n)

data Vec a n where
    VN :: Vec a Z
    VC :: a -> Vec a n -> Vec a (S n)

type family (n :: N) + (m :: N) :: N
type instance Z + m     = m
type instance (S n) + m = S (n + m)

{-
class n <: m

instance Z <: S n
instance (n <: m) => S n <: S m
-}

class ToNat n where
    toNat :: Nat n


natVal :: forall n. ToNat n => Nat n
natVal = toNat :: Nat n

  
instance ToNat Z where
    toNat = NZ

instance ToNat n => ToNat (S n) where
    toNat = NS toNat

{-
class StrongNat n where
    strong :: Dict (m <: n) -> Nat m

leqTrans :: Nat x -> Nat y -> Nat z -> Dict (x <: y) -> Dict (y <: z) -> Dict (x <: z)
leqTrans _ _ NZ _ _                  = undefined
leqTrans _ NZ _ _ _                  = undefined
leqTrans NZ _ (NS z) _ _             = Dict
leqTrans (NS x) (NS y) (NS z) a b    = undefined

down :: Dict (m <: n) -> Dict (StrongNat n) -> Dict (StrongNat m)
down a b = undefined
-}

instance Show (Nat n) where
    show n = "Nat " ++ show (toInt n)
 
toInt :: Nat n -> Int
toInt NZ = 0
toInt (NS n) = 1 + toInt n

fromFin :: ToNat n => Fin n -> Nat n
fromFin f = natVal

{-
finToTup :: ToNat n => Fin (S n) -> (Int, Int)
finToTup f@FZ   = (0, toInt $ fromFin f)
finToTup (FS f) = (x + 1, y + 1) where
    (x, y) = finToTup f

instance ToNat (S n) => Show (Fin (S n)) where
    show f = "Fin " ++ show x ++ "/" ++ show y where
        (x, y) = finToTup f
-}

full :: a -> Nat n -> Vec a n
full a NZ     = VN
full a (NS n) = VC a (full a n)

vZip :: (a -> b -> c) -> Vec a n -> Vec b n -> Vec c n
vZip f VN VN = VN
vZip f (VC a vec) (VC b vec') = VC (f a b) (vZip f vec vec')

vFold :: (a -> b -> a) -> a -> Vec b n -> a  
vFold f x VN = x
vFold f x (VC b vec) = f (vFold f x vec) b

vMap :: (a -> b) -> Vec a n -> Vec b n
vMap f VN       = VN
vMap f (VC x v) = VC (f x) (vMap f v)

vConc :: Vec a n -> Vec a m -> Vec a (n + m)
vConc VN w       = w
vConc (VC x v) w = VC x (vConc v w)

vLen :: ToNat n => Vec a n -> Nat n
vLen v = natVal

enumF :: Nat n -> Vec (Fin n) n
enumF NZ     = VN
enumF (NS NZ) = VC FZ VN
enumF (NS (NS n)) = VC FZ (vMap FS (enumF (NS n)))

vSum :: Num a => Vec a n -> a
vSum = vFold (+) 0

delete :: Fin (S n) -> Vec a (S n) -> Vec a n
delete FZ (VC x v)          = v
delete (FS FZ) (VC x v)     = v
delete (FS (FS f)) (VC x v) = VC x (delete (FS f) v)

subMatrix :: Fin (S n) -> Fin (S m) -> Vec (Vec a (S m)) (S n) -> Vec (Vec a m) n
subMatrix f g v = vMap (delete g) $ delete f v

{-
det :: (Num a, ToNat n) => Vec (Vec a n) n -> a
det VN         = 0
det v@(VC _ _) = vSum $ vZip f (enumF $ vLen v) v where
    f j (VC x _) = x * minor FZ j v

minor :: (Num a, ToNat n) => Fin (S n) -> Fin (S n) -> Vec (Vec a (S n)) (S n) -> a
minor i j v = det (subMatrix i j v)
-}
main :: IO ()
main = putStrLn "hoi"
