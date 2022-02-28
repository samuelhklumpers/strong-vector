{-# LANGUAGE DataKinds, TypeFamilies, GADTs, ConstraintKinds, ScopedTypeVariables, FlexibleInstances, TypeOperators, FlexibleContexts, MultiParamTypeClasses #-}

module Naturals where
import Data.Constraint


data N = Z | S N

data Nat n where
    NZ :: Nat 'Z
    NS :: Nat n -> Nat ('S n)

data Fin n where
    FI :: Fin ('S 'Z)
    FZ :: Fin ('S n) -> Fin ('S ('S n))
    FS :: Fin ('S n) -> Fin ('S ('S n))

type family (n :: N) + (m :: N) :: N where
    'Z + m     = m
    ('S n) + m = 'S (n + m)

instance Show (Nat n) where
    show n = "Nat " ++ show (toInt n)

instance Show (Fin ('S n)) where
    show f = "Fin " ++ show x ++ "/" ++ show y where
        (x, y) = finToTup f

toInt :: Nat n -> Int
toInt NZ = 0
toInt (NS n) = 1 + toInt n

(+|) :: Nat n -> Nat m -> Nat (n + m)
NZ +| n     = n
(NS n) +| m = NS (n +| m)

fromFin :: Fin ('S n) -> Nat ('S n)
fromFin FI     = NS NZ
fromFin (FZ f) = NS (fromFin f)
fromFin (FS f) = NS (fromFin f)

finToTup :: Fin ('S n) -> (Int, Int)
finToTup FI     = (0, 1)
finToTup (FZ f) = (0, 1 + toInt (fromFin f))
finToTup (FS f) = (x + 1, y + 1) where
    (x, y) = finToTup f

toFin :: Nat n -> Fin ('S n)
toFin NZ     = FI
toFin (NS n) = FZ $ toFin n

-- Given doesn't work well: it makes instance constraints as large as instance heads, making some (all) undecidable
class KnownNat n where
    nat :: Nat n

instance KnownNat 'Z where
    nat = NZ

instance KnownNat n => KnownNat ('S n) where
    nat = NS nat

know :: Nat n -> Dict (KnownNat n)
know NZ = Dict
know (NS n) = Dict \\ know n

lower :: Dict (KnownNat ('S n)) -> Dict (KnownNat n)
lower Dict = h nat where
    h :: Nat ('S n) -> Dict (KnownNat n)
    h (NS n) = know n

{-
lower' :: KnownNat ('S n) :- KnownNat n
lower' = unmapDict lower

lower'' :: Proxy n -> KnownNat ('S n) :- KnownNat n
lower'' _ = unmapDict lower
-}