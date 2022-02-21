{-# LANGUAGE DataKinds, TypeFamilies, GADTs, ScopedTypeVariables, FlexibleInstances, TypeOperators, FlexibleContexts, MultiParamTypeClasses #-}

module Naturals where

import Data.Reflection ( Given(..) )

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

{-
instance Reifies n (Nat n) where
-}
instance Given (Nat n) where
    given = undefined  -- TODO replace with a reflected/coerced Nat

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