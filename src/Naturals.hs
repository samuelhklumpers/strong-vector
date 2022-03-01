{-# LANGUAGE DataKinds, TypeFamilies, GADTs, TypeApplications, ConstraintKinds, ScopedTypeVariables, FlexibleInstances, TypeOperators, FlexibleContexts, MultiParamTypeClasses, EmptyCase, AllowAmbiguousTypes #-}

module Naturals where
import Data.Constraint
import Data.Bifunctor (bimap)
import Data.Void (Void)


data N = Z | S N

data Nat n where
    NZ :: Nat 'Z
    NS :: Nat n -> Nat ('S n)

data Fin n where
    FZ :: Fin ('S n)
    FS :: Fin ('S n) -> Fin ('S ('S n))

fin0 :: Fin 'Z -> Void
fin0 f = case f of {}

finS :: KnownNat n => Fin n -> Fin ('S n)
finS (f :: Fin n) = case nat :: Nat n of
    NZ   -> case f of {}
    NS _ -> FS f

-- no generalized injectivity annotations :(
type family (n :: N) + (m :: N) :: N where
    'Z + m     = m
    ('S n) + m = 'S (n + m)

instance Show (Nat n) where
    show n = "Nat " ++ show (toInt n)

instance KnownNat n => Show (Fin ('S n)) where
    show f = "Fin " ++ show x ++ "/" ++ show y where
        (x, y) = finToTup f

toInt :: Nat n -> Int
toInt NZ = 0
toInt (NS n) = 1 + toInt n

(+|) :: Nat n -> Nat m -> Nat (n + m)
NZ +| n     = n
(NS n) +| m = NS (n +| m)

finSize :: KnownNat n => Fin n -> Nat n
finSize _ = nat

finToTup :: KnownNat n => Fin n -> (Int, Int)
finToTup f@FZ = (0, toInt $ finSize f)
finToTup ((FS f) :: Fin n) = bimap (+1) (+1) $ finToTup f \\ lower (Dict @(KnownNat n))

toFZ :: Nat n -> Fin ('S n)
toFZ _ = FZ

toFS :: Nat n -> Fin ('S n)
toFS NZ     = FZ
toFS (NS n) = FS $ toFS n


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

plusRightInj :: Nat n -> (n + m) :~: (n + k) -> m :~: k
plusRightInj NZ Refl = Refl
plusRightInj (NS n) Refl = plusRightInj n Refl

plusRightRev :: ('S n + m) :~: 'S k -> (n + m) :~: k
plusRightRev Refl = Refl

data ExistNat f where
    Witness :: Nat n -> Dict (f n) -> ExistNat f
-}