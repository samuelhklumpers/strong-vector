module NaturalsFuns where

import Data.Constraint
import Data.Void

import NaturalsBase
import NaturalsFams

-- * Functions

-- | Natural singleton addition
(+|) :: Nat n -> Nat m -> Nat (n + m)
NZ     +| n = n -- the definition of the @+@ family makes everything here typecheck smoothly
(NS n) +| m = NS (n +| m)

-- | Natural singleton subtraction
(-|) :: Nat n -> Nat m -> Nat (n - m)
NZ     -| _      = NZ
n      -| NZ     = n
(NS n) -| (NS m) = n -| m

-- | Natural singleton multiplication
(*|) :: Nat n -> Nat m -> Nat (n :* m)
NZ     *| _ = NZ
(NS n) *| m = m +| (n *| m)

-- | Proof that @f :: Fin 'Z@ if and only if @f@ is @undefined@
fin0 :: Fin 'Z -> Void
fin0 f = case f of {} -- there is no constructor for @Fin 'Z@, so we can discharge @f@ by simply pattern matching into an empty case expression

-- | Alternative to @FS@ that does not require @n ~ 'S m@
finS :: KnownNat n => Fin n -> Fin ('S n)
finS (f :: Fin n) = case nat :: Nat n of
    NZ   -> case f of {}
    NS _ -> FS f

-- | @toFin n m@ points to the @n@th index in an vector of size @n + m + 1@.
toFin :: Nat n -> Nat m -> Fin (n + 'S m)
toFin NZ m     = toFZ m
toFin (NS n) m = finS \\ know (n +| NS m) $ toFin n m

