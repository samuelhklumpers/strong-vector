{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

-- | This module declares the type-level naturals for the type signatures of sized vectors,
-- along with the necessary machinery to manipulate them.
module Naturals
    (module Naturals
    , module NaturalsBase)
    where

import Data.Constraint
import Data.Void
import Data.Constraint.Deferrable
import Unsafe.Coerce

import NaturalsBase


-- * Families

-- | Type-level addition
type family (n :: N) + (m :: N) :: N where
    -- no generalized injectivity annotations :(
    -- => concretely this means we have to disambiguate every function that takes some @n + m@ containing argument
    'Z + m     = m
    ('S n) + m = 'S (n + m)

-- | Type-level subtraction
type family (n :: N) - (m :: N) :: N where
    'Z - m          = 'Z
    n - 'Z          = n
    ('S n) - ('S m) = n - m

-- | Type-level multiplication
type family (n :: N) :* (m :: N) :: N where
    'Z :* m = 'Z
    -- no nested type instances without undecidable instances :(
    -- so move this somewhere else
    ('S n) :* m = m + (n :* m)

-- | Type-level digit concatentation. For example @N9 .| N1 .| N2@ can be read as the type of 912.
type family (n :: N) .| (m :: N) :: N where
    n .| m = n :* Digit + m

-- | Auxilliary family for type-level division
type family DivH (k :: N) (m :: N) (n :: N) (j :: N) :: N where
    -- thx agda-stdlib
    DivH k m 'Z     j      = k
    DivH k m ('S n) 'Z     = DivH ('S k) m n m
    DivH k m ('S n) ('S j) = DivH k      m n j

-- | Type-level division
type family Div (n :: N) (m :: N) :: N where
    Div n ('S m) = DivH 'Z m n m

-- | Type-level less than
type family (n :: N) <: (m :: N) :: Bool where
    n <: 'Z      = 'False
    'Z <: 'S n   = 'True
    'S n <: 'S m = n <: m


-- * Classes

-- | Inequality class
class (!~) a b where
    neq :: Neg (a :~: b)

-- * Instances

instance  'S n !~ 'Z where -- mildly hacky, but in general the larger unequal number is on the left of the !~
    neq = \case 

instance n !~ m => 'S n !~ 'S m where
    neq Refl = neq @n @m Refl -- we can pull this through a Decidable so we can always deduce n !~ m for concrete n, m when possible?

-- * Types

-- | Alias for logical negation.
type Neg x = x -> Void

-- | Alias for inequality.
type Neq x y = Neg (x :~: y)

-- | Type of evidence for less than
type n <? m = n <: m :~: 'True
-- can push this to a class or so to make writing this easier for the user


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

-- | @toFin n m@ points to the @n@th index in an vector of size @n + m + 1@.
toFin :: Nat n -> Nat m -> Fin (n + 'S m)
toFin NZ m     = toFZ m
toFin (NS n) m = finS \\ know (n +| NS m) $ toFin n m


-- * Proofs

-- | ex falso [sequitur] quodlibet
exFalso :: Void -> a
exFalso v = case v of {}

-- | Proof that if @n :* m@ is @'Z@, then at least one of them is @'Z@. 
factorZ :: Nat n -> Nat m -> (n :* m) :~: 'Z -> Either (n :~: 'Z) (m :~: 'Z)
factorZ NZ _ _ = Left Refl
factorZ _ NZ _ = Right Refl

-- | If @a \lor b@ and @\lnot b@, then @a@.
rightOrCancel :: Neg y -> Either x y -> x
rightOrCancel _ (Left x) = x
rightOrCancel c (Right y) = exFalso $ c y

-- | If @a \lor b@ and @\lnot a@, then @b@.
leftOrCancel :: Neg x -> Either x y -> y
leftOrCancel c (Left y) = exFalso $ c y
leftOrCancel _ (Right x) = x

-- | If @n <? m@, then @n@ is not @m@.
ltNeq :: Nat n -> Nat m -> n <? m -> Neg (m :~: n)
ltNeq (NS n) (NS m) p Refl = ltNeq n m p Refl

{-
-- | Proof of @n :* 1 ~ n@
mulRightId :: Nat n -> n :* 'S 'Z :~: n
mulRightId NZ = Refl
mulRightId (NS n) = congS $ mulRightId n
-}

-- | Congruence for @'S@
congS :: n :~: m -> 'S n :~: 'S m
congS Refl = Refl

-- | Proof that @f :: Fin 'Z@ if and only if @f@ is @undefined@
fin0 :: Fin 'Z -> Void
fin0 f = case f of {} -- there is no constructor for @Fin 'Z@, so we can discharge @f@ by simply pattern matching into an empty case expression

-- | Alternative to @FS@ that does not require @n ~ 'S m@
finS :: KnownNat n => Fin n -> Fin ('S n)
finS (f :: Fin n) = case nat :: Nat n of
    NZ   -> case f of {}
    NS _ -> FS f

-- | Proof of associativity of @+@
plusAssoc :: Nat n -> Nat m -> Nat k -> (n + m) + k :~: n + (m + k)
plusAssoc NZ _ _ = Refl
plusAssoc (NS n') m k = congS $ plusAssoc n' m k

-- | Proof that @-n@ is the additive inverse of @n@.
addCancel :: forall n m. Nat n -> (n + m) - n :~: m
addCancel NZ     = Refl
addCancel (NS n) = addCancel n

-- | Datatype of decidable propositions.
-- For example @n <? m@ is decidable for all @Nat n, Nat m@, since we can deconstruct their values to deduce a proof
-- of either @n <: m@ or @Neg (n <: m)@.
data Dec p where
    Yes :: p -> Dec p
    No :: Neg p -> Dec p

-- | Natural singleton comparison.
(<|) :: Nat n -> Nat m -> Dec (n <? m)
_ <| NZ          = No \case
NZ <| (NS _)     = Yes Refl
(NS n) <| (NS m) = n <| m

helper0 :: Nat (n + 'Z) -> Nat n
helper0 = unsafeCoerce

helper1 :: Nat ('S 'Z :* n) -> Nat n
helper1 = unsafeCoerce

helper2 :: forall n m. Nat m -> Nat ('S n :* m) -> Nat (n :* m)
helper2 m nm = nm -| m \\ addCancel @m @(n :* m) m

-- | Type-level division. (Use ill-advised)
divide :: forall n m. Nat m -> Nat (n :* m) -> Neq m 'Z -> Nat n
divide m nm p = case nm <| m of
    Yes _ -> unsafeCoerce NZ
    No _ ->  unsafeCoerce $ NS $ unsafeCoerce $ divide m (unsafeCoerce $ nm -| m) p

-- | Proof that if @n + m@ and @n@ are known, then @m@ is too.
splitPlus :: forall n m. Dict (KnownNat (n + m)) -> Dict (KnownNat n) -> Dict (KnownNat m)
splitPlus Dict Dict = h nat where
    h :: Nat n -> Dict (KnownNat m)
    h NZ = Dict
    h (NS n) = splitPlus (lower Dict) (know n)
