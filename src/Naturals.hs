{-# LANGUAGE DataKinds, TypeFamilies, GADTs, TypeApplications, ConstraintKinds, ScopedTypeVariables, FlexibleInstances, TypeOperators, FlexibleContexts, MultiParamTypeClasses, EmptyCase, AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

-- | This module declares the type-level naturals for the type signatures of sized vectors,
-- along with the necessary machinery to manipulate them.
module Naturals where

import Data.Bifunctor (bimap)
import Data.Constraint ( Dict(..), (\\) )
import Data.Void (Void)
import Data.Constraint.Deferrable

-- | The boolean type.
data B = T | F

-- | The natural numbers type.
data N = Z | S N
-- Note that -XDataKinds lifts @N@ to a kind, and @Z@ and @S@ to type constructors

-- | The singleton type for natural numbers.
data Nat n where
    NZ :: Nat 'Z
    NS :: Nat n -> Nat ('S n)
-- The "singleton" in "singleton type" stems from the fact that for each choice of type parameters, the type has only a single inhabitant,
-- i.e. is a singleton in the terminology of sets.

-- | The finite set type.
-- Remark that @Fin n@ has @n@ values.
data Fin n where
    -- we use ('S n) here rather than n because:
    -- 1. Fin 'Z is uninhabited eitherway
    -- 2. some functions expect 'S n, for example see @delete@
    FZ :: Fin ('S n)
    FS :: Fin ('S n) -> Fin ('S ('S n))

-- | Proof that @f :: Fin 'Z@ if and only if @f@ is @undefined@
fin0 :: Fin 'Z -> Void
fin0 f = case f of {} -- there is no constructor for @Fin 'Z@, so we can discharge @f@ by simply pattern matching into an empty case expression

-- | Alternative to @FS@ that does not require @n ~ 'S m@
finS :: KnownNat n => Fin n -> Fin ('S n)
finS (f :: Fin n) = case nat :: Nat n of
    NZ   -> case f of {}
    NS _ -> FS f

-- | Type-level addition
type family (n :: N) + (m :: N) :: N where
    -- no generalized injectivity annotations :(
    -- => concretely this means we have to disambiguate every function that takes some @n + m@ containing argument
    'Z + m     = m
    ('S n) + m = 'S (n + m)

-- | Congruence for @'S@
congS :: n :~: m -> 'S n :~: 'S m
congS Refl = Refl

-- | Proof of associativity of @+@
plusAssoc :: Nat n -> Nat m -> Nat k -> (n + m) + k :~: n + (m + k)
plusAssoc NZ _ _ = Refl
plusAssoc (NS n') m k = congS $ plusAssoc n' m k

-- | Type-level multiplication
type family (n :: N) :* (m :: N) :: N where
    'Z :* m = 'Z
    -- no nested type instances without undecidable instances :(
    -- so move this somewhere else
    ('S n) :* m = m + (n :* m)

-- | Type-level less than
type family (n :: N) <: (m :: N) :: B where
    n <: 'Z      = 'F
    'Z <: 'S n   = 'T
    'S n <: 'S m = n <: m

-- | Type of evidence for less than
type n <? m = n <: m :~: 'T
-- can push this to a class or so to make writing this easier for the user

-- | Proof that if @n :* m@ is @'Z@, then at least one of them is @'Z@. 
factorZ :: Nat n -> Nat m -> (n :* m) :~: 'Z -> Either (n :~: 'Z) (m :~: 'Z)
factorZ NZ _ _ = Left Refl
factorZ _ NZ _ = Right Refl

-- | Alias for logical negation.
type Neg x = x -> Void

-- | ex falso [sequitur] quodlibet
exFalso :: Void -> a
exFalso v = case v of {}

-- | If @a \lor b@ and @\lnot b@, then @a@.
rightOrCancel :: Neg y -> Either x y -> x
rightOrCancel _ (Left x) = x
rightOrCancel c (Right y) = exFalso $ c y

-- | If @n <? m@, then @n@ is not @m@.
ltNeq :: Nat n -> Nat m -> n <? m -> Neg (m :~: n)
ltNeq (NS n) (NS m) p Refl = ltNeq n m p Refl


instance Show (Nat n) where
    show n = "Nat " ++ show (toInt n)

instance KnownNat n => Show (Fin n) where
    show f = "Fin " ++ show x ++ "/" ++ show y where
        (x, y) = finToTup f

-- | Convert @s :: Nat n@ to @n :: Int@
toInt :: Nat n -> Int
toInt NZ = 0
toInt (NS n) = 1 + toInt n

-- | Natural singleton addition
(+|) :: Nat n -> Nat m -> Nat (n + m)
NZ     +| n = n -- the definition of the @+@ family makes everything here typecheck smoothly
(NS n) +| m = NS (n +| m)

-- | Natural singleton multiplication
(*|) :: Nat n -> Nat m -> Nat (n :* m)
NZ     *| _ = NZ
(NS n) *| m = m +| (n *| m)

-- | Return the size of the set this @Fin@ is from
finSize :: KnownNat n => Fin n -> Nat n
finSize _ = nat

{- |
    Return the index and size of a @Fin@. 

    For example, @FS (FS FZ) :: Fin ('S ('S ('S ('S 'Z))))@ would become @(1, 4)@, indicating that it points to the 2nd element of a set of 4 elements. -}
finToTup :: KnownNat n => Fin n -> (Int, Int)
finToTup f@FZ = (0, toInt $ finSize f)
finToTup ((FS f) :: Fin n) = bimap (+1) (+1) $ finToTup f \\ lower (Dict @(KnownNat n))

-- | Point to the 0th (lowest) index in @Fin ('S n)@
toFZ :: Nat n -> Fin ('S n)
toFZ _ = FZ

-- | Point to the @n@th (highest) index in @Fin ('S n)@
toFS :: Nat n -> Fin ('S n)
toFS NZ     = FZ
toFS (NS n) = FS $ toFS n

-- | This class associates singleton values to type-level naturals.
-- Note that, unintuitively, @KnownNat n@ not hold universally for @n :: N@, (barring type reflection).
-- However, @KnownNat@ will hold for any concrete type, which is why we (I) refer to those @n@ with @KnownNat n@ as "constructible".
class KnownNat n where
    -- but also note that type reflection would not help either
    -- as in that case we again have to carry around @Typeable@

    -- Given doesn't work well: it makes instance constraints as large as instance heads, making some (all) undecidable
    nat :: Nat n

-- these instances ensure that any concrete @n@ has @KnownNat n@
instance KnownNat 'Z where
    nat = NZ

instance KnownNat n => KnownNat ('S n) where
    nat = NS nat

-- | If we have a singleton @Nat n@, then @n@ is constructible
know :: Nat n -> Dict (KnownNat n)
know NZ     = Dict              -- KnownNat 'Z
know (NS n) = Dict \\ know n    -- Apply KnownNat n => KnownNat ('S n) to KnownNat n

-- | If @'S n@ is constructible, then @n@ is constructible
lower :: Dict (KnownNat ('S n)) -> Dict (KnownNat n)
lower Dict = h nat where
    -- first construct @s :: Nat ('S n)@,
    -- then destruct it to get @t :: Nat n@,
    -- which is sufficient to prove @KnownNat n@.
    h :: Nat ('S n) -> Dict (KnownNat n)
    h (NS n) = know n
-- we can use lower as follows
-- x \\ lower (Dict @(KnownNat n))
-- to promote some x :: KnownNat m => a with @n ~ 'S m@
-- to KnownNat n => a

-- note that we use type applications here, like @(KnownNat n)
-- in this case, this is syntactic sugar over writing @Dict :: Dict (KnownNat n)@


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