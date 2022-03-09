{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

-- | This module declares the type-level naturals for the type signatures of sized vectors,
-- along with the necessary machinery to manipulate them.
module Naturals where

import Data.Bifunctor
import Data.Constraint
import Data.Void
import Data.Constraint.Deferrable
import Unsafe.Coerce

-- | The natural numbers type.
data N = Z | S N deriving (Eq, Show)
-- Note that -XDataKinds lifts @N@ to a kind, and @Z@ and @S@ to type constructors


n0 :: N
n1 :: N
n2 :: N
n3 :: N
n4 :: N
n5 :: N
n6 :: N
n7 :: N
n8 :: N
n9 :: N
n0 = Z
n1 = S n0
n2 = S n1
n3 = S n2
n4 = S n3
n5 = S n4
n6 = S n5
n7 = S n6
n8 = S n7
n9 = S n8

type N0 = 'Z
type N1 = 'S N0
type N2 = 'S N1
type N3 = 'S N2
type N4 = 'S N3
type N5 = 'S N4
type N6 = 'S N5
type N7 = 'S N6
type N8 = 'S N7
type N9 = 'S N8
type Digit = 'S N9

na0 :: Nat N0
na0 = NZ
na1 :: Nat N1
na1 = NS na0
na2 :: Nat N2
na2 = NS na1
na3 :: Nat N3
na3 = NS na2
na4 :: Nat N4
na4 = NS na3
na5 :: Nat N5
na5 = NS na4
na6 :: Nat N6
na6 = NS na5
na7 :: Nat N7
na7 = NS na6
na8 :: Nat N8
na8 = NS na7
na9 :: Nat N9
na9 = NS na8


type family (n :: N) .| (m :: N) :: N where
    n .| m = n :* Digit + m

-- | The singleton type for boolean.
data Boolean b where
    BT :: Boolean 'True
    BF :: Boolean 'False

deriving instance Show (Boolean b)

-- | The singleton type for natural numbers.
data Nat n where
    NZ :: Nat 'Z
    NS :: Nat n -> Nat ('S n)
-- The "singleton" in "singleton type" stems from the fact that for each choice of type parameters, the type has only a single inhabitant,
-- i.e. is a singleton in the terminology of sets.

deriving instance Eq (Nat n)


-- | The finite set type.
-- Remark that @Fin n@ has @n@ values.
data Fin n where
    -- we use ('S n) here rather than n because:
    -- 1. Fin 'Z is uninhabited eitherway
    -- 2. some functions expect 'S n, for example see @delete@
    FZ :: Fin ('S n)
    FS :: Fin ('S n) -> Fin ('S ('S n))

deriving instance Eq (Fin n)

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

-- | Type-level subtraction
type family (n :: N) - (m :: N) :: N where
    'Z - m          = 'Z
    n - 'Z          = n
    ('S n) - ('S m) = n - m

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

type family DivH (k :: N) (m :: N) (n :: N) (j :: N) :: N where
    -- thx agda-stdlib
    DivH k m 'Z     j      = k
    DivH k m ('S n) 'Z     = DivH ('S k) m n m
    DivH k m ('S n) ('S j) = DivH k      m n j

type family Div (n :: N) (m :: N) :: N where
    Div n ('S m) = DivH 'Z m n m


{-
-- | Proof of @n :* 1 ~ n@
mulRightId :: Nat n -> n :* 'S 'Z :~: n
mulRightId NZ = Refl
mulRightId (NS n) = congS $ mulRightId n
-}

-- | Type-level less than
type family (n :: N) <: (m :: N) :: Bool where
    n <: 'Z      = 'False
    'Z <: 'S n   = 'True
    'S n <: 'S m = n <: m

-- | Type of evidence for less than
type n <? m = n <: m :~: 'True
-- can push this to a class or so to make writing this easier for the user

-- | Proof that if @n :* m@ is @'Z@, then at least one of them is @'Z@. 
factorZ :: Nat n -> Nat m -> (n :* m) :~: 'Z -> Either (n :~: 'Z) (m :~: 'Z)
factorZ NZ _ _ = Left Refl
factorZ _ NZ _ = Right Refl

-- | Alias for logical negation.
type Neg x = x -> Void

type Neq x y = Neg (x :~: y)

-- | ex falso [sequitur] quodlibet
exFalso :: Void -> a
exFalso v = case v of {}

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


instance Show (Nat n) where
    show n = "Nat " ++ show (toInt n)

instance KnownNat n => Show (Fin n) where
    show f = "Fin " ++ show x ++ "/" ++ show y where
        (x, y) = finToTup f

-- | Convert @s :: Nat n@ to @n :: Int@
toInt :: Nat n -> Int
toInt NZ = 0
toInt (NS n) = 1 + toInt n

-- | Lower a Boolean to a boolean.
toB :: Boolean b -> Bool
toB BT = True
toB BF = False

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

-- | @toFin n m@ points to the @n@th index in an vector of size @n + m + 1@.
toFin :: Nat n -> Nat m -> Fin (n + 'S m)
toFin NZ m     = toFZ m
toFin (NS n) m = finS \\ know (n +| NS m) $ toFin n m

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

addCancel :: forall n m. Nat n -> (n + m) - n :~: m
addCancel NZ     = Refl
addCancel (NS n) = addCancel n

data Dec p where
    Yes :: p -> Dec p
    No :: Neg p -> Dec p

(<|) :: Nat n -> Nat m -> Dec (n <? m)
_ <| NZ          = No \case
NZ <| (NS _)     = Yes Refl
(NS n) <| (NS m) = n <| m


{-
bla :: Nat m -> Nat (n :* m) -> (n :* m) <? m -> n :~: 'Z
bla (NS _) NZ Refl = Refl
bla (NS n) (NS nat) Refl = _wv
-}


helper0 :: Nat (n + 'Z) -> Nat n
helper0 = unsafeCoerce

helper1 :: Nat ('S 'Z :* n) -> Nat n
helper1 = unsafeCoerce

helper2 :: forall n m. Nat m -> Nat ('S n :* m) -> Nat (n :* m)
helper2 m nm = nm -| m \\ addCancel @m @(n :* m) m

divide :: forall n m. Nat m -> Nat (n :* m) -> Neq m 'Z -> Nat n
divide m nm p = case nm <| m of
    Yes _ -> unsafeCoerce NZ
    No _ ->  unsafeCoerce $ NS $ unsafeCoerce $ divide m (unsafeCoerce $ nm -| m) p


splitPlus :: forall n m. Dict (KnownNat (n + m)) -> Dict (KnownNat n) -> Dict (KnownNat m)
splitPlus Dict Dict = h nat where
    h :: Nat n -> Dict (KnownNat m)
    h NZ = Dict
    h (NS n) = splitPlus (lower Dict) (know n)



{-
data ExistNat f where
    Witness :: Nat n -> Dict (f n) -> ExistNat f


class a + b ~ c => PlusEq (a :: N) (c :: N) (b :: N) where
    plusEq :: a + b :~: c

instance x ~ (a + b ~ c) => Class x (PlusEq a c b) where cls = Sub Dict

instance a + b ~ c => PlusEq a c b where
    plusEq = Refl

plusEqEvidence :: a + b :~: c -> Dict (PlusEq a c b)
plusEqEvidence Refl = Dict


temp :: forall a b c. Dict (PlusEq a c b) -> a + b :~: c
temp Dict = plusEq @a @c @b

minus :: Nat a -> Nat c -> a <? c -> ExistNat (PlusEq a c)
minus NZ c _          = Witness c Dict
minus (NS a :: Nat a) (NS c :: Nat c) l = case minus a c l of
    Witness (b :: Nat b) d -> Witness b r'
        where
        e = mapDict cls d
        p :: a + b :~: c
        p = plusEq @a @c @b \\ e
        r' :: Dict (PlusEq a c b)
        r' = plusEqEvidence p -- i don't know exactly why this works

minus' :: forall a c. Nat a -> Nat c -> ExistNat (PlusEq a c) -> a <? c -- oops you're supposed to use <=? here :)
minus' NZ NZ _                 = undefined
minus' NZ (NS _) _             = Refl
minus' (NS _) NZ (Witness _ d) = case temp d of {}
minus' (NS a) (NS c) w = _
-}

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
-}