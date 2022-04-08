{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Properties of natural number operations
module NaturalsProofs where


import Data.Constraint
import Data.Constraint.Deferrable
import Data.Void
import Unsafe.Coerce


import NaturalsBase
import NaturalsFams
import NaturalsFuns
import SingBase


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

-- | Congruence for @'S@
congS :: n :~: m -> 'S n :~: 'S m
congS Refl = Refl

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

-- | Proof that if @n + m@ and @n@ are known, then @m@ is too.
splitPlus :: forall n m. Dict (Known (n + m)) -> Dict (Known n) -> Dict (Known m)
splitPlus Dict Dict = h auto where
    h :: Nat n -> Dict (Known m)
    h NZ = Dict
    h (NS n) = splitPlus (lower Dict) (know n)

prodSub :: forall n m. Nat m -> Nat ('S n :* m) -> Nat (n :* m)
prodSub m nm = nm -| m \\ addCancel @m @(n :* m) m

-- * Axioms

-- | The following statements are unprovable (as far as I can tell), hence they are axioms.
plusZero :: Nat (n + 'Z) -> Nat n
plusZero = unsafeCoerce

oneMult :: Nat ('S 'Z :* n) -> Nat n
oneMult = unsafeCoerce

-- | Type-level division. (Use ill-advised)
divide :: forall n m. Nat m -> Nat (n :* m) -> Neq m 'Z -> Nat n
divide m nm p = case nm <| m of
    Yes _ -> unsafeCoerce NZ
    No _ ->  unsafeCoerce $ NS $ unsafeCoerce $ divide m (unsafeCoerce $ nm -| m) p


-- | If we have a singleton @Nat n@, then @n@ is constructible
know :: Nat n -> Dict (Known n)
know NZ     = Dict              -- Known 'Z
know (NS n) = Dict \\ know n    -- Apply Known n => Known ('S n) to Known n

-- | If @'S n@ is constructible, then @n@ is constructible
lower :: Dict (Known ('S n)) -> Dict (Known n)
lower Dict = h auto where
    -- first construct @s :: Nat ('S n)@,
    -- then destruct it to get @t :: Nat n@,
    -- which is sufficient to prove @Known n@.
    h :: Nat ('S n) -> Dict (Known n)
    h (NS n) = know n
-- we can use lower as follows
-- x \\ lower (Dict @(Known n))
-- to promote some x :: Known m => a with @n ~ 'S m@
-- to Known n => a

-- note that we use type applications here, like @(Known n)
-- in this case, this is syntactic sugar over writing @Dict :: Dict (Known n)@

