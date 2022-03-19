-- | This module declares the type-level naturals for the type signatures of sized vectors,
-- along with the necessary machinery to manipulate them.
module NaturalsBase where
-- splitting this from Naturals; this part doesn't require UndecidableInstances or AllowAmbiguousTypes

import Data.Constraint

import SingBase


-- * Types

-- | The natural numbers type.
data N = Z | S N deriving (Eq, Show)
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

-- | The singleton type for boolean.
data Boolean b where
    BT :: Boolean 'True
    BF :: Boolean 'False

-- * Classes

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


-- * Instances

type instance Sing = Nat
type instance Sing = Boolean

instance SingKind Bool where
    type Demote Bool = Bool

    fromSing BT = True
    fromSing BF = False

instance Show (Nat n) where
    show n = "Nat " ++ show (toInt n)

instance KnownNat n => Show (Fin n) where
    show f = "Fin " ++ show x ++ "/" ++ show y where
        (x, y) = finToTup f

deriving instance Show (Boolean b)


deriving instance Eq (Nat n)
deriving instance Eq (Fin n)
deriving instance Eq (Boolean b)


-- * Functions

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
nD :: N
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
nD = S n9

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
naD :: Nat Digit
naD = NS na9

-- | Convert @s :: Nat n@ to @n :: Int@
toInt :: Nat n -> Int
toInt NZ = 0
toInt (NS n) = 1 + toInt n

-- | Return the size of the set this @Fin@ is from
finSize :: KnownNat n => Fin n -> Nat n
finSize _ = nat

{- |
    Return the index and size of a @Fin@. 

    For example, @FS (FS FZ) :: Fin ('S ('S ('S ('S 'Z))))@ would become @(1, 4)@, indicating that it points to the 2nd element of a set of 4 elements. -}
finToTup :: KnownNat n => Fin n -> (Int, Int)
finToTup f = (finToInt f, toInt $ finSize f)

finToInt :: Fin n -> Int
finToInt FZ     = 0
finToInt (FS f) = 1 + finToInt f

-- | Lower a Boolean to a boolean.
toB :: Boolean b -> Bool
toB BT = True
toB BF = False


-- | Point to the 0th (lowest) index in @Fin ('S n)@
toFZ :: Nat n -> Fin ('S n)
toFZ _ = FZ

-- | Point to the @n@th (highest) index in @Fin ('S n)@
toFS :: Nat n -> Fin ('S n)
toFS NZ     = FZ
toFS (NS n) = FS $ toFS n


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

