module Deprecate where

    
{-
-- a block tensor is described by a list of lists of dimensions
-- so we have 2 levels of stacking operations
data Block ix a where
    BLV :: Vec n a -> Block (': (': n '[]) '[]) a   -- a vector is a "column block"
    BLC :: Vec n (Block ix a) -> Block (': iy ix) a -> Block (': (': n iy) ix) a -- n blocks + a chain of vectors of blocks (of the same shape) -> longer chain of blocks
    BLS :: Vec n (Block ix a) -> Block (': (': n '[]) ix) a -- n blocks -> block of higher dimension

type Sparse (ix :: HL N) a = M.Map (HList ix) a

type family Sing :: k -> Type

data SomeSing k where
    SomeSing :: Sing (a :: k) -> SomeSing k

class SingKind k where
    type Demote k = (r :: Type) | r -> k

    fromSing :: Sing (a :: k) -> Demote k
    toSing :: Demote k -> SomeSing k

getL :: HList (xs :: HL k) -> Fin (Length xs) -> Demote k
getL (HC x _) FZ = x
getL xs (FS fin) = _wd
-}



{-
-- | Flatten a tensor into a vector.
flatten :: Tensor ix a -> Vec (Prod ix) a
flatten (TV v) = v \\ mulRightId (size v)
flatten (TC vs) = concatenate $ fmap flatten vs
-}

{-
toShape :: Vec (Prod ix) a -> List ix -> Neg (ix :~: 'Nil) -> Tensor ix a
toShape VN (LC n LN) c          = undefined -- TV VN
toShape VN (LC n (LC nat li)) c = undefined -- _wy
toShape (VC a vec) ns c         = undefined -- _wt

reshape :: Tensor ix a -> List ix' -> Neg (ix' :~: 'Nil) -> Prod ix :~: Prod ix' -> Tensor ix' a
reshape t ns c pf = toShape (flatten t \\ pf) ns c
-}


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
