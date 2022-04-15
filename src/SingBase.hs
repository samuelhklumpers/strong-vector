{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}


-- | The singleton family, function symbol applications, the [] singleton SList and it's generalization XList.
-- Partially adapted from [singletons](https://hackage.haskell.org/package/singletons).
module SingBase where


-- | The singleton family, connecting the underlying types to their singleton type.
-- For example
--  @Sing N       = Nat@
--  @Sing B       = Boolean@
--  @Sing [N]     = SList N@
--  @Sing (Fin n) = SFin n@
type family Sing (x :: k) = (y :: *) | y -> x
-- ^ As opposed to the @Sing@ family of singletons, our variant is not eta-reduced,
-- allowing us to define @Fin n@ as a singleton type.


-- | The datatype representing a domain-codomain pair
data TyFun :: * -> * -> *
-- | The type of type-level function symbols: by viewing @k1 ~> k2@ as the argument to @Apply@, it represents a partially applied type family
type k1 ~> k2 = TyFun k1 k2 -> *
infixr 0 ~> 

-- | The type symbol application family.
-- To defunctionalize a family @type family X k1 :: k2@, one has to define a @data SymX :: k1 ~> k2@
-- and a @type instance Apply SymX x = X x@.
type family Apply (f :: k1 ~> k2) (x :: k1) :: k2

-- | Type constructor symbol, @Tycon tc@ corresponds to @tc@.
data TyCon :: (k1 -> k2) -> k1 ~> k2
type instance Apply (TyCon tc) x = tc x

-- | Singleton symbol, @Apply SingSym k@ is the singleton associated to the kind @k@
data SingSym :: k ~> *
type instance Apply SingSym x = Sing x

-- | Dependent list type.
-- If @F : k ~> *@ represents a family of types indexed by @k@, and @xs : [k]@, then @XList F xs@ is the heterogeneous list with elements of types "@F@ mapped over @xs@". 
data XList :: forall k. (k ~> *) -> [k] -> * where
    XNil   :: forall k (f :: k ~> *). XList f ('[] :: [k])
    XCons  :: forall k (f :: k ~> *) (x :: k) (xs :: [k]). Apply f (x :: k) -> XList f (xs :: [k]) -> XList f (x ': xs)

-- | Singleton list type, @SList k@ is the list of singletons associated to the kind @k@
type SList = XList SingSym
type instance Sing x = SList x

-- | Specialized version of @XList@ for type constructors
type TList tc = XList (TyCon tc)

-- | Simple value of XList that only stores values
data SymId :: * ~> *
type instance Apply SymId x = x
type List = XList SymId

-- Ordering for Sparse Tensor
deriving instance (forall x. Eq (tc x)) => Eq (TList tc ix)
deriving instance (forall x. Ord (tc x)) => Ord (TList tc ix)
deriving instance (forall x. Show (tc x)) => Show (TList tc ix)


-- | The class of singleton kinds. If @k@ is an instance, then @k@ should have an associated singleton.
class SingKind k where
    type Demote k = (r :: *) | r -> k

    fromSing :: Sing (a :: k) -> Demote k 

instance Eq (XList f '[]) where
    XNil == XNil = True

deriving instance (Eq (Apply f x), Eq (XList f xs)) => Eq (XList f (x ': xs))

instance Show (XList f '[]) where
    show XNil = "XNil"

deriving instance (Show (Apply f x), Show (XList f xs)) => Show (XList f (x ': xs))

-- | The element containment type family for lists
type family Elem (x :: k) (xs :: [k]) :: Bool where
    Elem x '[]      = 'False
    Elem x (x ': _) = 'True
    Elem x (y ': v) = Elem x v

-- | This class associates singleton values to type-level values, allowing for implicit value passing.
class Known s where
    auto :: Sing s

instance Known '[] where
    auto = XNil

instance (Known s, Known ss) => Known (s ': ss) where
    auto = XCons auto auto
