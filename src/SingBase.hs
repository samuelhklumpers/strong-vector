{-# LANGUAGE UndecidableInstances #-}


module SingBase where


type family Sing :: k -> *

data TyFun :: * -> * -> *
type k1 ~> k2 = TyFun k1 k2 -> *

type family Apply (f :: k1 ~> k2) (x :: k1) :: k2


data TyCon :: (k1 -> k2) -> k1 ~> k2
type instance Apply (TyCon tc) x = tc x


data SingSym :: k ~> *
type instance Apply SingSym x = Sing x


data XList :: forall k. (k ~> *) -> [k] -> * where
    XNil   :: forall k (f :: k ~> *). XList f ('[] :: [k])
    XCons  :: forall k (f :: k ~> *) (x :: k) (xs :: [k]). Apply f (x :: k) -> XList f (xs :: [k]) -> XList f (x ': xs)

type SList = XList SingSym
type TList tc = XList (TyCon tc)

type instance Sing = SList


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
