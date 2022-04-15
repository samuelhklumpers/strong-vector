module VectorsSing where

import VectorsBase
import SingBase
import Naturals


-- | Dependent vector type, equivalent to @XList@, but carries its kind variables in @Vec@
data XVec :: forall n k. (k ~> *) -> Vec n k -> * where
    XN  :: XVec f 'VN
    XC  :: Apply f x -> XVec f xs -> XVec f ('VC x xs)

type SVec = XVec SingSym
type TVec tc = XVec (TyCon tc)
 
type instance Sing x = SVec x

instance Known 'VN where
    auto = XN

instance (Known s, Known ss) => Known ('VC s ss) where
    auto = XC auto auto

-- | Convert from the list to the vector kind
type family ToVec (xs :: [k]) :: Vec (Length xs) k where
    ToVec '[] = 'VN
    ToVec (x ': xs) = 'VC x (ToVec xs)

-- | Convert from the vector to the list kind
type family FromVec (xs :: Vec n k) :: [k] where
    FromVec 'VN        = '[] 
    FromVec ('VC x xs) = x ': FromVec xs

-- | Convert an @XList@ to an @XVec@
toXVec :: XList f xs -> XVec f (ToVec xs)
toXVec XNil         = XN
toXVec (XCons x xs) = XC x $ toXVec xs
