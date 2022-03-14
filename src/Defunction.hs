module Defunction where



data TyFun :: * -> * -> *
type k1 ~> k2 = TyFun k1 k2 -> * 


type family Apply (f :: k1 ~> k2) (x :: k1) :: k2

data TyCon :: (k1 -> k2) -> k1 ~> k2
type instance Apply (TyCon tc) x = tc x


type family FMap (f :: k1 ~> k2) (xs :: [k1]) :: [k2] where
    FMap f '[] = '[]
    FMap f (x ': xs) = Apply f x ': FMap f xs

{-
sFMap :: forall (f :: * ~> *) (xs :: [*]). Proxy f -> (forall a. a -> Apply f a) -> HList xs -> HList (FMap f xs)
sFMap _ _ HN = HN
sFMap p f (HC x xs) = HC (f x) (sFMap p f xs)
-}