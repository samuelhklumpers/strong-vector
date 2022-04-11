{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Streams where

import SingBase
import Naturals

data DStream :: (N ~> *) -> N -> * where
    DNext :: Apply f n -> DStream f ('S n) -> DStream f n

type DStream' f = DStream f N0

instance (Show (Apply f n), Show (Apply f ('S n)), Show (Apply f ('S ('S n)))) => Show (DStream f n) where
    show (DNext x (DNext y (DNext z _))) = "{" ++ show x ++ "," ++ show y ++ "," ++ show z ++ ",..."


type family Id (x :: k) :: k where
    Id x = x

type family Const (x :: k1) (y :: k2) :: k1 where
    Const x _ = x

data IdSym1 :: k ~> k
type instance Apply IdSym1 x = x

data ConstSym1 :: k1 -> k2 ~> k1
type instance Apply (ConstSym1 x) _ = x

ones :: DStream (ConstSym1 Int) n
ones = DNext 1 ones

count :: Nat n -> DStream (TyCon Nat) n
count n = DNext n (count $ NS n)

count' :: DStream' (TyCon Nat)
count' = count NZ

sHead :: DStream f n -> Apply f n
sHead (DNext x _) = x

sTail :: DStream f n -> DStream f ('S n)
sTail (DNext _ xs) = xs
