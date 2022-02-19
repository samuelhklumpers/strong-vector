{-# LANGUAGE DataKinds, TypeFamilies, GADTs, ScopedTypeVariables, FlexibleInstances, TypeOperators, FlexibleContexts #-}

module Main where

import Data.List ( intercalate )
import Control.Applicative (liftA2)

import Naturals ( type (+), Fin(..), Nat(..), N(S, Z), Known(nat) )


data Vec n a where -- the order of the params makes Vec not a Functor oops
    VN :: Vec 'Z a
    VC ::  a -> Vec n a -> Vec ('S n) a

instance Show a => Show (Vec n a) where
    show v = "<" ++ intercalate "," (map show $ vList v) ++ ">"

instance Functor (Vec n) where
    fmap _ VN       = VN
    fmap f (VC x v) = VC (f x) (fmap f v)

instance Known n => Applicative (Vec n) where
    pure x = full x nat
    
    liftA2 _ VN VN = VN
    liftA2 f (VC a v) (VC b w) = VC (f a b) (liftA2 f v w) -- i regret everything

vList :: Vec n a -> [a]
vList = vFold (flip (:)) []

full :: a -> Nat n -> Vec n a
full _ NZ     = VN
full a (NS n) = VC a (full a n)

vFold :: (a -> b -> a) -> a -> Vec n b -> a
vFold _ x VN = x
vFold f x (VC b vec) = f (vFold f x vec) b

vConc :: Vec n a -> Vec m a -> Vec (n + m) a
vConc VN w     = w
vConc (VC x v) w = VC x (vConc v w)

vLen :: Vec n a -> Nat n
vLen VN = NZ
vLen (VC _ v) = NS (vLen v)

toFin :: Nat n -> Fin ('S n)
toFin NZ     = FI
toFin (NS n) = FZ $ toFin n

enumF :: Nat n -> Vec n (Fin n)
enumF NZ          = VN
enumF (NS NZ)     = VC FI VN
enumF (NS (NS n)) = VC (toFin $ NS n) (fmap FS (enumF (NS n)))

vSum :: Num a => Vec n a -> a
vSum = vFold (+) 0

delete :: Fin ('S n) -> Vec ('S n) a -> Vec n a
delete FI (VC _ VN)    = VN
delete (FZ _) (VC _ v) = v
delete (FS f) (VC x v) = VC x $ delete f v

subMatrix :: Fin ('S n) -> Fin ('S m) -> Vec ('S n) (Vec ('S m) a) -> Vec n (Vec m a)
subMatrix f g v = delete g <$> delete f v

det :: Num a => Vec n (Vec n a) -> a
det VN             = 0
det (VC (VC x _) VN) = x
det v@(VC _ w) = vSum $ liftA2 f (enumF $ vLen v) v where
    f j (VC x _) = (if even' j then 1 else -1) * x * minor (toFin $ vLen w) j v

    even' :: Fin n -> Bool
    even' FI     = True
    even' (FZ g) = even' g
    even' (FS g) = not $ even' g

minor :: Num a => Fin ('S n) -> Fin ('S n) -> Vec ('S n) (Vec ('S n) a) -> a
minor i j v = det (subMatrix i j v)

main :: IO ()
main = putStrLn "hoi"
