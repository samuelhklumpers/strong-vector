{-# LANGUAGE DataKinds, PolyKinds, TypeFamilies, GADTs, ScopedTypeVariables, UndecidableInstances, FlexibleInstances, TypeOperators, FlexibleContexts, ConstraintKinds, MultiParamTypeClasses, PatternSynonyms #-}







module Main where

data N = Z | S N

data Nat n where
    NZ :: Nat 'Z
    NS :: Nat n -> Nat ('S n)

class Hole x where
    tact :: x

data Fin n where
    FZ :: Nat ('S n) -> Fin ('S n)
    FS :: Nat ('S n) -> Fin ('S n) -> Fin ('S ('S n))

data Vec a n where
    VN :: Nat n -> Vec a 'Z
    VC :: Nat ('S n) -> a -> Vec a n -> Vec a ('S n)

--pattern FZ' <- FZ _
--pattern FS' f <- FS _ f

pattern VN' :: Vec a 'Z
pattern VN' <- VN NZ where
    VN' = VN NZ

--pattern VC' x v <- VC (NS n) x v

type family (n :: N) + (m :: N) :: N
type instance 'Z + m     = m
type instance ('S n) + m = 'S (n + m)

instance Show (Nat n) where
    show n = "Nat " ++ show (toInt n)

toInt :: Nat n -> Int
toInt NZ = 0
toInt (NS n) = 1 + toInt n

fromFin :: Fin n -> Nat n
fromFin (FZ n)   = n
fromFin (FS n _) = NS n

finToTup :: Fin ('S n) -> (Int, Int)
finToTup f@(FZ _)  = (0, toInt $ fromFin f)
finToTup (FS _ f) = (x + 1, y + 1) where
    (x, y) = finToTup f

instance Show (Fin ('S n)) where
    show f = "Fin " ++ show x ++ "/" ++ show y where
        (x, y) = finToTup f

full :: a -> Nat n -> Vec a n
full _ NZ     = VN'
full a (NS n) = VC (NS n) a (full a n)

vZip :: (a -> b -> c) -> Vec a n -> Vec b n -> Vec c n
vZip _ (VN _) (VN _) = VN'
vZip f (VC n a vec) (VC _ b vec') = VC n (f a b) (vZip f vec vec')

vFold :: (a -> b -> a) -> a -> Vec b n -> a
vFold _ x (VN _) = x
vFold f x (VC _ b vec) = f (vFold f x vec) b

vMap :: (a -> b) -> Vec a n -> Vec b n
vMap _ (VN _)     = VN'
vMap f (VC n x v) = VC n (f x) (vMap f v)

{-
vConc :: Vec a n -> Vec a m -> Vec a (n + m)
vConc (VN _) w     = w
vConc (VC (NS n) x v) w = VC _ x (vConc v w)
-}

vLen :: Vec a n -> Nat n
vLen (VN _) = NZ
vLen (VC n _ _) = n

enumF :: Nat n -> Vec (Fin n) n
enumF NZ     = VN'
enumF (NS NZ) = VC (NS NZ) (FZ (NS NZ)) VN'
enumF (NS (NS n)) = VC (NS (NS n)) (FZ (NS (NS n))) (vMap (FS (NS n)) (enumF (NS n)))

vSum :: Num a => Vec a n -> a
vSum = vFold (+) 0

delete :: Fin ('S n) -> Vec a ('S n) -> Vec a n
delete (FZ _) (VC _ _ v)        = v
delete (FS _ (FZ _)) (VC _ _ v) = v
delete (FS _ (FS m f)) (VC (NS n) x v) = VC n x (delete (FS m f) v)

subMatrix :: Fin ('S n) -> Fin ('S m) -> Vec (Vec a ('S m)) ('S n) -> Vec (Vec a m) n
subMatrix f g v = vMap (delete g) $ delete f v

-- | not quite the determinant, put (-1) ** x here when implemented
det :: Num a => Vec (Vec a n) n -> a
det (VN _)             = 0
det (VC (NS NZ) (VC (NS NZ) x _) _) = x
det v@VC {} = vSum $ vZip f (enumF $ vLen v) v where
    f j (VC (NS n) x _) = x * minor (FZ (NS n)) j v

minor :: Num a => Fin ('S n) -> Fin ('S n) -> Vec (Vec a ('S n)) ('S n) -> a
minor i j v = det (subMatrix i j v)


main :: IO ()
main = putStrLn "hoi"
