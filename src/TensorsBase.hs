{-# LANGUAGE UndecidableInstances #-}
-- | Tensors and basic operations
module TensorsBase where

import Data.Distributive
import Data.Functor.Rep
import GHC.Base hiding (Nat, TyCon)

import Naturals
import VectorsBase hiding ((++))
import SingBase
import Data.Proxy (Proxy (Proxy))
import Unsafe.Coerce (unsafeCoerce)
import Prelude hiding (zipWith)


-- | The type for tensors with known dimensions.
-- NB: the constructor @TZ a@ represents the fact that the 0-tensor has 1 element,
-- since a tensor with dimensions @ns@ has @prod ns@ elements, and the nullary product is 1.
data Tensor ix a where
    TZ :: a -> Tensor '[] a
    TC :: Vec n (Tensor ix a) -> Tensor (n ': ix) a

deriving instance Eq a => Eq (Tensor ix a)

type family Append (xs :: [k]) (x :: k) :: [k] where
    Append '[]       x = x ': '[]
    Append (x ': xs) y = x ': Append xs y

showT :: Show a => Nat (Length ix) -> Tensor ix a -> String
showT _ (TZ a) = show a -- :))
showT d@(NS d') (TC v) = let v' = fmap (showT d') v in
    if toInt d <= 1 then
        "<" ++ unwords (toList v') ++ ">"
    else
        "<" ++ unlines (toList v') ++ ">"

instance (Show a, Known (Length ix)) => Show (Tensor ix a) where
    show = showT auto

instance Functor (Tensor ix) where
    fmap f (TZ a) = TZ (f a)
    fmap f (TC vs) = TC (fmap (fmap f) vs)

instance Functor (Tensor2 ix) where
    fmap f (TZ2 a) = TZ2 (f a)
    fmap f (TC2 vs) = TC2 (fmap (fmap f) vs)

instance Known ix => Applicative (Tensor ix) where
    pure = pureRep
    liftA2 = zipWithT

instance Foldable (Tensor ix) where
  foldMap f (TZ a) = f a
  foldMap f (TC v) = foldMap (foldMap f) v

zipWithT :: (a -> b -> c) -> Tensor ns a -> Tensor ns b -> Tensor ns c
zipWithT f (TZ a) (TZ b) = TZ (f a b)
zipWithT f (TC v) (TC w) = TC $ zipWith (zipWithT f) v w

instance Known ix => Distributive (Tensor ix) where
    distribute = distributeRep

instance Known ix => Representable (Tensor ix) where
    type Rep (Tensor ix) = TList Fin ix

    tabulate = tabulateT
    index = getT

-- | Index a tensor with a list of indices
getT :: Tensor ix a -> TList Fin ix -> a
getT (TZ a)  XNil         = a
getT (TC vs) (XCons i ix) = getT (get vs i) ix

getT2 :: Tensor2 ix a -> TVec Fin ix -> a
getT2 (TZ2 a)  XN         = a
getT2 (TC2 vs) (XC i ix) = getT2 (get vs i) ix

-- | Create a tensor from a generating function, provided the resulting dimensions are known
tabulateT :: Known ix => (TList Fin ix -> a) -> Tensor ix a
tabulateT = tabulateTN auto

tabulateTN2 :: SVec ix -> (TVec Fin ix -> a) -> Tensor2 ix a
tabulateTN2 ns f = fmap f (enumT2 ns)

tabulateT2 :: Known ix => (TVec Fin ix -> a) -> Tensor2 ix a
tabulateT2 = tabulateTN2 auto

-- | Generalization of @curry@ to @XList@.
-- Converts a @(n+1)@-ary list function into a function taking one value which returns a @n@-ary list function.
xCurry :: (XList f (x ': xs) -> a) -> Apply f x -> XList f xs -> a
xCurry f x xs = f (XCons x xs)

-- | Create a tensor from a generating function, given the dimensions
tabulateTN :: SList ix -> (TList Fin ix -> a) -> Tensor ix a
tabulateTN ns f = fmap f (enumT ns)
--tabulateTN XNil f = TZ (f XNil)
--tabulateTN (XCons n ns) f = TC $ fmap (tabulateTN ns) (generateN n (xCurry f))


-- | List indexing type family. Is @Any@ when @i@ is invalid.
type family Get (xs :: Vec n k) (i :: Fin n) :: k where
    Get ('VC x _)  'FZ     = x
    Get ('VC _ xs) ('FS i) = Get xs i

-- | List updating type family. Is @Any@ when @i@ is invalid.
type family Put (xs :: Vec n k) (i :: Fin n) (x :: k) :: Vec n k where
    Put ('VC _ xs) 'FZ x     = 'VC x xs
    Put ('VC x xs) ('FS i) y = 'VC x (Put xs i y)

-- | Swapping type family, @Swap i j xs@ is @xs@ with the elements at @i@ and @j@ swapped.
-- Is @Any@ when @i@ or @j@ is invalid.
type family Swap (i :: Fin n) (j :: Fin n) (xs :: Vec n k) :: Vec n k where
    Swap i j xs = Put (Put xs j (Get xs i)) i (Get xs j)

-- | Unsafely index an @XList@ with a @Nat@
getX :: forall f xs i. XVec f xs -> SFin (VLength xs) i -> Apply f (Get xs i)
getX (XC x _) SFZ      = x
getX (XC _ xs) (SFS i) = getX xs i


type family VLength (xs :: Vec n k) :: N where
    VLength (xs :: Vec n k) = n

putX :: Proxy x -> XVec f xs -> SFin (VLength xs) i -> Apply f x -> XVec f (Put xs i x)
putX _ (XC _ v) SFZ x     = XC x v
putX p (XC x v) (SFS i) y = XC x $ putX p v i y

-- | Typeclass encoding the result of the @Swap@ family. NB: @swap@ is unsafe.
swapX :: forall xs f i j. SFin (VLength xs) i -> SFin (VLength xs) j -> XVec f xs -> XVec f (Swap i j xs)
swapX i j xs = putX (Proxy @(Get xs j)) (putX (Proxy @(Get xs i)) xs j (getX xs i)) i (getX xs j)

-- | Axiom: @length (put xs i x) == length xs@. Is absurd when @i@ or @j@ is invalid.
lengthLemma :: forall xs x i f. Proxy f -> Proxy x -> Proxy xs -> Proxy i -> Apply f (VLength xs) -> Apply f (VLength (Put xs i x))
lengthLemma _ _ _ _ = unsafeCoerce


data Tensor2 :: forall n. Vec n N -> * -> * where
    TZ2 :: a -> Tensor2 'VN a
    TC2 :: Vec n (Tensor2 ix a) -> Tensor2 ('VC n ix) a

-- | Unsafely transpose two dimensions of a tensor, where the dimensions of the input tensor are assumed to be swapped.
transpose' :: forall ix i j a. Known ix => SFin (VLength ix) i -> SFin (VLength ix) j -> Tensor2 (Swap i j ix) a -> Tensor2 ix a
transpose' i j t = tabulateT2 $ getT2 t . swapX i j


-- | Axiom: @swap i j . swap i j == id@
swapLemma :: SFin (VLength ix) i -> SFin (VLength ix) j -> Tensor2 ix a -> Tensor2 (Swap i j (Swap i j ix)) a
swapLemma _ _ = unsafeCoerce

-- | Unsafely transpose two dimensions of a tensor, where the dimensions of the output tensor are swapped.
-- Tends to behave more nicely with respect to ambiguity.
transpose :: forall ix i j a. Known (Swap i j ix) => SFin (VLength ix) i -> SFin (VLength ix) j -> Tensor2 ix a -> Tensor2 (Swap i j ix) a
transpose i j t = transpose' i j $ swapLemma i j t

-- | Flatten a tensor into a vector.
flatten :: Tensor ix a -> Vec (Prod ix) a
flatten (TZ a) = VC a VN
flatten (TC vs) = concatenate (flatten <$> vs)

-- | Given a list of dimensions, convert a vector into a tensor with those dimensions
enshape :: Vec (Prod ix) a -> SList ix -> Tensor ix a
enshape (VC a VN) XNil = TZ a
enshape v (XCons n ns) = TC $ flip enshape ns <$> split n (prod ns) v

-- | Given a list of dimensions, reshape a tensor to those dimensions
reshape :: Prod ix ~ Prod iy => Tensor ix a -> SList iy -> Tensor iy a
reshape t = enshape (flatten t)

enumT :: SList ns -> Tensor ns (TList Fin ns)
enumT XNil         = TZ XNil
enumT (XCons n ns) = TC $ fmap (flip fmap (enumT ns) . XCons) (enumFin n)

enumT2 :: SVec ns -> Tensor2 ns (TVec Fin ns)
enumT2 XN        = TZ2 XN
enumT2 (XC n ns) = TC2 $ fmap (flip fmap (enumT2 ns) . XC) (enumFin n)

directMul :: Num a => Tensor ns a -> Tensor ns a -> Tensor ns a
directMul = zipWithT (*)

frobenius :: Num a => Tensor ns a -> Tensor ns a -> a
frobenius a b = sum $ directMul a b

squared :: Num a => Tensor ns a -> a
squared a = frobenius a a

{-
matMul :: forall n m k a. (Known n, Known m, Known k, Num a) => Tensor '[n, m] a -> Tensor '[m, k] a -> Tensor '[n, k] a
matMul (TC v) s = TC $ fmap h v where
    s' :: Tensor '[k, m] a
    s' = transpose' na0 na1 s

    s'' :: Vec k (Tensor '[m] a)
    s'' = case s' of
        TC w -> w

    h :: Tensor '[m] a -> Tensor '[k] a
    h r = TC $ fmap (TZ . frobenius r) s''
-}