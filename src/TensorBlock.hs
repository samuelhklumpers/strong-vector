{-# LANGUAGE UndecidableInstances #-}
module TensorBlock where

import Naturals
import Vectors
import Tensors
import Control.Applicative
import SingBase
import Prelude hiding (splitAt, (++), zipWith)

type family NewDim (xs :: [k]) :: [[k]] where
    NewDim '[]       = '[]
    NewDim (x ': xs) = '[x] ': NewDim xs

-- | The datatype of block tensors.
-- @BZ@ states that a scalar is a 0-dimensional block
-- @BL@ states that a 0-length block is block
-- @BS@ introduces blockiness by allowing one to stack blocks
data Block bs a where
    BZ :: a -> Block '[] a
    BL :: Block ('[] ': bs) a
    BS :: Vec n (Block bs a) -> Block (ns ': bs) a -> Block ((n ': ns) ': bs) a
-- ^ Some examples are in order
-- (0)                   :: Block '[] Int
-- <0, 1, 2>             :: Block '[ '[N3]] Int
-- <0, 1 | 2 | 3, 4, 5 > :: Block '[ '[N2, N1, N3]] Int
--
-- ----------- :: Block '[ '[N3, N1, N2], '[N2, N1]] Int
-- <0, 1 | 6 >
-- <2, 3 | 7 >
-- <4, 5 | 8 >
-- -----------
-- <0, 1 | 2 >
-- -----------
-- <9, 0 | 1 >
-- <2, 3 | 4 >
-- -----------

-- | Concatenate a vector of blocks into a larger block
bConcat :: Vec n (Block bs a) -> Block ('[n] ': bs) a
bConcat v = BS v BL

instance Functor (Block bs) where
    fmap f (BZ a) = BZ (f a)
    fmap _ BL = BL
    fmap f (BS b bs) = BS (fmap (fmap f) b) (fmap f bs)

instance Known bs => Applicative (Block bs) where
    pure x = fullB x auto
    liftA2 = zipWithB

-- | @full x n@ returns a block of shape @bs@ of copies of @x@
fullB :: a -> SList bs -> Block bs a
fullB a XNil                    = BZ a
fullB _ (XCons XNil _)          = BL
fullB a (XCons (XCons n ns) bs) = BS (full (fullB a bs) n) (fullB a (XCons ns bs))

-- | Zip two blocks with a binary operation
zipWithB :: (a -> b -> c) -> Block bs a -> Block bs b -> Block bs c
zipWithB f (BZ a) (BZ b) = BZ (f a b)
zipWithB _ BL _ = BL
zipWithB f (BS as ass) (BS bs bss) = BS (zipWith (zipWithB f) as bs) (zipWithB f ass bss)

-- | Convert a tensor to the trivial block tensor
tensorBlock :: Tensor ns a -> Block (NewDim ns) a
tensorBlock (TZ a) = BZ a
tensorBlock (TC v) = bConcat (fmap tensorBlock v)

type family Sum (ns :: [N]) :: N where
    Sum '[] = 'Z
    Sum (n ': ns) = n + Sum ns

type family Stacken (bs :: [[N]]) :: [N] where
    Stacken '[] = '[]
    Stacken (ns ': nss) = Sum ns ': Stacken nss

-- | Convert a block tensor to a tensor, forgetting blockiness
blockTensor :: Block bs a -> Tensor (Stacken bs) a
blockTensor (BZ a) = TZ a
blockTensor BL = TC VN
blockTensor (BS b bs) = case blockTensor bs of
    TC vs -> TC (fmap blockTensor b ++ vs)

{-
enBlock :: SList bs -> Tensor (Stacken bs) a -> Block bs a
enBlock XNil (TZ a) = BZ a
enBlock (XCons XNil _) _ = BL
enBlock (XCons (XCons n ns) nss) (TC ts) = BS (enBlock nss h) (enBlock (XCons ns nss) ts') where
    (h, ts') = splitAt n ts

join :: Block bs (Block bs a) -> Block bs a
join = _ -- use blockTensor and enBlock

instance Known bs => Monad (Block bs) where
    --
-}
