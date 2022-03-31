{-# LANGUAGE ScopedTypeVariables #-}

module VectorsSparse where

import Data.Map ( empty, fromList, lookup, toDescList, Map, toAscList, insert )
import VectorsBase
import Naturals
import NaturalsBase
import Data.Maybe
import Unsafe.Coerce (unsafeCoerce)

data SVec' n a where
    SVN :: a -> SVec' 'Z a  -- where input is sparse value
    SVC :: a -> SVec' n a -> SVec' ('S n) a -- Where a is new value, k is position

-- saved in a dictionary.
type SVec n a = (a, Map (Fin n) a)

exampleSparse :: SVec 'Z Int
exampleSparse = (3, empty)

exampleSparse2 :: SVec N4 Int
exampleSparse2 = (2, fromList [(FS FZ, 5), (FS $ FS FZ, 5)])


exampleVec3 :: Vec N4 Int
exampleVec3 = VC 2 $ VC 5 $ VC 5 $ VC 2 VN

-- | Return the value at index n if it exists. Otherwise return the default sparse value.
getS :: SVec n a -> Fin n -> a
getS (sV, m) n = fromMaybe sV $ Data.Map.lookup n m

-- | Insert (overwrite) a value at an index if it is not the default value.
putS :: Eq a => SVec n a -> Fin n -> a -> SVec n a
putS (sV, m) n v | sV == v   = (sV, m)
                 | otherwise = (sV, insert n v m)

-- | supply generateN with getS to generate the vector
fromSparse :: KnownNat n => SVec n a -> Vec n a
fromSparse sVec = generateN nat $ getS sVec

toSparse :: forall a n . (KnownNat n, Eq a) => a -> Vec n a -> SVec n a
toSparse sparseVal = go (enumFin nat)
       where go :: Eq a => Vec p (Fin n) -> Vec p a -> SVec n a
             go VN VN                                = (sparseVal, empty)
             go (VC f fs) (VC v vs) | v == sparseVal = svec
                                    | otherwise      = putS svec f v
               where svec :: Eq a => SVec n a
                     svec = go fs vs