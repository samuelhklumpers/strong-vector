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
exampleSparse2 = (2, fromList [(FS FZ, 5), (FS $ FS FZ, 6)])

-- | Return the value at index n if it exists. Otherwise return the default sparse value.
getS :: SVec n a -> Fin n -> a
getS (sV, m) n = fromMaybe sV $ Data.Map.lookup n m

-- | Insert (overwrite) a value at an index if it is not the default value.
putS :: SVec ('S n) a -> Fin ('S n) -> a -> SVec ('S n) a
putS (sV, m) n v | sV == v   = (sV, m)
                 | otherwise = (sV, insert n v m)

-- | supply generateN with getS to generate the vector
fromSparse :: KnownNat n => SVec n a -> Vec n a
fromSparse sVec = generateN nat $ getS sVec

-- | Given a vector and sparse value, produce a sparse vector
toSparse :: Eq a => Vec n a -> a -> SVec ('S n) a
toSparse v sV = go v sV FZ
       where go :: Eq a => Vec n a -> a -> Fin ('S n) -> SVec ('S n) a
             go VN sV i                   = (sV, empty)
             go (VC x v') sV i | x == sV   = svec
                               | otherwise = putS svec i x
                where svec :: SVec n a
                      svec = unsafeCoerce $ go v' sV (FS i)