{-# LANGUAGE ScopedTypeVariables #-}

module VectorsSparse where

import Prelude hiding (zipWith)
import Data.Map ( empty, fromList, lookup, toDescList, Map, toAscList, insert, union, mapWithKey, difference, findWithDefault)
import qualified Data.Map as Map
import VectorsBase ( enumFin, generateN, Vec(..) )
import Naturals
import NaturalsBase
import Data.Maybe
import Unsafe.Coerce (unsafeCoerce)
import Control.Applicative (liftA2)

import SingBase

-- | Sparse vector represented by a sparse value and a dictionary indexed by positions in vector
data SpVec n a = SpVec a (Map (Fin n) a) deriving (Show)

-- | Sparse vectors are equal if they represent the same vector
instance (Eq a) => (Eq (SpVec n a)) where
    s1 == s2 = x1 == x2 && d1 == d2
        where (SpVec x1 d1) = sparsify s1
              (SpVec x2 d2) = sparsify s2

-- | Return the value at index n if it exists. Otherwise return the default sparse value.
getS :: SpVec n a -> Fin n -> a
getS (SpVec sV m) n = findWithDefault sV n m

-- | Insert (overwrite) a value at an index if it is not the default value.
putS :: Eq a => SpVec n a -> Fin n -> a -> SpVec n a
putS (SpVec sV m) n v | sV == v   = SpVec sV m
                 | otherwise = SpVec sV $ insert n v m

-- | Map a function over an SpVec.
-- | Note: May cause items in the dict to be equal to the sparse value. But we cannot filter those here since fmap does not have an equality constraint.
instance Functor (SpVec n) where
    fmap f (SpVec sparseVal dict) = SpVec (f sparseVal) (fmap f dict) 

-- | Zip two sparse vectors using a binary function by applying it to the sparse values, and zipping the dictionaries
-- | where we use the sparse value if a value is missing in the other dictionary.
zipWithS :: (a -> b -> c) -> SpVec n a -> SpVec n b -> SpVec n c
zipWithS f (SpVec sV1 d1) v2@(SpVec sV2 d2) = SpVec sV zipDicts
    where sV = f sV1 sV2
          zipDicts = inD1OrBoth `union` onlyInD2

          inD1OrBoth = mapWithKey (\k v -> f v $ getS v2 k) d1  -- Apply f to everything in d1 with corresponding value in d2
          onlyInD2 = fmap (f sV1) (difference d2 d1) -- Apply f to remaining values not in d1   

instance Applicative (SpVec n) where
    pure x = SpVec x empty

    liftA2 = zipWithS

-- | Remove all values from the dictionary that are equal to the sparse value of the SpVec
sparsify :: Eq a => SpVec n a -> SpVec n a
sparsify (SpVec sV d) = SpVec sV (Map.filter (/= sV) d)

-- | supply generateN with getS to generate the vector
fromSparse :: Known n => SpVec n a -> Vec n a
fromSparse sVec = generateN auto $ getS sVec

-- | Turn a regular vector into a sparse representation using a specified sparse value
toSparse :: forall a n . (Known n, Eq a) => a -> Vec n a -> SpVec n a
toSparse sparseVal = go (enumFin auto)
       where go :: Eq a => Vec p (Fin n) -> Vec p a -> SpVec n a
             go VN VN                                = SpVec sparseVal empty
             go (VC f fs) (VC v vs) | v == sparseVal = svec
                                    | otherwise      = putS svec f v
               where svec :: Eq a => SpVec n a
                     svec = go fs vs


------------------ Functions that show that sparse vectors could be useful ------------------------------

-- | Dot product between two sparse vectors
dot :: (Num a) => SpVec n a -> SpVec n a -> SpVec n a
dot = liftA2 (*)



------------------ Some vecs to play with in GHCI -------------------

sparseVec1 :: SpVec N9 Int
sparseVec1 = SpVec 5 $ fromList [(FZ, 2), (FS FZ, 8)]

sparseVec2 :: SpVec N9 Int
sparseVec2 = SpVec 3 $ fromList [(FS FZ, 6), (FS $ FS $ FS $ FS FZ, 4)]

sparseVecDotExample :: SpVec N9 Int
sparseVecDotExample = sparsify $ sparseVec1 `dot` sparseVec2

svec1 :: SpVec 'Z Int
svec1 = SpVec 3 empty

svec2 :: SpVec N4 Int
svec2 = SpVec 2 $ fromList [(FS FZ, 5), (FS $ FS FZ, 5)]

svec3 :: SpVec N4 Int
svec3 = SpVec 5 $ fromList [(FS FZ, 0), (FS $ FS $ FS FZ, 7)]

exampleVec3 :: Vec N4 Int
exampleVec3 = VC 2 $ VC 5 $ VC 5 $ VC 2 VN