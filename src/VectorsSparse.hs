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

-- saved in a dictionary.
data SVec n a = SVec a (Map (Fin n) a) deriving (Show)

-- | Return the value at index n if it exists. Otherwise return the default sparse value.
getS :: SVec n a -> Fin n -> a
getS (SVec sV m) n = findWithDefault sV n m

-- | Insert (overwrite) a value at an index if it is not the default value.
putS :: Eq a => SVec n a -> Fin n -> a -> SVec n a
putS (SVec sV m) n v | sV == v   = SVec sV m
                 | otherwise = SVec sV $ insert n v m

-- | Map a function over an SVec.
-- | Note: May cause items in the dict to be equal to the sparse value. But we cannot filter those here since fmap does not have an equality constraint.
instance Functor (SVec n) where
    fmap f (SVec sparseVal dict) = SVec (f sparseVal) (fmap f dict) 

-- | Zip two sparse vectors using a binary function by applying it to the sparse values, and zipping the dictionaries
-- | where we use the sparse value if a value is missing in the other dictionary.
zipWith :: (a -> b -> c) -> SVec n a -> SVec n b -> SVec n c
zipWith f (SVec sV1 d1) v2@(SVec sV2 d2) = SVec sV zipDicts
    where sV = f sV1 sV2
          zipDicts = inD1OrBoth `union` onlyInD2

          inD1OrBoth = mapWithKey (\k v -> f v $ getS v2 k) d1  -- Apply f to everything in d1 with corresponding value in d2
          onlyInD2 = fmap (f sV1) (difference d2 d1) -- Apply f to remaining values not in d1   

instance Applicative (SVec n) where
    pure x = SVec x empty

    liftA2 = zipWith

-- | Remove all values from the dictionary that are equal to the sparse value of the SVec
sparsify :: Eq a => SVec n a -> SVec n a
sparsify (SVec sV d) = SVec sV (Map.filter (/= sV) d)

-- | supply generateN with getS to generate the vector
fromSparse :: KnownNat n => SVec n a -> Vec n a
fromSparse sVec = generateN nat $ getS sVec

toSparse :: forall a n . (KnownNat n, Eq a) => a -> Vec n a -> SVec n a
toSparse sparseVal = go (enumFin nat)
       where go :: Eq a => Vec p (Fin n) -> Vec p a -> SVec n a
             go VN VN                                = SVec sparseVal empty
             go (VC f fs) (VC v vs) | v == sparseVal = svec
                                    | otherwise      = putS svec f v
               where svec :: Eq a => SVec n a
                     svec = go fs vs


------------------ Functions that show that sparse vectors could be useful ------------------------------
sparseVec1 :: SVec N9 Int
sparseVec1 = SVec 5 $ fromList [(FZ, 2), (FS FZ, 8)]

sparseVec2 :: SVec N9 Int
sparseVec2 = SVec 3 $ fromList [(FS FZ, 6), (FS $ FS $ FS $ FS FZ, 4)]

dot :: (Eq a, Num a) => SVec n a -> SVec n a -> SVec n a
dot v1 v2 = sparsify $ liftA2 (*) v1 v2

sparseVecDot :: SVec N9 Int
sparseVecDot = sparseVec1 `dot` sparseVec2



------------------ Some vecs to play with in GHCI -------------------

svec1 :: SVec 'Z Int
svec1 = SVec 3 empty

svec2 :: SVec N4 Int
svec2 = SVec 2 $ fromList [(FS FZ, 5), (FS $ FS FZ, 5)]

svec3 :: SVec N4 Int
svec3 = SVec 5 $ fromList [(FS FZ, 0), (FS $ FS $ FS FZ, 7)]

exampleVec3 :: Vec N4 Int
exampleVec3 = VC 2 $ VC 5 $ VC 5 $ VC 2 VN