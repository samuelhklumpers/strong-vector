module TensorsSparse where 

import Data.Map (Map, findWithDefault, insert)
import qualified Data.Map as Map
import NaturalsBase ( Fin(..), KnownNatList(..), KnownNat, Nat, finSize, nat, N2, N3, toInt)
import SingBase
import TensorsBase (Tensor (TC), tabulateTN, getT)
import Vectors (enumFin, toList)

data Map' ix a = Map (TList Fin ix) a
data STensor ix a = STensor a (Map (TList Fin ix) a)

getST :: STensor ix a -> TList Fin ix -> a
getST (STensor sV m) ix = findWithDefault sV ix m

putST :: Eq a => STensor ix a -> TList Fin ix -> a -> STensor ix a
putST sT@(STensor sV m) ix v | sV == v   = sT
                             | otherwise = STensor sV $ insert ix v m

modifyST :: Eq a => STensor ix a -> TList Fin ix -> (a -> a) -> STensor ix a
modifyST sT@(STensor sV m) ix f | sV == newV = STensor sV $ Map.delete ix m
                                | otherwise  = putST sT ix newV
                            where newV = f $ getST sT ix

instance Functor (STensor n) where
    fmap f (STensor sV m) = STensor (f sV) (fmap f m) 

sparsifyT :: Eq a => STensor ix a -> STensor ix a
sparsifyT (STensor sV d) = STensor sV (Map.filter (/= sV) d)

fromSparseT :: KnownNatList ix => STensor ix a -> Tensor ix a
fromSparseT sTensor = tabulateTN nats $ getST sTensor

toSparseT :: forall a ix . (KnownNatList ix, Eq a) => a -> Tensor ix a -> STensor ix a
toSparseT sparseVal t = sparsifyT $ STensor sparseVal $ tabulateDict nats $ getT t

tabulateDict :: TList Nat ix -> (TList Fin ix -> a) -> Map (TList Fin ix) a
tabulateDict ns f = fmap f (Map.fromList $ [(x, x) | x <- enumList ns])

enumList :: TList Nat ix -> [TList Fin ix]
enumList XNil         = [XNil]
enumList (XCons n ns) = concatMap ((`fmap` enumList ns) . XCons) (enumFin n)

-- note; m x n matrix is n : m : [] since m : [] is column vector
type SMat m n a = STensor (n ': m ': '[]) a
type MapMat m n a = Map (TList Fin (n ': m ': '[])) a

matMult :: forall m n p. (KnownNat n, KnownNat p) => SMat m n Int -> SMat n p Int -> SMat m p Int
matMult (STensor sV mnMap) np = STensor sV newDict
        where dictIgnoreSparse :: MapMat m p (Int, Int)
              dictIgnoreSparse = foldr (combine np) Map.empty (Map.toList mnMap)
              n = toInt (nat :: Nat n)
              newDict :: MapMat m p Int
              newDict = fmap (\(v, count) -> v + (n - count) * sV * sV) dictIgnoreSparse

-- TODO: There are examples of matrices B that have values that get multiplied by values in A that are represented by the sparse value. We need to add those still...

combine :: (KnownNat p) => SMat n p Int -> (TList Fin (n ': m ': '[]), Int) -> MapMat m p (Int, Int) -> MapMat m p (Int, Int)
combine np (XCons j (XCons i XNil), val) = Map.unionWith tuplePlus (someFunc nat i j val np)
    where tuplePlus (a,b) (c,d) = (a + c, b + d)

-- i, j is index in mn matrix. 
-- For k in 1..p:
--  let b = (j, k) in np
--  add val * b to (i, k) in output. So output is just fromList $ [((i, k), val * b)]
-- something like
someFunc :: Nat p -> Fin m -> Fin n -> Int -> SMat n p Int -> MapMat m p (Int, Int)
someFunc p i j val np = Map.fromList $ [(getIndex k, (getValue k, 1)) | k <- toList $ enumFin p] 
    where getIndex k = XCons k (XCons i XNil)  -- k i => (i, k)
          getValue k = val * getST np (XCons k (XCons j XNil))

-- 2x3 matrix
twoByThree :: SMat N2 N3 Int
twoByThree = STensor 3 (Map.fromList $ [(XCons FZ (XCons FZ XNil), 1), (XCons (FS $ FS FZ) (XCons (FS FZ) XNil), 6), (XCons (FS $ FS FZ) (XCons FZ XNil), 4)])

threeByTwo :: SMat N3 N2 Int
threeByTwo = STensor 3 $ Map.fromList $ [(XCons FZ (XCons (FS $ FS FZ) XNil), 8), (XCons (FS FZ) (XCons (FS $ FS FZ) XNil), 3)]