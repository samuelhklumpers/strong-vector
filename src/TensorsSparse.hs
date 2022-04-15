module TensorsSparse where 

import Data.Map (Map, findWithDefault, insert)
import qualified Data.Map as Map
import NaturalsBase ( Fin(..), Nat, finSize, N2, N3, toInt)
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

fromSparseT :: Known ix => STensor ix a -> Tensor ix a
fromSparseT sTensor = tabulateTN auto $ getST sTensor

toSparseT :: forall a ix . (Known ix, Eq a) => a -> Tensor ix a -> STensor ix a
toSparseT sparseVal t = sparsifyT $ STensor sparseVal $ tabulateDict auto $ getT t

tabulateDict :: SList ix -> (TList Fin ix -> a) -> Map (TList Fin ix) a
tabulateDict ns f = fmap f (Map.fromList $ [(x, x) | x <- enumList ns])

enumList :: SList ix -> [TList Fin ix]
enumList XNil         = [XNil]
enumList (XCons n ns) = concatMap ((`fmap` enumList ns) . XCons) (enumFin n)

-- note; m x n matrix is n : m : [] since m : [] is column vector
type SMat m n a = STensor (n ': m ': '[]) a
type MapMat m n a = Map (TList Fin (n ': m ': '[])) a


-- | Sparse matrix multiplication in O(|mnMap|*p + |npMap|*m), which is faster than the trivial O(mnp + m^2p) when the matrices are sparse (less than min(m,n,p) elements)
matMult :: forall m n p a. (Num a, Known m, Known n, Known p) => SMat m n a -> SMat n p a -> SMat m p a
matMult (STensor sV mnMap) np@(STensor sV2 npMap) = STensor (sV * sV2) dnew
        where -- All required products from d1 and corresponding d2 (or sparse) elements.
              d1 = foldr combineNp Map.empty (Map.toList mnMap)
              -- All remaining products from d2 and only corresponding sparse (missing) values from d2
              d2 = foldr combineMn Map.empty (Map.toList npMap)
              n = toInt (auto :: Nat n)
              -- "count" counts the number of times a value was added to that index.
              -- In normal matrix multiplication, the sum of n products are added to each index.
              -- Hence we need to add the missing products for sparse values: (n-count) * sV * sV2
              dnew = fmap (\(v, count) -> v + fromIntegral (n - count) * sV * sV2) 
                          (Map.unionWith tuplePlus d1 d2)

              combineNp :: (Num a, Known p) => (TList Fin (n ': m ': '[]), a) -> MapMat m p (a, Int) -> MapMat m p (a, Int)
              combineNp (XCons j (XCons i XNil), val) = Map.unionWith tuplePlus npProducts
                  where npProducts = Map.fromList $ [(getIndex k, (getValue k, 1)) | k <- toList $ enumFin auto] 
                        getIndex k = XCons k (XCons i XNil)  -- k i => (i, k)
                        getValue k = val * getST np (XCons k (XCons j XNil))

              -- Return 0 as second tuple element value if the product is already dealt for by combineNp
              combineMn :: (Num a, Known m) => (TList Fin (p ': n ': '[]), a) -> MapMat m p (a, Int) -> MapMat m p (a, Int)
              combineMn (XCons j (XCons i XNil), val) = Map.unionWith tuplePlus mnProducts
                  where mnProducts = Map.fromList $ [(getIndex k, getValue k) | k <- toList $ enumFin auto] 
                        getIndex k = XCons j (XCons k XNil)
                        getValue k | Map.member (XCons i (XCons k XNil)) mnMap = (0, 0)
                                   | otherwise                                 = (val * sV, 1)
                  -- i, j is index in np matrix
                  -- for k in 1..m
                  --  let b = (k, i) in mn (but skip if is in the dict. Only do if it is the sparse value)
                  --  add val * b to to (k, i) in output.



-- 2x3 matrix
twoByThree :: SMat N2 N3 Int
twoByThree = STensor 3 (Map.fromList [(XCons FZ (XCons FZ XNil), 1), (XCons (FS $ FS FZ) (XCons (FS FZ) XNil), 6), (XCons (FS FZ) (XCons (FS FZ) XNil), 4)])

threeByTwo :: SMat N3 N2 Int
threeByTwo = STensor 7 $ Map.fromList [(XCons FZ (XCons (FS $ FS FZ) XNil), 8), (XCons (FS FZ) (XCons (FS $ FS FZ) XNil), 3)]


-- 2x3 matrix
aa :: SMat N2 N3 Int
aa = STensor 3 (Map.fromList [(XCons FZ (XCons FZ XNil), 1), (XCons (FS $ FS FZ) (XCons (FS FZ) XNil), 6), (XCons (FS FZ) (XCons (FS FZ) XNil), 4)])

ab :: SMat N3 N2 Int
ab = STensor 3 $ Map.fromList [(XCons FZ (XCons (FS $ FS FZ) XNil), 8), (XCons (FS FZ) (XCons FZ XNil), 3), (XCons FZ (XCons FZ XNil), 2), (XCons FZ (XCons (FS FZ) XNil), 1)]




-- | Helper for adding two 2-tuples elementwise
tuplePlus :: (Num a, Num b) => (a, b) -> (a, b) -> (a, b)
tuplePlus (a,b) (c,d) = (a + c, b + d)