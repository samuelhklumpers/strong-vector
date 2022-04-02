module TensorsSparse where 

import Data.Map (Map, findWithDefault, insert)
import qualified Data.Map as Map
import NaturalsBase ( Fin, KnownNatList(..), KnownNat, Nat )
import SingBase
import TensorsBase (Tensor (TC), tabulateTN, getT)

data STensor ix a = STensor a (Map (TList Fin ix) a)

getST :: STensor ix a -> TList Fin ix -> a
getST (STensor sV m) ix = findWithDefault sV ix m

putST :: Eq a => STensor ix a -> TList Fin ix -> a -> STensor ix a
putST sT@(STensor sV m) ix v | sV == v   = sT
                            | otherwise = STensor sV $ insert ix v m

instance Functor (STensor n) where
    fmap = undefined

sparsify :: Eq a => STensor ix a -> STensor ix a
sparsify (STensor sV d) = STensor sV (Map.filter (/= sV) d)

fromSparse :: KnownNatList ix => STensor ix a -> Tensor ix a
fromSparse sTensor = tabulateTN nats $ getST sTensor

-- TODO TODO
-- toSparse :: forall a ix . (KnownNatList ix, Eq a) => a -> Tensor ix a -> STensor ix a
-- toSparse sparseVal t = tabulateSTN sparseVal nats $ getT t -- TODO

-- tabulateSTN :: a -> TList Nat ix -> (TList Fin ix -> a) -> STensor ix a
-- tabulateSTN sV XNil f = undefined-- ???
-- tabulateSTN sV (XCons n ns) f = fmap (tabulateSTN sV ns) (generateN n)

-- note; m x n matrix is n : m : [] since m : [] is column vector
type SMat m n a = STensor (n ': m ': '[]) a

matMult :: (KnownNat m, KnownNat n, KnownNat p) => SMat m n a -> SMat n p a -> SMat m p a
matMult mn np = mp
        where mp = undefined