{-# LANGUAGE TypeFamilies          #-}

module Database where
import Vectors
import NaturalsBase
import SingBase
import Tensors

-- data STRING = CEND | CA STRING | CB STRING | CC STRING deriving (Eq, Show)

data C = CA | CB | CC deriving (Eq, Show)

data Character c where
    SCA :: Character 'CA
    SCB :: Character 'CB
    SCC :: Character 'CC

instance Show (Character c) where
    show SCA = "a"
    show SCB = "b"
    show SCC = "c"

type STRING = TList Character

data Table n m r = Table (Vec n String) (Tensor (m ': r ': '[]) String) deriving (Show)

table22 :: Table N2 N2 N2
table22 = Table header body

header :: Vec N2 String
header = VC "col1" $ VC "col2" VN

body :: Tensor (N2 ': N2 ': '[]) String
body = TC (VC (TC (VC (TZ "a") (VC (TZ "b") VN))) (VC (TC (VC (TZ "c") (VC (TZ "d") VN))) VN))

newRow :: Tensor ( N2 ': '[]) [Char]
newRow = TC (VC (TZ "1") (VC (TZ "2") VN))

addRow :: Tensor (m ': '[]) String -> Table n m r ->  Table n m ('S r)
addRow (TC _) (Table h (TC xs)) = Table h (TC (fmap (addToFront "hoi") xs))

addCol :: String -> Tensor (r ': '[]) String -> Table n m r ->  Table ('S n) ('S m) r
addCol newHeader ts (Table h (TC xs)) = Table newHeaders (TC (VC ts xs))
    where newHeaders = VC newHeader h

addToFront :: String -> Tensor (m ': '[]) String -> Tensor ('S m ': '[]) String
addToFront s (TC VN)         = TC (VC (TZ s) VN)
addToFront s (TC (VC t ts)) = TC (VC (TZ s) (VC t ts))
