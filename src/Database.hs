{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE IncoherentInstances #-} -- only used for show instances

module Database where
import Vectors hiding ((++))
import NaturalsBase
import SingBase
import Tensors
import Naturals (Length)

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

data Table c r = Table (TList STRING c) (Tensor (Length c ': r ': '[]) String) deriving (Show)

instance Show (STRING s) where
    show XNil                    = ""
    show (XCons c cs)            = show c ++ show cs

instance Show (TList STRING h) where
    show XNil                      = ""
    show (XCons XNil xs)           = show " - " ++ show xs
    show (XCons (XCons c cs) XNil) = show c ++ show cs
    show (XCons (XCons c cs) xs)   = show c ++ show cs ++ ":" ++ show xs

newRow :: Tensor ( N2 ': '[]) String
newRow = TC (VC (TZ "1") (VC (TZ "2") VN))

insertRow :: Tensor (Length c ': '[]) String -> Table c r ->  Table c ('S r)
insertRow (TC _) (Table h (TC xs)) = Table h (TC (fmap (addToFront "hoi") xs))

addCol :: STRING s -> Tensor (r ': '[]) String -> Table c r ->  Table (s ': c) r
addCol newHeader ts (Table h (TC xs)) = Table newHeaders (TC (VC ts xs))
    where newHeaders = XCons newHeader h

addToFront :: String -> Tensor (m ': '[]) String -> Tensor ('S m ': '[]) String
addToFront s (TC VN)         = TC (VC (TZ s) VN)
addToFront s (TC (VC t ts)) = TC (VC (TZ s) (VC t ts))

ca :: STRING ( 'CC ': 'CA ': '[])
ca = XCons SCC $ XCons SCA XNil

bb :: STRING ( 'CB ': 'CB ': '[])
bb = XCons SCB $ XCons SCB XNil

header :: TList STRING (('CC ': 'CA ': '[]) ':  ('CB ': 'CB ': '[]) ': '[])
header = XCons ca $ XCons bb XNil

body :: Tensor (N2 ': N2 ': '[]) String
body = TC (VC (TC (VC (TZ "a") (VC (TZ "b") VN))) (VC (TC (VC (TZ "c") (VC (TZ "d") VN))) VN))

table22 :: Table '[ '[ 'CC, 'CA], '[ 'CB, 'CB]] N2
table22 = Table header body
