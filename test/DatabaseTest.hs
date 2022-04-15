module DatabaseTest (dbTests) where

import Database
import NaturalsBase
import Vectors
import Tensors
import SingBase


import Test.Hspec
import Test.HUnit

hello :: STRING ( 'CH ': 'CE ': 'CL ': 'CL ': 'CO ': '[])
hello = XCons SCH $ XCons SCE $ XCons SCL $ XCons SCL $ XCons SCO XNil

ca :: STRING ( 'CC ': 'CA ': '[])
ca = XCons SCC $ XCons SCA XNil

bb :: STRING ( 'CB ': 'CB ': '[])
bb = XCons SCB $ XCons SCB XNil

bbb :: STRING ( 'CB ': 'CB ': 'CB ': '[])
bbb = XCons SCB $ XCons SCB $ XCons SCB XNil

cc :: STRING ( 'CC ': 'CC ': '[])
cc = XCons SCC $ XCons SCC XNil

newCol :: Tensor ( N2 ': '[]) String
newCol = TC (VC (TZ "col32") (VC (TZ "col33") VN))

newRow :: Vec N2 String
newRow = VC "a" (VC "3" VN)

newRow2 :: Vec N2 String
newRow2 = VC "b" (VC "2" VN)

newRow3 :: Vec N3 String
newRow3 = VC "col31" (VC "c" (VC "1" VN))

addR  = insertRow newRow addC2
addR2 = insertRow newRow2 addR
addR3 = insertRow newRow3 addC3

addC  = insertColumn ca (TC VN) emptyTable
addC2 = insertColumn bbb (TC VN) addC
addC3 = insertColumn hello newCol addR2

-- A 3 by 2 table
table32 = insertColumn hello newCol addR2

table33 = insertRow newRow3 table32

table21 = Table headers rows
  where 
        headers = XCons header1 $ XCons header2 XNil
        rows    = TC (VC (TC (VC (TZ "a") VN)) (VC (TC (VC (TZ "c")  VN)) VN))

header1 :: Header '[ 'CB, 'CB, 'CB] ('S 'Z)
header1 = Header (NS NZ)
header2 :: Header '[ 'CC, 'CA] 'Z
header2 = Header NZ

col3 = TC (VC (TZ "col32")  (VC (TZ "col33")  VN ))
col1 = TC (VC (TZ "1")  (VC (TZ "2") (VC (TZ "3") VN )))

col11 = TC (VC (TZ "a") VN )

dbTests = TestLabel "Database" $ TestList [
        TestLabel "Select" $ TestList
        [
            "Select a column by name" ~: selectFromTable hello table32 ~=? col3,
            "Select a column by index" ~: selectByIndex NZ table33 ~=? col1
        ],
        TestLabel "Insert" $ TestList
        [
            "Insert a row, then select a column" ~: selectFromTable bbb (insertRow newRow addC2) ~=? col11,
            "Insert a column, then select that column" ~: selectFromTable hello (insertColumn hello newCol addR2) ~=? col3
        ]
    ]

