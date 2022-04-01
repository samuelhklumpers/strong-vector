{-# LANGUAGE AllowAmbiguousTypes #-}

module Database where
import Vectors
import NaturalsBase
import SingBase

import Control.Lens
import Control.Monad.ST

import Data.Constraint

import Data.STRef


import Naturals
import VectorsBase
import Tensors

import NaturalsFams (Length)

data STRING = CZ | CA STRING | CB STRING | CC STRING deriving (Eq, Show)
-- Note that -XDataKinds lifts @N@ to a kind, and @Z@ and @S@ to type constructors

-- | The singleton type for string.
data STIN c where
    SCZ :: STIN 'CZ
    SCA :: STIN c -> STIN ('CA c)
    SCB :: STIN c -> STIN ('CB c)
    SCC :: STIN c -> STIN ('CC c)

data MyList a = MNil | MCons Bool (MyList a)

abc :: STIN ('CA ('CB ('CC 'CZ)))
abc = SCA $ SCB $ SCC SCZ

aa :: STIN ('CA 'CZ)
aa = SCA SCZ

aToB :: STIN ('CA 'CZ) -> STIN ('CB 'CZ)
aToB _ = SCB SCZ

aToBTest = aToB aa




-- toStringMask :: STRING -> [STRING] -> XList 
-- toStringMask s []                 = XNil
toStringMask s []                 = MNil
toStringMask s (x:xs) | x == s    = MCons True $ toStringMask s xs
                      | otherwise = MCons False $ toStringMask s xs

-- isIt :: STRING -> STRING -> Boolean b 
isIt :: String -> String -> Bool
isIt c1 c2 | c1 == c2  = True
           | otherwise = False

-- theMask2 :: SList '[ 'False, 'True, 'False, 'True]

-- | The @'STRING@ counting type family
-- type family Count (bs :: [STRING]) :: N where
--     Count '[] = 'Z
--     Count ('True ': bs) = 'S (Count bs)
--     Count ('False ': bs) = Count bs

type family Countt (s :: STRING) (bs :: [STRING]) :: N where
    Countt _ '[]                 = 'Z
    Countt (c ss) (c _ ': xs)    = 'S (Countt (CA ss) xs)
    Countt (_ ss) ('CA _ ': xs)  = (Countt (CA ss) xs)
    Countt s (_ ': xs)           = (Countt s xs)


type instance Sing = STIN


mask2 :: Vec (Length bs) a -> SList bs -> Vec (Countt (CA CZ) bs) a
mask2 VN XNil = VN
mask2 (VC a v) (XCons (SCA _) bv) = VC a (mask2 v bv)
mask2 (VC _ v) (XCons (SCB _) bv) = mask2 v bv
mask2 (VC _ v) (XCons (SCC _) bv) = mask2 v bv
mask2 (VC _ v) (XCons SCZ bv)     = mask2 v bv


caa :: Vec('S ('S 'Z)) STRING
caa = VC (CA CZ) $ VC (CA $ CB CZ) VN

demo = mask2 caa theMask

-- theMask :: SList '[ 'CA, 'CB ]
-- theMask :: SList '[ 'CA 'CZ, 'CZ]
theMask = XCons (SCA SCZ) $ XCons SCZ XNil


theMask2 :: SList '[ 'False]
theMask2 = XCons BF XNil


instance SingKind STRING where
    type Demote STRING = STRING
    fromSing (SCA s) = CA (fromSing s)
    fromSing (SCB s) = CB (fromSing s)
    fromSing (SCC s) = CC (fromSing s)
    fromSing SCZ     = CZ