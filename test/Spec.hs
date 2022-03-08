{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE TypeApplications, StandaloneDeriving, TypeOperators, FlexibleContexts, FlexibleInstances, DataKinds, DeriveGeneric #-}

module Main where

import Vectors
import Naturals

import Test.Hspec
import Test.HUnit
import Test.Hspec.Contrib.HUnit
import Test.QuickCheck
import Test.QuickCheck.Classes.Base
import Data.Type.Equality
import Data.Proxy (Proxy (Proxy))
import Data.Foldable (traverse_)
import Control.Lens
import Control.Monad.ST
import Data.STRef

instance Arbitrary (Vec 'Z a) where
    arbitrary = pure VN

instance (Arbitrary a, Arbitrary (Vec n a)) => Arbitrary (Vec ('S n) a) where
    arbitrary = VC <$> arbitrary <*> arbitrary

type Vec4 = Vec N4

zeroF :: Fin N4
zeroF = toFin NZ na3
oneF = toFin na1 na2
twoF = toFin na2 na2
threeF = toFin na3 NZ

enum6 = enumFin na6

f1o6 = toFin na1 na4
f3o6 = toFin na3 na2

sliceAndMaskResult = VC f1o6 (VC f3o6 VN)


theMask :: BVec N6 ('BCons 'F ('BCons 'T ('BCons 'F ('BCons 'T ('BCons 'F ('BCons 'F 'BNil))))))
theMask = BC BF $ BC BT $ BC BF $ BC BT $ BC BF $ BC BF BN

propertyTestLaws :: Laws -> SpecWith ()
propertyTestLaws (Laws className properties) =
  describe className $
  traverse_ (\(name, p) -> it name (property p)) $
  properties 



maskAssignTest :: Vec N4 Int
maskAssignTest = runST $ do
    v <- newSTRef $ full (1 :: Int) (nat :: Nat N4)
    
    let w = full (3 :: Int) (nat :: Nat N2)
    let m = BC BF $ BC BT $ BC BF $ BC BT BN

    v & vAt FZ  .:= 2
    v & vMask m .:= w

    readSTRef v

maskAssignResult :: Vec N4 Int
maskAssignResult = VC 2 $ VC 3 $ VC 1 $ VC 3 VN


theHL = HC n0 $ HC n1 $ HC n2 HN
theIX = FFS (FFZ @N1) 


unitTests = test [ 
        "indexing enumFin returns the index"  ~: (get (enumFin na4) twoF) ~=? twoF,
        "slicing [0..5][1:2:2] = [1,3] "      ~: slice na1 na2 na2 na1 Refl enum6 ~=? sliceAndMaskResult,
        "masking [0..5][F,T,F,T,F,F] = [1,3]" ~: mask enum6 theMask ~=? sliceAndMaskResult,
        "([1,1,1,1][0] := 2)[F,T,F,T] := [3,3] == [2,3,1,3]" ~: maskAssignTest ~=? maskAssignResult,
        "[0,1,2][1] == 1 (but different)" ~: getH theHL theIX ~=? n1
        -- "split 2 3 [0..5] = [[0..2], [3..5]]" ~: split two three enum6 ~=? undefined
    ]

main :: IO ()
main = hspec $ do
  describe "unit tests" $
    fromHUnitTest unitTests

  describe "Vec" $
    propertyTestLaws (functorLaws (Proxy @Vec4)) *>
    propertyTestLaws (applicativeLaws (Proxy @Vec4)) *>
    propertyTestLaws (monadLaws (Proxy @Vec4)) *>
    propertyTestLaws (foldableLaws (Proxy @Vec4)) *>
    propertyTestLaws (traversableLaws (Proxy @Vec4))
