{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE TypeApplications, StandaloneDeriving, TypeOperators, FlexibleContexts, FlexibleInstances, DataKinds, DeriveGeneric #-}

module Main where

import Vectors
import Naturals

import ProductTests

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

one = NS NZ
two = one +| one
three = one +| two
four = two *| two
five = two +| three
six = two *| three

zeroF :: Fin N4
zeroF = toFin NZ three
oneF = toFin one two
twoF = toFin two one
threeF = toFin three NZ

enum6 = enumFin six

f1o6 = toFin one four
f3o6 = toFin three two

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



unitTests = test [ 
        "indexing enumFin returns the index"  ~: (get (enumFin four) twoF) ~=? twoF,
        "slicing [0..5][1:2:2] = [1,3] "      ~: slice one two two one Refl enum6 ~=? sliceAndMaskResult,
        "masking [0..5][F,T,F,T,F,F] = [1,3]" ~: mask enum6 theMask ~=? sliceAndMaskResult,
        "([1,1,1,1][0] := 2)[F,T,F,T] := [3,3] == [2,3,1,3]" ~: maskAssignTest ~=? maskAssignResult,
        -- "split 2 3 [0..5] = [[0..2], [3..5]]" ~: split two three enum6 ~=? undefined
        productTests
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
