{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE DeriveGeneric #-}

module Main where

import Vectors
import Naturals
import SwapH

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
oneF :: Fin ('S ('S N2))
twoF :: Fin ('S ('S ('S N1)))
threeF :: Fin ('S ('S ('S ('S 'Z))))
zeroF = toFin NZ na3
oneF = toFin na1 na2
twoF = toFin na2 na1
threeF = toFin na3 NZ

enum6 :: Vec N6 (Fin N6)
enum6 = enumFin na6

f1o6 :: Fin ('S ('S N4))
f3o6 :: Fin ('S ('S ('S ('S N2))))
f1o6 = toFin na1 na4
f3o6 = toFin na3 na2

mfs :: Vec ('S ('S ('S 'Z))) (Fin ('S ('S N4)))
mfs = VC f1o6 (VC f1o6 (VC f3o6 VN))

sliceAndMaskResult :: Vec ('S ('S 'Z)) (Fin ('S ('S N4)))
sliceAndMaskResult = VC f1o6 (VC f3o6 VN)


theMask :: BVec N6 ('BCons 'False ('BCons 'True ('BCons 'False ('BCons 'True ('BCons 'False ('BCons 'False 'BNil))))))
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

sliceBuzz :: Vec (N9 .| N0) String
sliceBuzz = runST $ do
    let na15 = na1 *| naD +| na5
    let na18 = na1 *| naD +| na8
    let na30 = na3 *| naD
    let na90 = na9 *| naD

    v <- newSTRef $ show . finToInt <$> enumFin na90

    let fizz = full "F" na30
    let buzz = full "B" na18
    let fizzBuzz = full "FB" na6

    v & vSlice na0 na30 na3 na0 .:= fizz -- yeah looks just like numpy!!
    v & vSlice na0 na18 na5 na0 .:= buzz -- :(
    v & vSlice na0 na6 na15 na0 .:= fizzBuzz

    readSTRef v

maskAssignResult :: Vec N4 Int
maskAssignResult = VC 2 $ VC 3 $ VC 1 $ VC 3 VN


f0o3 = toFin na0 na2
f1o3 = toFin na1 na1
f2o3 = toFin na2 na0

theHL = HC n0 $ HC n1 $ HC n2 HN
theHL' = HC na0 $ HC na1 $ HC na2 HN

theIX = FFS (FFZ @N1)
theIX' = FFS (FFS FFZ)

fhl = HC f0o3 $ HC f1o3 $ HC f2o3 HN
fhl' = HC f0o3 $ HC f2o3 $ HC f1o3 HN

unitTests = test [
        "indexing enumFin returns the index"                 ~: get (enumFin na4) twoF ~=? twoF,
        "slicing [0..5][1:2:2] = [1,3] "                     ~: slice na1 na2 na2 na1 enum6 ~=? sliceAndMaskResult,
        "masking [0..5][F,T,F,T,F,F] = [1,3]"                ~: mask enum6 theMask ~=? sliceAndMaskResult,
        "([1,1,1,1][0] := 2)[F,T,F,T] := [3,3] == [2,3,1,3]" ~: maskAssignTest ~=? maskAssignResult,
        "[0,1,2][1] == 1 (but different)"                    ~: getH theHL theIX ~=? n1,
        "[0,1,2][1] == 1 (but different again)"              ~: getH theHL' theIX ~=? na1,
        "swap [0,1,2] 1 2 == [0,2,1]"                        ~: swapH fhl theIX theIX' ~=? fhl',
        "[0..5][[1,1,3]] == [1,1,3]"                         ~: multiGet enum6 mfs ~=? mfs
        -- "split 2 3 [0..5] = [[0..2], [3..5]]" ~: split two three enum6 ~=? undefined
    ]

main :: IO ()
main = do
    print "sliceBuzz:"
    print $ unwords $ toList sliceBuzz


    hspec $ do
        describe "unit tests" $
            fromHUnitTest unitTests

        describe "Vec" $
            propertyTestLaws (functorLaws (Proxy @Vec4)) *>
            propertyTestLaws (applicativeLaws (Proxy @Vec4)) *>
            propertyTestLaws (monadLaws (Proxy @Vec4)) *>
            propertyTestLaws (foldableLaws (Proxy @Vec4)) *>
            propertyTestLaws (traversableLaws (Proxy @Vec4))
