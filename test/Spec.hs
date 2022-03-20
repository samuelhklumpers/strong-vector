{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE DeriveGeneric #-}

module Main where

import Vectors
import Tensors
import Naturals
import SingBase

import Test.Hspec
import Test.HUnit
import Test.Hspec.Contrib.HUnit
import Test.QuickCheck
import Test.QuickCheck.Classes.Base
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


theMask :: SList '[ 'False, 'True, 'False, 'True, 'False, 'False ]
theMask = XCons BF $ XCons BT $ XCons BF $ XCons BT $ XCons BF $ XCons BF XNil

propertyTestLaws :: Laws -> SpecWith ()
propertyTestLaws (Laws className properties) =
  describe className $
  traverse_ (\(name, p) -> it name (property p)) $
  properties



maskAssignTest :: Vec N4 Int
maskAssignTest = runST $ do
    v <- newSTRef $ full (1 :: Int) (nat :: Nat N4)

    let w = full (3 :: Int) (nat :: Nat N2)
    let m = XCons BF $ XCons BT $ XCons BF $ XCons BT XNil

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


transposeTest :: Tensor '[N4, N3, N2] Int
transposeTest = runST $ do
    let x1 = (+1) . finToInt <$> enumFin na2
    let x2 = finToInt <$> enumFin na4
    let x3 = (+1) . finToInt <$> enumFin na3

    let v1 = fmap (\n -> fromIntegral n * x2) x1
    let v2 = fmap (fmap (\n -> fromIntegral n * x3)) v1

    let t1' = fmap (fmap (fmap TZ)) v2
    let t2' = fmap (fmap TC) t1'
    let t3' = fmap TC t2'
    let t4 = TC t3'

    let tt1 = transpose' na0 na2 t4
    let tt2 = transpose' na0 na1 tt1

    return tt2

maskAssignResult :: Vec N4 Int
maskAssignResult = VC 2 $ VC 3 $ VC 1 $ VC 3 VN

f0o3 :: Fin N3
f1o3 :: Fin N3
f2o3 :: Fin N3
f0o3 = toFin na0 na2
f1o3 = toFin na1 na1
f2o3 = toFin na2 na0

{-
theHL :: HList '[N, N, N]
theHL = XCons n0 $ XCons n1 $ XCons n2 HN
theHL' :: HList '[Nat N0, Nat N1, Nat N2]
theHL' = XCons na0 $ XCons na1 $ XCons na2 HN

theIX :: FFin ('S ('S N1)) ('UpF '( '(), 'InF '()))
theIX = FFS (FFZ @N1)

theIX' :: FFin ('S ('S ('S n))) ('UpF '( '(), 'UpF '( '(), 'InF '())))
theIX' = FFS (FFS FFZ)
-}

fhl :: TList Fin '[N3, N3, N3]
fhl = XCons f0o3 $ XCons f1o3 $ XCons f2o3 XNil
fhl' :: TList Fin '[N3, N3, N3]
fhl' = XCons f0o3 $ XCons f2o3 $ XCons f1o3 XNil

vec2 :: Int -> Int -> Vec N2 Int
vec2 a b = VC a (VC b VN)

myTensor11 :: Tensor (N1 ': N1 ': '[]) Int -- 1x1 tensor equals 1x1 matrix
myTensor11 = TC $ VC (TC $ VC (TZ 5) VN) VN

myTensor2 :: Tensor (N2 ': '[]) Int  -- 2 tensor equals 2-vector
myTensor2 = TC $ fmap TZ (vec2 5 8)

myTensor22 :: Tensor (N2 ': N2 ': '[]) Int  -- 2x2 tensor
myTensor22 = TC $ fmap TC $ VC (fmap TZ (vec2 1 2)) (VC (fmap TZ (vec2 3 4)) VN)

myTensor12 :: Tensor (N1 ': N2 ': '[]) Int
myTensor12 = TC (VC (TC (VC (TZ 0) (VC (TZ 1) VN))) VN)

myTensor21 :: Tensor (N2 ': N1 ': '[]) Int
myTensor21 = TC (VC (TC (VC (TZ 0) VN)) (VC (TC (VC (TZ 1) VN)) VN))

myTranspose21 :: Tensor (N2 ': N1 ': '[]) Int
myTranspose21 = transpose na0 na1 myTensor12

unitTests :: Test
unitTests = test [
        "indexing enumFin returns the index"                 ~: get (enumFin na4) twoF ~=? twoF,
        "slicing [0..5][1:2:2] = [1,3] "                     ~: slice na1 na2 na2 na1 enum6 ~=? sliceAndMaskResult,
        "masking [0..5][F,T,F,T,F,F] = [1,3]"                ~: mask enum6 theMask ~=? sliceAndMaskResult,
        "([1,1,1,1][0] := 2)[F,T,F,T] := [3,3] == [2,3,1,3]" ~: maskAssignTest ~=? maskAssignResult,
        "transp 0 1 [[0, 1]] == [[0], [1]]"                  ~: myTranspose21 ~=? myTensor21,
        --"[0,1,2][1] == 1 (but different)"                    ~: getH theHL theIX ~=? n1,
        --"[0,1,2][1] == 1 (but different again)"              ~: getH theHL' theIX ~=? na1,
        --"swap [0,1,2] 1 2 == [0,2,1]"                        ~: swapH fhl theIX theIX' ~=? fhl',
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
