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
import Test.Hspec.QuickCheck
import TensorsBase
import TensorsSparse
import DatabaseTest (dbTests)
import Recursion


instance Arbitrary (Vec 'Z a) where
    arbitrary = pure VN

instance (Arbitrary a, Arbitrary (Vec n a)) => Arbitrary (Vec ('S n) a) where
    arbitrary = VC <$> arbitrary <*> arbitrary

instance Arbitrary a => Arbitrary (Tensor '[] a) where
    arbitrary = TZ <$> arbitrary

instance Arbitrary (Vec n (Tensor ns a)) => Arbitrary (Tensor (n ': ns) a) where
    arbitrary = TC <$> arbitrary

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
  traverse_ (\(name, p) -> it name (property p))
  properties



maskAssignTest :: Vec N4 Int
maskAssignTest = runST $ do
    v <- newSTRef $ full (1 :: Int) (auto :: Nat N4)

    let w = full (3 :: Int) (auto :: Nat N2)
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


transposeTest :: Tensor2 ('VC N4 ('VC N3 ('VC N2 'VN))) Int
transposeTest = runST $ do
    let x1 = (+1) . finToInt <$> enumFin na2
    let x2 = finToInt <$> enumFin na4
    let x3 = (+1) . finToInt <$> enumFin na3

    let v1 = fmap (\n -> fromIntegral n * x2) x1
    let v2 = fmap (fmap (\n -> fromIntegral n * x3)) v1

    let t1' = fmap (fmap (fmap TZ2)) v2
    let t2' = fmap (fmap TC2) t1'
    let t3' = fmap TC2 t2'
    let t4 = TC2 t3'

    let i0 = SFZ
    let i1 = SFS SFZ
    let i2 = SFS $ SFS SFZ

    let tt1 = transpose' i0 i2 t4
    let tt2 = transpose' i0 i1 tt1

    return tt2

maskAssignResult :: Vec N4 Int
maskAssignResult = VC 2 $ VC 3 $ VC 1 $ VC 3 VN

f0o3 :: Fin N3
f1o3 :: Fin N3
f2o3 :: Fin N3
f0o3 = toFin na0 na2
f1o3 = toFin na1 na1
f2o3 = toFin na2 na0

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
myTensor22 = TC (TC <$> VC (fmap TZ (vec2 1 2)) (VC (fmap TZ (vec2 3 4)) VN))

myTensor12 :: Tensor2 ('VC N1 ('VC N2 'VN)) Int
myTensor12 = TC2 (VC (TC2 (VC (TZ2 0) (VC (TZ2 1) VN))) VN)

myTensor21 :: Tensor2 ('VC N2 ('VC N1 'VN)) Int
myTensor21 = TC2 (VC (TC2 (VC (TZ2 0) VN)) (VC (TC2 (VC (TZ2 1) VN)) VN))

myTranspose21 :: Tensor2 ('VC N2 ('VC N1 'VN)) Int
myTranspose21 = transpose SFZ (SFS SFZ) myTensor12

myReshape4 :: Tensor '[N4] Int
myReshape4 = TC $ TZ <$> VC 1 (VC 2 $ VC 3 $ VC 4 VN)

myShape22 :: SList '[ N2, N2]
myShape22 = XCons na2 $ XCons na2 XNil

data DoubleSym :: N ~> *
type instance Apply DoubleSym n = Vec (n :* N2) Int


doubleFold :: Vec N8 Int
doubleFold = dfold (Proxy @DoubleSym) h maskAssignResult VN where
    h :: Nat n -> Int -> Vec (n :* N2) Int -> Vec (N2 + (n :* N2)) Int
    h _ a v = VC a $ VC a v

doubleFoldRes :: Vec N8 Int
doubleFoldRes = VC 2 $ VC 2 $ VC 3 $ VC 3 $ VC 1 $ VC 1 $ VC 3 $ VC 3 VN

unitTests :: Test
unitTests = test [
        dbTests,
        "indexing enumFin returns the index"                 ~: get (enumFin na4) twoF ~=? twoF,
        "slicing [0..5][1:2:2] = [1,3] "                     ~: slice na1 na2 na2 na1 enum6 ~=? sliceAndMaskResult,
        "masking [0..5][F,T,F,T,F,F] = [1,3]"                ~: mask enum6 theMask ~=? sliceAndMaskResult,
        "([1,1,1,1][0] := 2)[F,T,F,T] := [3,3] == [2,3,1,3]" ~: maskAssignTest ~=? maskAssignResult,
        "transp 0 1 [[0, 1]] == [[0], [1]]"                  ~: myTranspose21 ~=? myTensor21,
        "reshape [1,2,3,4] [2,2] == [[1,2],[3,4]]"           ~: reshape myReshape4 myShape22 ~=? myTensor22,
        "flatten . reshape == flatten"                       ~: flatten (reshape myReshape4 myShape22) ~=? flatten myReshape4,
        "dfold double [2,3,1,3] == [2,2,3,3,1,1,3,3]"        ~: doubleFold ~=? doubleFoldRes,
        "[0..5][[1,1,3]] == [1,1,3]"                         ~: multiGet enum6 mfs ~=? mfs
    ]

{-
sparseMatMulTest :: Int -> Int -> Tensor '[ N2, N3] Bool -> Tensor '[ N3, N4] Bool -> Tensor '[ N2, N3] Int -> Tensor '[ N3, N4] Int -> Bool
sparseMatMulTest x y z z' a b = matMul a' b' == fromSparseT (matMult sb sa) where
    m = fmap asInt z
    m' = fmap asInt z'
    asInt :: Bool -> Int
    asInt v = if v then 1 else 0
    a' = (+x) <$> directMul m a
    b' = (+y) <$> directMul m' b
    sa = toSparseT x a'
    sb = toSparseT y b'
-}

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

        --describe "Sparse" $
        --    prop "sparseMul is matMul" sparseMatMulTest


-- demos
demoFull :: Vec N4 Int
demoFull = pure 3 

demoEnum :: Vec N4 (Fin N4)
demoEnum = enumFin auto

demoSlice :: Vec N9 Int
demoSlice = runST $ do
    v <- newSTRef (pure 0)
    let w = pure 3

    v & vSlice na1 na3 na2 na2 .:= w

    readSTRef v

demoMask :: Vec N4 Int
demoMask = runST $ do
    v <- newSTRef (pure 0)
    let w = pure 1
    let m = XCons BT $ XCons BF $ XCons BT $ XCons BF XNil

    v & vMask m .:= w

    readSTRef v

demoEnshape :: Tensor '[N3, N2] Int
demoEnshape = enshape (finToInt <$> enumFin auto) (XCons na3 $ XCons na2 XNil)

--demoTransp :: Tensor '[N2, N3] Int
--demoTransp = transpose' na0 na1 demoEnshape