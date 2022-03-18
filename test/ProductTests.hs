module ProductTests (productTests) where

import Vectors

import Test.Hspec
import Test.HUnit
import Test.Hspec.Contrib.HUnit

vec1 = VC (VC 1 (VC 3 VN)) (VC (VC 2 (VC 4 VN)) VN)
vec2 = VC (VC 1 (VC 4 VN)) (VC (VC 2 (VC 5 VN)) (VC (VC 3 (VC 6 VN)) VN))
vec3 = VC (VC 1 (VC 4 (VC 7 VN))) (VC (VC 2 (VC 5 (VC 8 VN))) (VC (VC 3 (VC 6 (VC 9 VN))) VN))
vec4 = VC 1 (VC 3 VN)
vec5 = VC 2 (VC 4 VN)
vec6 = VC 1 (VC 2 VN)

productTests = TestLabel "Products" $ TestList [
        TestLabel "trace" $ TestList
        [
            "trace <<1,3>,<2,4>>" ~: 5 ~=? trace vec1,
            "trace <<1,4>,<2,5>,<3,6>>" ~: 6 ~=? trace vec2,
            "trace <<1,4,7>,<2,5,8>,<3,6,9>>" ~: 15 ~=? trace vec3
        ],
        TestLabel "Inner Product" $ TestList
        [
            "innerProduct <1,3>, <3,4>" ~: 14 ~=? innerProduct vec4 vec5
        ],
        TestLabel "Outer product" $ TestList
        [
            "outerProduct <1,3> <2,4>" ~: VC (VC 2 (VC 6 VN)) (VC (VC 4 (VC 12 VN)) VN) ~=? outerProduct vec4 vec5
        ]
    ]

