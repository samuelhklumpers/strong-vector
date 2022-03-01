{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE TypeApplications, StandaloneDeriving, TypeOperators, FlexibleContexts, FlexibleInstances, DataKinds, DeriveGeneric #-}

module Main where

import Vectors
import Naturals

import Test.Hspec
import Test.QuickCheck
import Test.QuickCheck.Classes.Base
import Data.Proxy (Proxy (Proxy))
import Data.Foldable (traverse_)


instance Arbitrary (Vec 'Z a) where
    arbitrary = pure VN

instance (Arbitrary a, Arbitrary (Vec n a)) => Arbitrary (Vec ('S n) a) where
    arbitrary = VC <$> arbitrary <*> arbitrary


type N0 = 'Z
type N1 = 'S N0
type N2 = 'S N1
type N4 = N2 + N2
type Vec4 = Vec N4

propertyTestLaws :: Laws -> SpecWith ()
propertyTestLaws (Laws className properties) =
  describe className $
  traverse_ (\(name, p) -> it name (property p)) $
  properties 


main :: IO ()
main = hspec $ do
  describe "Vec" $
    propertyTestLaws (functorLaws (Proxy @Vec4)) *>
    propertyTestLaws (applicativeLaws (Proxy @Vec4)) *>
    propertyTestLaws (monadLaws (Proxy @Vec4)) *>
    propertyTestLaws (foldableLaws (Proxy @Vec4)) *>
    propertyTestLaws (traversableLaws (Proxy @Vec4))
