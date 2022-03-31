{-# LANGUAGE UndecidableInstances #-}

-- | Type level natural number arithmetic
module NaturalsFams where

import NaturalsBase

-- * Families

-- | Type-level addition
type family (n :: N) + (m :: N) :: N where
    -- no generalized injectivity annotations :(
    -- => concretely this means we have to disambiguate every function that takes some @n + m@ containing argument
    'Z + m     = m
    ('S n) + m = 'S (n + m)

-- | Type-level subtraction
type family (n :: N) - (m :: N) :: N where
    'Z - m          = 'Z
    n - 'Z          = n
    ('S n) - ('S m) = n - m

-- | Type-level multiplication
type family (n :: N) :* (m :: N) :: N where
    'Z :* m = 'Z
    -- no nested type instances without undecidable instances :(
    -- so move this somewhere else
    ('S n) :* m = m + (n :* m)

-- | Type-level digit concatentation. For example @N9 .| N1 .| N2@ can be read as the type of 912.
type family (n :: N) .| (m :: N) :: N where
    n .| m = (n :* Digit) + m

-- | Auxilliary family for type-level division
type family DivH (k :: N) (m :: N) (n :: N) (j :: N) :: N where
    -- thx agda-stdlib
    DivH k m 'Z     j      = k
    DivH k m ('S n) 'Z     = DivH ('S k) m n m
    DivH k m ('S n) ('S j) = DivH k      m n j

-- | Type-level division
type family Div (n :: N) (m :: N) :: N where
    Div n ('S m) = DivH 'Z m n m

-- | Type-level less than
type family (n :: N) <: (m :: N) :: Bool where
    n <: 'Z      = 'False
    'Z <: 'S n   = 'True
    'S n <: 'S m = n <: m

-- | The list product type family
type family Prod (ns :: [N]) :: N where
    Prod '[]       = 'S 'Z
    Prod (n ': ns) = n :* Prod ns

-- | The @'True@ counting type family
type family Count (bs :: [Bool]) :: N where
    Count '[] = 'Z
    Count ('True ': bs) = 'S (Count bs)
    Count ('False ': bs) = Count bs

-- | The list length type family
type family Length (xs :: [k]) :: N where
    Length '[]       = 'Z
    Length (_ ': xs) = 'S (Length xs)
