{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Recursion schemes for @N@-indexed recursive types
module Recursion where

import Vectors
import SingBase
import Naturals
import Data.Proxy
import GHC.Exts (Any)
    

-- * Types

-- | Constant depth rose tree type
data NRose n a where
    Node :: a -> [NRose (Pred n) a] -> NRose n a

data NRoseF n a b where
    NodeF :: a -> [b] -> NRoseF n a b

-- | Base/pattern functor for @Vec@
data VecF n a b where
    Nil  :: VecF 'Z a b
    Cons :: forall n a b. a -> b -> VecF ('S n) a b


-- * Families

-- | @Base t@ gets the base functor of an indexed functor
type family Base (t :: N -> * -> *) :: N -> * -> * -> *

-- | Predecessor type family
type family Pred (n :: N) :: N where
    Pred 'Z     = Any
    Pred ('S n) = n


-- * Classes

-- | An @IxRFunctor f@ is an indexed right functor, that is @f n a@ is a functor for all @n :: N@ and @a@.
class IxRFunctor f where
    rmap :: forall a b c (n :: N). (b -> c) -> f n a b -> f n a c 

-- | Class of Well Ordered recursive types, i.e.,
-- those recursive types in which all lengths of the paths to leaves are a fixed natural.
-- Most instances of @WO@ are also instances of @CoWO@, such that @project@ and @embed@ are (kind of) inverses.
class IxRFunctor (Base t) => WO t where
    -- | Roll of a single constructor.
    project :: t n a -> Base t n a (t (Pred n) a) 

-- | Class of Well Ordered corecursive types, which can be rolled up one constructor each time.
class IxRFunctor (Base t) => CoWO t where
    -- the base case is a bit icky because of the indices, unlike in recursion-schemes
    nil :: Base t 'Z a b -> t 'Z a
    -- | Roll up a single constructor.
    embed :: Base t ('S n) a (t n a) -> t ('S n) a

-- | Class of Opposite Well Ordered recursive types, i.e.,
-- those recursive types with only productive values, which can be deconstructed ad infinitum.
class IxRFunctor (Base t) => OpWO t where
    coproject :: t n a -> Base t n a (t ('S n) a)
-- ^ NB: The detail in this class might be pointless, because "streamy" types rarely admit partial functions (I think),
-- so there is no need for the index.

-- | Class of Opposite Well Ordered corecursive types.
-- I'm not sure what this means.
class IxRFunctor (Base t) => CoOpWO t where
    coembed :: Base t n a (t ('S n) a) -> t n a 


-- * Instances

instance (forall (n :: N) a. Functor (f n a)) => IxRFunctor f where
    rmap f x = fmap f x

instance Functor (VecF n a) where
    fmap _ Nil = Nil
    fmap f (Cons a b) = Cons a (f b)

instance Functor (NRoseF n a) where
    fmap f (NodeF a b) = NodeF a (fmap f b)

type instance Base Vec = VecF
type instance Base NRose = NRoseF

instance WO Vec where
    project VN        = Nil
    project (VC x xs) = Cons x xs

instance CoWO Vec where
    nil  Nil          = VN
    embed (Cons x xs) = VC x xs

instance WO NRose where
    project (Node a xs) = NodeF a xs

instance CoWO NRose where
    nil (NodeF a _)    = Node a []
    embed (NodeF a xs) = Node a xs 


-- * Functions

-- | Generalized folding function, best explained by examples
wcata :: WO t => (forall n. Base t n a b -> b) -> t m a -> b
wcata f = f . rmap (wcata f) . project

size' :: Vec n a -> Int
size' = wcata \case
    Nil       -> 0
    Cons _ xs -> 1 + xs

-- | Generalized unfolding function
wana :: CoWO t => Nat m -> (forall n. Nat n -> b -> Base t n a b) -> b -> t m a
wana NZ g     = nil . g NZ
wana (NS n) g = embed . rmap (wana n g) . g (NS n)

enumInt :: Nat n -> Vec n Int
enumInt n = wana n h 0 where
    h :: Nat m -> Int -> VecF m Int Int 
    h NZ     _ = Nil 
    h (NS _) x = Cons x (x + 1)

-- | Dependent vector fold. If @f :: N ~> *@ represents a natural index family and @v :: Vec n a@, then folding @dfold@ applies the folding function @n@ times,
-- resulting in a value of the type @f@ applied to @n@.
dfold :: Proxy f -> (forall k. Nat k -> a -> Apply f k -> Apply f ('S k)) -> Vec n a -> Apply f N0 -> Apply f n
dfold _ _ VN z = z
dfold p f (VC a v) z = f (size v) a (dfold p f v z)