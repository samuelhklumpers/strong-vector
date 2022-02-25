module Classes where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Relation.Binary.PropositionalEquality.Core

open ≡-Reasoning



id : ∀ {ℓ} {A : Set ℓ} → A → A
id x = x

_$_ : ∀ {ℓ} {A B : Set ℓ} → (A → B) → A → B
_$_ = id

_∘_ : ∀ {ℓ} {A B C : Set ℓ} → (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)


record Functor {ℓ} (F : Set ℓ → Set ℓ) : Set (lsuc ℓ)  where
  field
    fmap : ∀ {A B} → (A → B) → F A → F B
    
    F-id : ∀ {A} → (a : F A) → fmap id a ≡ a
    F-∘ : ∀ {A B C} → (g : B → C) (f : A → B) (a : F A) → fmap (g ∘ f) a ≡ (fmap g ∘ fmap f) a

  _<$>_ : ∀ {A B} → (A → B) → F A → F B
  _<$>_ = fmap

  infixl 20 _<$>_

open Functor {{...}} public


record Applicative (F : Set → Set) : Set₁ where
  field
    {{funF}} : Functor F

    pure : {A : Set} → A → F A
    _<*>_ : {A B : Set} → F (A → B) → F A → F B

    A-id  : ∀ {A} → (v : F A) → pure id <*> v ≡ v
    A-∘   : ∀ {A B C} → (u : F (B →  C)) (v : F (A → B)) (w : F A) → pure _∘_ <*> u <*> v <*> w ≡ u <*> (v <*> w)
    A-hom : ∀ {A B} → (f : A → B) (x : A) → pure f <*> pure x ≡ pure (f x)
    A-ic  : ∀ {A B} → (u : F (A → B)) (y : A) → u <*> pure y ≡ pure (_$ y) <*> u
    
  infixl 20 _<*>_

open Applicative {{...}} public


postulate
  -- this is from parametricity: fmap is universal w.r.t. the functor laws
  appFun : ∀ {A B F} {{aF : Applicative F}} → (f : A → B) (x : F A) → pure f <*> x ≡ fmap f x


record Monad (F : Set → Set) : Set₁ where
  field
    {{appF}} : Applicative F
    _>>=_ : ∀ {A B} → F A → (A → F B) → F B

  return : ∀ {A} → A → F A
  return = pure

  _>=>_ : {A B C : Set} → (A → F B) → (B → F C) → A → F C
  f >=> g = λ a → f a >>= g

  infixl 10 _>>=_
  infixr 10 _>=>_
  

  field
    left-1  : ∀ {A B} → (a : A) (k : A → F B) → return a >>= k ≡ k a
    right-1 : ∀ {A} → (m : F A) → m >>= return ≡ m
    assoc : ∀ {A B C D} → (f : A → F B) (g : B → F C) (h : C → F D) (a : A) → (f >=> (g >=> h)) a ≡ ((f >=> g) >=> h) a

open Monad {{...}} public
