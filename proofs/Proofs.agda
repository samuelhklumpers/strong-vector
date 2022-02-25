module Proofs where

open import Agda.Builtin.Equality
open import Relation.Binary.PropositionalEquality.Core
open import Data.Nat

open ≡-Reasoning

open import Classes


data Vec : ℕ → Set → Set where
  Nil  : ∀ {a} → Vec 0 a
  Cons : ∀ {n A} → (a : A) → Vec n A → Vec (suc n) A

cons-cong : ∀ {n A} {a c : A} {b d : Vec n A} → a ≡ c → b ≡ d → Cons a b ≡ Cons c d
cons-cong {_} {_} {a} {c} {b} {d} p q = begin
  Cons a b ≡⟨ cong (λ x → Cons a x) q ⟩
  Cons a d ≡⟨ cong (λ x → Cons x d) p ⟩
  Cons c d ∎

instance
  VecF : {n : ℕ} → Functor (Vec n)
  VecF = record {
    fmap = fmap' ;
    F-id = id' ;
    F-∘ = comp' }
    where
      fmap' : ∀ {n A B} → (A → B) → Vec n A → Vec n B
      fmap' f Nil = Nil
      fmap' f (Cons a v) = Cons (f a) (fmap' f v)

      id' : ∀ {n A} → (a : Vec n A) → fmap' id a ≡ a
      id' Nil = refl
      id' (Cons a v) = cong (λ w → Cons a w) (id' v)

      comp' : ∀ {n A B C} → (g : B → C) (f : A → B) (a : Vec n A) → fmap' (g ∘ f) a ≡ (fmap' g ∘ fmap' f) a
      comp' g f Nil = refl
      comp' g f (Cons a v) = cons-cong refl (comp' g f v)


full : ∀ {A} → A → (n : ℕ) → Vec n A
full x zero = Nil
full x (suc n) = Cons x (full x n)

zipWith : ∀ {n A B C} → (A → B → C) → Vec n A → Vec n B → Vec n C
zipWith _ Nil Nil = Nil
zipWith f (Cons a v) (Cons b w) = Cons (f a b) (zipWith f v w)

instance
  VecA : {n : ℕ} → Applicative (Vec n)
  VecA {n} = record
           { pure = λ x → full x n
           ; _<*>_ = ap'
           ; A-id = id'
           ; A-∘ = comp'
           ; A-hom = hom'
           ; A-ic = ic'
           }
    where
      ap' : ∀ {n A B} (v : Vec n (A → B)) (w : Vec n A) → Vec n B
      ap' Nil Nil = Nil
      ap' (Cons a v) (Cons b w) = Cons (a b) (ap' v w)
      
      id' : ∀ {n A} (v : Vec n A) → ap' (full id n) v ≡ v
      id' Nil = refl
      id' (Cons a v) = cons-cong refl (id' v)

      comp' : ∀ {n A B C} → (u : Vec n (B → C)) (v : Vec n (A → B)) (w : Vec n A)
              → ap' (ap' (ap' (full _∘_ n) u) v) w ≡ ap' u (ap' v w)
      comp' Nil Nil Nil = refl
      comp' (Cons a u) (Cons b v) (Cons c w) = cons-cong refl (comp' u v w)

      hom' : ∀ {n A B} (f : A → B) (x : A) → ap' (full f n) (full x n) ≡ full (f x) n
      hom' {zero} f x = refl
      hom' {suc n} f x = cons-cong refl (hom' {n} f x)

      ic' : ∀ {n A B} (u : Vec n (A → B)) (y : A) → ap' u (full y n) ≡ ap' (full (_$ y) n) u
      ic' Nil y = refl
      ic' (Cons a u) y = cons-cong refl (ic' u y)


tail : ∀ {n A} → Vec (suc n) A → Vec n A
tail (Cons x v) = v

diag : ∀ {n A} → Vec n (Vec n A) → Vec n A
diag Nil = Nil
diag (Cons (Cons a w) v) = Cons a (diag (fmap tail v))

fmap-pure : ∀ {A B F} {{aF : Applicative F}} (f : A → B) (x : A)
            → fmap f (Applicative.pure aF x) ≡ Applicative.pure aF (f x)
fmap-pure f x = begin
  fmap f (pure x) ≡⟨ sym (appFun f (pure x)) ⟩
  pure f <*> pure x ≡⟨ A-hom f x ⟩
  pure (f x) ∎

diag-full : ∀ {A} (n : ℕ) (v : Vec n A) → diag (full v n) ≡ v
diag-full _ Nil = refl
diag-full (suc n) (Cons a v) = cons-cong refl (begin
  diag (fmap tail (full (Cons a v) n)) ≡⟨ cong diag (fmap-pure tail (Cons a v)) ⟩
  diag (full v n) ≡⟨ diag-full n v ⟩
  v ∎)

instance
  VecM : {n : ℕ} → Monad (Vec n)
  VecM = record { _>>=_ = bind' ;
                  left-1 = left' ;
                  right-1 = {!!} ;
                  assoc = {!!} }

    where
      bind' : ∀ {n A B} → Vec n A → (A → Vec n B) → Vec n B
      bind' v f = diag (fmap f v)

      left' : ∀ {n A B} (a : A) (k : A → Vec n B) → bind' (pure a) k ≡ k a
      left' {n} a k = begin
          diag (fmap k (full a n)) ≡⟨ cong diag (fmap-pure k a) ⟩
          diag (full (k a) n) ≡⟨ diag-full n (k a) ⟩
          k a ∎

      right' : ∀ {n A} (m : Vec n A) → bind' m pure ≡ m
      right' Nil = refl
      right' (Cons a m) = begin
        bind' (Cons a m) pure ≡⟨ refl ⟩
        diag (fmap pure (Cons a m)) ≡⟨ cons-cong refl {!!} ⟩ -- :(
        Cons a m ∎
