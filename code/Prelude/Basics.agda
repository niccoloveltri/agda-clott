{-
We work in type theory with the following axioms:
1. UIP
2. Functional extensionality
In addition, we need some general lemmata.

This file is structured as follows:
1. The main axioms
2. Equality in Σ-types
3. Lemmata about ≡
-}
module Prelude.Basics where

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Sum

-- 1. The main axioms
postulate funext : ∀{ℓ ℓ'} → Extensionality ℓ ℓ'

uip : ∀{ℓ} {A : Set ℓ} → {a a' : A}
  → {p p' : a ≡ a'} → p ≡ p' 
uip {p = refl} {refl} = refl

-- 2. Equality in Σ-types
Σ≡ : {A : Set}{P : A → Set}
  → {a a' : A} {p : P a} {p' : P a'}
  → (e : a ≡ a') → subst P e p ≡ p' → (a , p) ≡ (a' , p')
Σ≡ refl refl = refl

path-prod : {A B : Set} {a₁ a₂ : A} {b₁ b₂ : B} → a₁ ≡ a₂ → b₁ ≡ b₂ → (a₁ , b₁) ≡ (a₂ , b₂)
path-prod refl refl = refl

sum-path : {A B C : Set} (f g : A ⊎ B → C)
         → ((a : A) → f (inj₁ a) ≡ g (inj₁ a))
         → ((b : B) → f (inj₂ b) ≡ g (inj₂ b))
         → (x : A ⊎ B) → f x ≡ g x
sum-path f g Ha Hb = [_,_] Ha Hb

isProp : Set → Set
isProp P = {x y : P} → x ≡ y

Σ≡-uip : {A : Set}{P : A → Set}
  → ({a : A} → isProp (P a))
  → {a a' : A} {p : P a} {p' : P a'}
  → (e : a ≡ a') → (a , p) ≡ (a' , p')
Σ≡-uip q refl = cong (_,_ _) q

-- 3. Lemmata about ≡

-- Dependent functions preserve equality
cong-dep : {A : Set}{P : A → Set}
  → (f : (a : A) → P a)
  → {x y : A} 
  → (e : x ≡ y) → subst P e (f x) ≡ f y
cong-dep f refl = refl

-- Functions with two arguments preserve equality
cong₂-dep : {A B : Set}{P : A → Set}
  → (f : (a : A) (p : P a) → B)
  → {a a' : A} {p : P a} {p' : P a'}
  → (e : a ≡ a') → subst P e p ≡ p' → f a p ≡ f a' p'
cong₂-dep f refl refl = refl

-- Transport of a composition
subst-trans : {A : Set}{P : A → Set}
  → {x y z : A}(e : x ≡ y)(e' : y ≡ z)
  → {p : P x}
  → subst P e' (subst P e p) ≡ subst P (trans e e') p
subst-trans refl refl = refl
