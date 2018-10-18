
module Basics where

open import Relation.Binary.PropositionalEquality
open import Data.Product

postulate funext : ∀{ℓ ℓ'} → Extensionality ℓ ℓ'

uip : ∀{ℓ} {A : Set ℓ} → {a a' : A}
  → {p p' : a ≡ a'} → p ≡ p' 
uip {p = refl} {refl} = refl

isProp : Set → Set
isProp P = {x y : P} → x ≡ y

Σ≡ : {A : Set}{P : A → Set}
  → {a a' : A} {p : P a} {p' : P a'}
  → (e : a ≡ a') → subst P e p ≡ p' → (a , p) ≡ (a' , p')
Σ≡ refl refl = refl

Σ≡-uip : {A : Set}{P : A → Set}
  → ({a : A} → isProp (P a))
  → {a a' : A} {p : P a} {p' : P a'}
  → (e : a ≡ a') → (a , p) ≡ (a' , p')
Σ≡-uip q refl = cong (_,_ _) q
