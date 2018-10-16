
module Basics where

open import Relation.Binary.PropositionalEquality

postulate funext : ∀{ℓ ℓ'} → Extensionality ℓ ℓ'

uip : ∀{ℓ} {A : Set ℓ} → {a a' : A}
  → {p p' : a ≡ a'} → p ≡ p' 
uip {p = refl} {refl} = refl

