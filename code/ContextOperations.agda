module ContextOperations where

open import Data.Unit
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Basics
open import Presheaves
open import Terminal
open import Product
open import Contexts
open import Types
open import Terms

∙ : {n : ℕ} → Ctx n -- ∙ = \.
∙ = Terminal

_,,_ : {n : ℕ} → Ctx n → Ty n → Ctx n
Γ ,, A = Prod Γ A

var : {n : ℕ} (Γ : Ctx n) (A : Ty n) → Tm (Γ ,, A) A
var Γ A = (λ { Δ (γ , x) → x}) , λ {Δ Δ' (γ , x) → refl}

weaken : {n : ℕ} (Γ : Ctx n) (A B : Ty n) → Tm Γ B → Tm (Γ ,, A) B
weaken Γ A B (t , p) = (λ {Δ (x₁ , x₂) → t Δ x₁}) , λ {Δ Δ' (x₁ , x₂) → p Δ Δ' x₁}
