{-
In this file, we define the main operations on contexts.
1. We always have the empty context.
2. Contexts can be extended with types
3. We can use variables in the context. This represents the following rule.
Γ ,, A ⊢ x : A
4. We can weaken the context. This represents the following rule
  Γ ⊢ t : B
--------------
Γ ,, A ⊢ t : B
-}
module CloTT.Structure.ContextOperations where

open import Data.Product
open import Prelude
open import Presheaves
open import CloTT.Structure.Contexts
open import CloTT.Structure.Types
open import CloTT.Structure.Terms

-- 1. The empty context
∙ : {n : ℕ} → Ctx n -- ∙ = \.
∙ = Terminal

-- 2. Context extension
_,,_ : {n : ℕ} → Ctx n → Ty n → Ctx n
Γ ,, A = Prod Γ A

-- 3. The variable rule
var : {n : ℕ} (Γ : Ctx n) (A : Ty n) → Tm (Γ ,, A) A
proj₁ (var Γ A) Δ (γ , x) = x
proj₂ (var Γ A) Δ Δ' (γ , x) = refl

-- 4. Weakening
weaken : {n : ℕ} (Γ : Ctx n) (A B : Ty n) → Tm Γ B → Tm (Γ ,, A) B
proj₁ (weaken Γ A B (t , p)) Δ (x₁ , x₂) = t Δ x₁
proj₂ (weaken Γ A B (t , p)) Δ Δ' (x₁ , x₂) = p Δ Δ' x₁
