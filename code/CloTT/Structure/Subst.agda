{-
Substitution of terms.
This rule can be written as
Γ ⊢ a : A         Γ ,, x : A ⊢ t[x] : B
---------------------------------------
           Γ ⊢ t[x ↦ a]
-}
module CloTT.Structure.Subst where

open import Data.Product
open import Prelude
open import CloTT.Structure.Contexts
open import CloTT.Structure.ContextOperations
open import CloTT.Structure.Types
open import CloTT.Structure.Terms

subst-Tm : {n : ℕ} {Γ : Ctx n} {A B : Ty n}
  → (t : Tm (Γ ,, A) B) (x : Tm Γ A)
  → Tm Γ B
proj₁ (subst-Tm (t , p) (x , q)) Δ y = t Δ (y , x Δ y)
proj₂ (subst-Tm {_} {Γ} {A} {B} (t , p) (x , q)) Δ Δ' y =
  begin
    Ctx.Mor B Δ Δ' (t Δ (y , x Δ y))
  ≡⟨ p Δ Δ' (y , x Δ y) ⟩
    t Δ' (Ctx.Mor (Γ ,, A) Δ Δ' (y , x Δ y))
  ≡⟨ cong (λ z → t Δ' (_ , z)) (q Δ Δ' y) ⟩
    t Δ' (Ctx.Mor Γ Δ Δ' y , x Δ' (Ctx.Mor Γ Δ Δ' y))
  ∎
