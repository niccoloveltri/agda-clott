{-
The Product type.
-}
module CloTT.TypeFormers.ProductType where

open import Data.Product
open import Data.Unit
open import Prelude
open import Presheaves
open import CloTT.Structure

-- Formation rule
_⊗_ : {n : ℕ} (A B : Ty n) → Ty n
A ⊗ B = Prod A B

-- Introduction rule
pair : {n : ℕ} (Γ : Ctx n) (A B : Ty n) (x : Tm Γ A) (y : Tm Γ B) → Tm Γ (A ⊗ B)
proj₁ (pair Γ A B (x , p) (y , q)) Δ t = (x Δ t) , (y Δ t)
proj₂ (pair Γ A B (x , p) (y , q)) Δ Δ' t =
  begin
    (Ctx.Mor A Δ Δ' (x Δ t) , Ctx.Mor B Δ Δ' (y Δ t))
  ≡⟨ cong (λ z → (z , _)) (p Δ Δ' t) ⟩
    (x Δ' (Ctx.Mor Γ Δ Δ' t) , Ctx.Mor B Δ Δ' (y Δ t))
  ≡⟨ cong (λ z → (_ , z)) (q Δ Δ' t) ⟩
    (x Δ' (Ctx.Mor Γ Δ Δ' t) , y Δ' (Ctx.Mor Γ Δ Δ' t))
  ∎

-- Elimination rules
pr₁ : {n : ℕ} (Γ : Ctx n) (A B : Ty n) → Tm Γ (A ⊗ B) → Tm Γ A
proj₁ (pr₁ Γ A B (x , p)) Δ t = proj₁ (x Δ t)
proj₂ (pr₁ Γ A B (x , p)) Δ Δ' t = cong proj₁ (p Δ Δ' t)

pr₂ : {n : ℕ} (Γ : Ctx n) (A B : Ty n) → Tm Γ (A ⊗ B) → Tm Γ B
proj₁ (pr₂ Γ A B (x , p)) Δ t = proj₂ (x Δ t)
proj₂ (pr₂ Γ A B (x , p)) Δ Δ' t = cong proj₂ (p Δ Δ' t)

-- Computation rules
pr₁-pair : {n : ℕ} (Γ : Ctx n) (A B : Ty n) (x : Tm Γ A) (y : Tm Γ B)
  → def-eq Γ A
           (pr₁ Γ A B (pair Γ A B x y))
           x
pr₁-pair Γ A B (x , p) (y , q) Δ t = refl

pr₂-pair : {n : ℕ} (Γ : Ctx n) (A B : Ty n) (x : Tm Γ A) (y : Tm Γ B)
  → def-eq Γ B
           (pr₂ Γ A B (pair Γ A B x y))
           y
pr₂-pair Γ A B (x , p) (y , q) Δ t = refl

-- Eta rule
prod-eta : {n : ℕ} (Γ : Ctx n) (A B : Ty n) (x : Tm Γ (A ⊗ B))
  → def-eq Γ (A ⊗ B)
           (pair Γ A B (pr₁ Γ A B x) (pr₂ Γ A B x)) 
           x
prod-eta Γ A B x Δ t = refl
