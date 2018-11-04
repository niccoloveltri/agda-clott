module CloTT.TypeFormers.Fix where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers.Later
open import CloTT.TypeFormers.FunctionType

fix₁ : {n : ℕ} (Γ : Ctx n) (A : Ty n) (i : Name n)
          → (f : Tm Γ (Later A i ⇒ A))
          → (Δ : ClockCtx n) → Ctx.Obj Γ Δ → Ctx.Obj A Δ
dfix₁ : {n : ℕ} (Γ : Ctx n) (A : Ty n) (i : Name n)
          → (f : Tm Γ (Later A i ⇒ A))
          → (Δ : ClockCtx n) → Ctx.Obj Γ Δ → LaterObj A i Δ
fix₁ Γ A i (f , p) Δ x = proj₁ (f Δ x) _ (dfix₁ Γ A i (f , p) Δ x) 
force (proj₁ (dfix₁ Γ A i (f , p) Δ x)) α = fix₁ Γ A i (f , p) (Δ [ i ↦ α ]) {!!}
proj₂ (dfix₁ Γ A i (f , p) Δ x) = {!!}

fix : {n : ℕ} (Γ : Ctx n) (A : Ty n) (i : Name n)
          → (e : Tm Γ (Later A i ⇒ A)) → Tm Γ A
proj₁ (fix Γ A i e) = {!!}         
proj₂ (fix Γ A i e) = {!!}         

