module CloTT.TypeFormers.Force where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers.Later
open import CloTT.TypeFormers.ClockQuantification

force-tm₁₁ : {n : ℕ} {Γ : Ctx n} {A : Ty (suc n)} (i : Name (suc n))
  → Tm Γ (□ (Later A i ) i)
  → (Δ : ClockCtx n)
  → Ctx.Obj Γ Δ
  → (κ : Clock) → Ctx.Obj A (insertClockCtx i κ Δ)
force-tm₁₁ {n} {Γ} {A} i (e , _) Δ x κ = Ctx.Mor A (insertClockCtx i (↑ κ) Δ [ i ↦ κ ]) _ (force (proj₁ (proj₁ (e Δ x) (↑ κ))) _)

force-tm₁ : {n : ℕ} {Γ : Ctx n} {A : Ty (suc n)} (i : Name (suc n))
  → Tm Γ (□ (Later A i ) i)
  → (Δ : ClockCtx n)
  → Ctx.Obj Γ Δ → □Obj A i Δ
proj₁ (force-tm₁ {n} {Γ} {A} i e Δ x) = force-tm₁₁ {n} {Γ} {A} i e Δ x 
proj₂ (force-tm₁ i e Δ x) = {!!}

force-tm : {n : ℕ} {Γ : Ctx n} {A : Ty (suc n)} (i : Name (suc n)) → Tm Γ (□ (Later A i ) i) → Tm Γ (□ A i) 
proj₁ (force-tm {n} {Γ} {A} i e) Δ x = force-tm₁ {n} {Γ} {A} i e Δ x
proj₂ (force-tm i e) = {!!}
