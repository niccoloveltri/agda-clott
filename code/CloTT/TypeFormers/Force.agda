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
  → (κ : Clock) → Ty.Obj A (insertClockCtx i κ Δ)
force-tm₁₁ {n} {Γ} {A} i (e , _) Δ x κ = Ty.Mor A (insertClockCtx i (↑ κ) Δ [ i ↦ κ ]) _ (force (proj₁ (proj₁ (e Δ x) (↑ κ))) _)

force-tm₁ : {n : ℕ} {Γ : Ctx n} {A : Ty (suc n)} (i : Name (suc n))
  → Tm Γ (□ (Later A i ) i)
  → (Δ : ClockCtx n)
  → Ctx.Obj Γ Δ → □Obj A i Δ
proj₁ (force-tm₁ {n} {Γ} {A} i e Δ x) = force-tm₁₁ {n} {Γ} {A} i e Δ x 
proj₂ (force-tm₁ {n} {Γ} {A} i (e , p) Δ x) κ α =
  begin
    Ty.Mor A (insertClockCtx i κ Δ) _ (Ty.Mor A (insertClockCtx i (↑ κ) Δ [ i ↦ κ ]) _ (force (proj₁ (proj₁ (e Δ x) (↑ κ))) _))
  ≡⟨ sym (Ty.MorComp A) ⟩
    Ctx.Mor A (insertClockCtx i (↑ κ) Δ [ i ↦ κ ]) _ (force (proj₁ (proj₁ (e Δ x) (↑ κ))) _)
  ≡⟨ Ty.MorComp A ⟩
    Ctx.Mor A (insertClockCtx i (↑ κ) Δ [ i ↦ α ]) _
            (Ctx.Mor A (insertClockCtx i (↑ κ) Δ [ i ↦ κ ]) _ (force (proj₁ (proj₁ (e Δ x) (↑ κ))) _))
  ≡⟨ cong (Ctx.Mor A (insertClockCtx i (↑ κ) Δ [ i ↦ α ]) _) (proj₂ (proj₁ (e Δ x) (↑ κ)) _ α) ⟩
    Ty.Mor A (insertClockCtx i (↑ κ) Δ [ i ↦ α ]) _ (force (proj₁ (proj₁ (e Δ x) (↑ κ))) _)
  ≡⟨ Ty.MorComp A ⟩
    Ty.Mor A (insertClockCtx i (↑ α) Δ [ i ↦ α ]) _
            (Ctx.Mor A (insertClockCtx i (↑ κ) Δ [ i ↦ α ]) _ (force (proj₁ (proj₁ (e Δ x) (↑ κ))) _))
  ≡⟨ cong (λ z → Ty.Mor A (insertClockCtx i (↑ α) Δ [ i ↦ α ]) _ (force (proj₁ z) _)) (proj₂ (e Δ x) (↑ κ) _) ⟩
    Ty.Mor A (insertClockCtx i (↑ α) Δ [ i ↦ α ]) _ (force (proj₁ (proj₁ (e Δ x) (↑ α))) _)
  ∎

force-tm₂ : {n : ℕ} {Γ : Ctx n} {A : Ty (suc n)} (i : Name (suc n))
  → (e : Tm Γ (□ (Later A i ) i))
  → (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ)
  → (x : Ctx.Obj Γ Δ)
  → (κ : Clock)
  → Ty.Mor A (insertClockCtx i κ Δ) _ (force-tm₁₁ {n} {Γ} {A} i e Δ x κ)
    ≡ force-tm₁₁ {n} {Γ} {A} i e Δ' (Ctx.Mor Γ Δ Δ' x) κ
force-tm₂ {n} {Γ} {A} i (e , p) Δ Δ' x κ =
  begin
    Ty.Mor A (insertClockCtx i κ Δ) _ (Ty.Mor A (insertClockCtx i (↑ κ) Δ [ i ↦ κ ]) _ (force (proj₁ (proj₁ (e Δ x) (↑ κ))) _))
  ≡⟨ sym (Ty.MorComp A) ⟩
    Ty.Mor A (insertClockCtx i (↑ κ) Δ [ i ↦ κ ]) _ (force (proj₁ (proj₁ (e Δ x) (↑ κ))) _)
  ≡⟨ Ty.MorComp A ⟩
    Ty.Mor A (insertClockCtx i (↑ κ) Δ' [ i ↦ κ ]) _ (force (LaterMor' A i (insertClockCtx i (↑ κ) Δ) _ (proj₁ (proj₁ (e Δ x) (↑ κ)))) _)
  ≡⟨ cong (λ z → Ty.Mor A (insertClockCtx i (↑ κ) Δ' [ i ↦ κ ]) _ (force (proj₁ (proj₁ z (↑ κ))) _)) (p Δ Δ' x) ⟩
    Ty.Mor A (insertClockCtx i (↑ κ) Δ' [ i ↦ κ ]) _ (force (proj₁ (proj₁ (e Δ' (Ty.Mor Γ Δ Δ' x)) (↑ κ))) _)
  ∎

force-tm : {n : ℕ} {Γ : Ctx n} {A : Ty (suc n)} (i : Name (suc n)) → Tm Γ (□ (Later A i ) i) → Tm Γ (□ A i) 
proj₁ (force-tm {n} {Γ} {A} i e) Δ x = force-tm₁ {n} {Γ} {A} i e Δ x
proj₂ (force-tm {n} {Γ} {A} i e) Δ Δ' x =
  Σ≡-uip (funext (λ { _ → funext (λ _ → uip)}))
         (funext (λ {κ → force-tm₂ {n} {Γ} {A} i e Δ Δ' x κ}))
