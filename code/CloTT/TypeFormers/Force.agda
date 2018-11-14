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

open import CloTT.TypeFormers.LaterType
open import CloTT.TypeFormers.WeakenClock
open import CloTT.TypeFormers.ClockQuantificationType

□pure : {n : ℕ} (Γ : Ctx n) (A : Ty (suc n)) (i : Name (suc n)) → Tm Γ (□ A i) → Tm Γ (□ (Later A i) i)
□pure Γ A i e = clock-abs i Γ (Later A i) (pure (WC Γ i) A (clock-subst-ii (WC Γ i) A i (clock-app Γ A i i e)) i)

force-□pure : {n : ℕ} (Γ : Ctx n) (A : Ty (suc n)) (i : Name (suc n)) (e : Tm Γ (□ A i))
  → def-eq Γ (□ A i)
           (force-tm {_} {Γ} {A} i (□pure Γ A i e))
           e
force-□pure Γ A i (e , p) Δ x =
  Σ≡-uip
    (funext (λ _ → funext (λ _ → uip)))
    (funext (λ κ → trans (sym (Ty.MorComp A))
                 (trans (sym (Ty.MorComp A))
                 (trans (cong (λ z → Ty.Mor A _ _ (proj₁ (e _ z) _)) (sym (Ctx.MorComp Γ)))
                 (trans (cong (λ z → Ty.Mor A _ _ (proj₁ z _)) (sym (p _ _ x)))
                 (trans (sym (Ty.MorComp A)) (proj₂ (e Δ x) _ _)))))))

□pure-force : {n : ℕ} (Γ : Ctx n) (A : Ty (suc n)) (i : Name (suc n)) (e : Tm Γ (□ (Later A i) i))
  → def-eq Γ (□ (Later A i) i)
           (□pure Γ A i (force-tm {_} {Γ} {A} i e))
           e
□pure-force Γ A i (e , p) Δ x =
  Σ≡-uip
    (funext (λ _ → funext (λ _ → uip)))
    (funext (λ κ →
      Σ≡-uip
        (funext (λ {_ → funext (λ _ → uip)}))
        (bisim A i
          (funext (λ {α → trans (sym (Ty.MorComp A))
                        (trans (sym (Ty.MorComp A))
                        (trans (cong (λ z → Ty.Mor A _ _ (force (proj₁ (proj₁ (e _ z) _)) _)) (sym (Ctx.MorComp Γ)))
                        (trans (cong (λ z → Ty.Mor A _ _ (force (proj₁ (proj₁ z _)) _)) (sym (p _ _ x)))
                        (trans (sym (Ty.MorComp A))
                        (trans {!!} (cong (λ z → force (proj₁ z) _) (proj₂ (e Δ x) (↑ ((insertClockCtx i κ Δ [ i ↦ α ]) i)) _)))
                        ))))
        })))
    ))
