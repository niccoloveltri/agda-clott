module CloTT.TypeFormers.ClockQuantificationType where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers.WeakenClock
open import CloTT.TypeFormers.ClockQuantification

clock-abs : {n : ℕ} (i : Name (suc n)) (Γ : Ctx n) (A : Ty (suc n)) (e : Tm (WC Γ i) A)
          → Tm Γ (□ A i)
proj₁ (proj₁ (clock-abs i Γ A (e , p)) Δ x) κ =
  e (insertClockCtx i κ Δ) (subst (Ctx.Obj Γ) (remove-insert i κ) x)
proj₂ (proj₁ (clock-abs i Γ A (e , p)) Δ x) κ α =
  begin
    Ctx.Mor A (insertClockCtx i κ Δ) _ (e (insertClockCtx i κ Δ) (subst (Ctx.Obj Γ) (remove-insert i κ) x))
  ≡⟨ p (insertClockCtx i κ Δ) _ (subst (Ctx.Obj Γ) (remove-insert i κ) x) ⟩
    e (insertClockCtx i α Δ) (Ctx.Mor Γ (removeClock i (insertClockCtx i κ Δ)) _ (subst (Ctx.Obj Γ) (remove-insert i κ) x))
  ≡⟨ cong (e (insertClockCtx i α Δ))
       (begin
          Ctx.Mor Γ (removeClock i (insertClockCtx i κ Δ)) _           
            (subst (Ctx.Obj Γ) (remove-insert i κ) x)
        ≡⟨ cong₂-dep (λ y z → Ctx.Mor Γ y _ z)
                     (sym (remove-insert i κ))
                     (trans (subst-trans (remove-insert i κ) (sym (remove-insert i κ)))
                            (cong (λ y → subst (Ctx.Obj Γ) y x) uip)) ⟩
          Ctx.Mor Γ Δ _ x
        ≡⟨ sym (cong₂-dep (λ y z → Ctx.Mor Γ y _ z) (sym (remove-insert i α))
                     (trans (subst-trans (remove-insert i α) (sym (remove-insert i α))) (cong (λ y → subst (Ctx.Obj Γ) y x) uip))) ⟩
          Ctx.Mor Γ (removeClock i (insertClockCtx i α Δ)) _ (subst (Ctx.Obj Γ) (remove-insert i α) x)
        ∎) ⟩  
    e (insertClockCtx i α Δ) (Ctx.Mor Γ (removeClock i (insertClockCtx i α Δ)) _ (subst (Ctx.Obj Γ) (remove-insert i α) x))
  ≡⟨ cong (e (insertClockCtx i α Δ)) (Ctx.MorId Γ) ⟩  
    e (insertClockCtx i α Δ) (subst (Ctx.Obj Γ) (remove-insert i α) x)
  ∎
proj₂ (clock-abs i Γ A (e , p)) Δ Δ' x =
  Σ≡-uip (funext (λ _ → (funext λ _ → uip)))
         (funext (λ κ →
           begin
             Ctx.Mor A (insertClockCtx i κ Δ) _ (e (insertClockCtx i κ Δ) (subst (Ctx.Obj Γ) (remove-insert i κ) x))
           ≡⟨ p (insertClockCtx i κ Δ) _ (subst (Ctx.Obj Γ) (remove-insert i κ) x) ⟩  
             e (insertClockCtx i κ Δ') (Ctx.Mor Γ (removeClock i (insertClockCtx i κ Δ)) _ (subst (Ctx.Obj Γ) (remove-insert i κ) x))
           ≡⟨ cong (e (insertClockCtx i κ Δ'))
                (begin
                   Ctx.Mor Γ (removeClock i (insertClockCtx i κ Δ)) _ (subst (Ctx.Obj Γ) (remove-insert i κ) x)
                 ≡⟨ cong₂-dep (λ y z → Ctx.Mor Γ y _ z)
                              (sym (remove-insert i κ))
                              (trans (subst-trans (remove-insert i κ) (sym (remove-insert i κ)))
                                     (cong (λ y → subst (Ctx.Obj Γ) y x) uip)) ⟩
                   Ctx.Mor Γ Δ _ x
                 ≡⟨ sym (cong-dep (λ z → Ctx.Mor Γ Δ _ x) (remove-insert i κ)) ⟩
                   subst (Ctx.Obj Γ) (remove-insert i κ) (Ctx.Mor Γ Δ Δ' x)
                 ∎) ⟩   
             e (insertClockCtx i κ Δ') (subst (Ctx.Obj Γ) (remove-insert i κ) (Ctx.Mor Γ Δ Δ' x))
           ∎))

clock-application : {n : ℕ} {Γ : Ctx n} {A : Ty (suc n)} (i : Name (suc n)) (j : Name n)
  → (e : Tm Γ (□ A i)) → Tm Γ (clock-subst A i j)
proj₁ (clock-application {n} {Γ} {A} i j (e , _)) Δ x = Ty.Mor A (insertClockCtx i (Δ j) Δ) _ (proj₁ (e Δ x) (Δ j))
proj₂ (clock-application {n} {Γ} {A} i j (e , p)) Δ Δ' x =
  begin
    Ctx.Mor A (insertClockCtx i (Δ j) Δ)
              _
              (Ctx.Mor A (insertClockCtx i (Δ j) Δ) _
                         (proj₁ (e Δ x) (Δ j)))
  ≡⟨ cong (Ctx.Mor A (insertClockCtx i (Δ j) Δ) _) (Ctx.MorId A) ⟩
    Ctx.Mor A (insertClockCtx i (Δ j) Δ) _ (proj₁ (e Δ x) (Δ j))
  ≡⟨ Ctx.MorComp A ⟩
    Ctx.Mor A (insertClockCtx i (Δ' j) Δ) _ (Ctx.Mor A (insertClockCtx i (Δ j) Δ) _ (proj₁ (e Δ x) (Δ j)))
  ≡⟨ cong (Ctx.Mor A (insertClockCtx i (Δ' j) Δ) _) (proj₂ (e Δ x) (Δ j) (Δ' j)) ⟩
    Ctx.Mor A (insertClockCtx i (Δ' j) Δ) _ (proj₁ (e Δ x) (Δ' j))
  ≡⟨ Ctx.MorComp A ⟩
    Ctx.Mor A (insertClockCtx i (Δ' j) Δ') _
              (Ctx.Mor A (insertClockCtx i (Δ' j) Δ) _
                         (proj₁ (e Δ x) (Δ' j)))
  ≡⟨ cong (λ z → Ctx.Mor A (insertClockCtx i (Δ' j) Δ') _ (proj₁ z (Δ' j))) (p Δ Δ' x) ⟩
    Ctx.Mor A (insertClockCtx i (Δ' j) Δ')
              _
              (proj₁ (e Δ' (Ctx.Mor Γ Δ Δ' x)) (Δ' j))
  ∎
