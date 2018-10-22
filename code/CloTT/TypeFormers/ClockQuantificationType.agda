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

{-

  , (λ Δ Δ' x → Σ≡-uip (funext (λ _ → (funext λ _ → uip)))
                       (funext (λ κ → trans (p (insertClockCtx i κ Δ) _ (subst (Ctx.Obj Γ) (remove-insert i κ) x))
                                            (cong (e (insertClockCtx i κ Δ')) 
                                            (trans (cong₂-dep (λ y z → Ctx.Mor Γ y _ z)
                                                              (sym (remove-insert i κ))
                                                              (trans (subst-trans (remove-insert i κ) (sym (remove-insert i κ)))
                                                                     (cong (λ y → subst (Ctx.Obj Γ) y x) {y = refl} uip)))
                                                   (sym (cong-dep (λ z → Ctx.Mor Γ Δ _ x) (remove-insert i κ))))))))
-}
