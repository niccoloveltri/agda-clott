module CloTT.TypeFormers.ClockQuantificationType where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers.WeakenClock
open import CloTT.TypeFormers.ClockQuantification

clock-abs : {n : ℕ} (i : Name (suc n)) (Γ : Ctx n) (A : Ty (suc n)) (e : Tm (WC Γ i) A)
          → Tm Γ (□ A i)
clock-abs i Γ A (e , p) =
  (λ Δ x → (λ κ → e (insertClockCtx i κ Δ) (subst (Ctx.Obj Γ) (remove-insert i κ ) x))
         ,
         λ κ α → trans (p (insertClockCtx i κ Δ) _ (subst (Ctx.Obj Γ) (remove-insert i κ ) x))
                       (cong (e (insertClockCtx i α Δ))
                       (trans (cong₂-dep (λ y z → Ctx.Mor Γ y _ z)
                                         (trans (sym (remove-insert i κ)) (remove-insert i _))
                                         (trans (subst-trans (remove-insert i κ) (trans (sym (remove-insert i κ)) (remove-insert i α)))
                                                (cong (λ y → subst (Ctx.Obj Γ) y x) uip)))
                              (Ctx.MorId Γ))))
  , {!!}
