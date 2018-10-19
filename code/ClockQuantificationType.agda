module ClockQuantificationType where

open import Data.Nat
open import Data.Fin
open import Size
open import Basics
open import Data.Product
open import ClockContexts
open import Relation.Binary.PropositionalEquality
open import Contexts
open import ClockContexts
open import ContextOperations
open import Types
open import Terms
open import ClockQuantification
open import DefinitionalEquality
open import WeakenClock
open ≡-Reasoning


clock-abs : {n : ℕ} (i : Fin (suc n)) (Γ : Ctx n) (A : Ty (suc n)) (e : Tm (WC Γ i) A)
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
