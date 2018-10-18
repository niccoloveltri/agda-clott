
module ClockQuantification where

--open import Presheaves
open import Types
open import Data.Nat
open import Data.Fin
open import Size
open import Basics
open import Data.Product
open import ClockContexts
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module _ {n : ℕ} (A : Ty (suc n)) (i : Fin (suc n)) where

  module A = Ty A

  □Obj : ClockCtx n → Set
  □Obj Δ =
    Σ ((κ : Clock) → A.Obj (insertClockCtx i κ Δ))
      (λ x → (κ : Clock) (α : Size≤ κ)
        → A.Mor (insertClockCtx i κ Δ) _ (x κ) ≡ x α)

  □Mor : (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ)
    → □Obj Δ → □Obj Δ'
  □Mor Δ Δ' (x , p) =
    (λ κ → A.Mor (insertClockCtx i κ Δ) _ (x κ)) ,
    (λ κ α →
      begin
        A.Mor (insertClockCtx i κ Δ') _
          (A.Mor (insertClockCtx i κ Δ) _ (x κ))
      ≡⟨ sym A.MorComp ⟩
        A.Mor (insertClockCtx i κ Δ) _ (x κ)
      ≡⟨ A.MorComp ⟩
        A.Mor (insertClockCtx i α Δ) _
          (A.Mor (insertClockCtx i κ Δ) _ (x κ))
      ≡⟨ cong (A.Mor (insertClockCtx i α Δ) _) (p κ α) ⟩
        A.Mor (insertClockCtx i α Δ) _ (x α)
      ∎)

  □MorId : {Δ : ClockCtx n} {x : □Obj Δ}
    → □Mor Δ (coeClockCtx Δ) x ≡ x
  □MorId =
    Σ≡-uip (funext (λ _ → funext (λ _ → uip)))
           (funext (λ _ → A.MorId))
           
  □MorComp : {Δ : ClockCtx n} {Δ' : ClockCtx≤ Δ} {Δ'' : ClockCtx≤ Δ'}
      → {x : □Obj Δ}
      → □Mor Δ _ x ≡ □Mor Δ' Δ'' (□Mor Δ Δ' x)
  □MorComp =
    Σ≡-uip (funext (λ _ → funext (λ _ → uip)))
           (funext (λ _ → A.MorComp))

  □ : Ty n
  □ = record
    { Obj = □Obj
    ; Mor = □Mor
    ; MorId = □MorId
    ; MorComp = λ {_}{_}{_}{x} → □MorComp {x = x}
    }


{-
module _ {n : ℕ} (A : Ty (suc n)) (i : Fin (suc n)) where

  module A = Ty A

  □Obj : ClockCtx n → Set
  □Obj Δ =
    Σ ((κ : Clock) → A.Obj (insertClockCtx i κ Δ))
      (λ x → (κ : Clock) (α : Size≤ κ)
        → A.Mor (insertClockCtx i κ Δ) (insertClockCtx≤ i κ α Δ (coeClockCtx Δ)) (x κ)
          ≡
          subst A.Obj (insertClockCtx-lem i κ α Δ (coeClockCtx Δ)) (x α))

  □Mor : (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ)
    → □Obj Δ → □Obj Δ'
  □Mor Δ Δ' (x , p) =
    (λ κ → subst A.Obj (sym (insertClockCtx-lem i κ κ Δ Δ')) (A.Mor (insertClockCtx i κ Δ) (insertClockCtx≤ i κ κ Δ Δ') (x κ))) ,
    (λ _ _ → {!!})

  □MorId : {Δ : ClockCtx n} {x : □Obj Δ}
    → □Mor Δ (coeClockCtx Δ) x ≡ x
  □MorId {Δ} {x , p} =
    Σ≡ (funext (λ κ →
          trans {!!}
                (A.MorId {insertClockCtx i κ Δ} {x κ})))
       {!funext!}

  □ : Ty n
  □ = record
    { Obj = □Obj
    ; Mor = □Mor
    ; MorId = {!!}
    ; MorComp = {!!}
    }
-}
