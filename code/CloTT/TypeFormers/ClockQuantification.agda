{-
Clock quantification.
Given a type A depending on n+1 clocks and a name i for a clock, our goal is to obtain a type □A depending on n clocks.
How does this work concretely?
We are given n clocks κ₁, ..., κn.
To be able to use A, we need to feed it n+1 clocks and thus we need one more clock.
This clock is inserted at position i.
Hence, an object is a pair of a clock and an object of A using the original clock context with that one inserted at i.
-}
module CloTT.TypeFormers.ClockQuantification where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure

module _ {n : ℕ} (A : Ty (suc n)) (i : Name (suc n)) where

  private module A = Ty A

  -- Object part
  □Obj : ClockCtx n → Set
  □Obj Δ =
    Σ ((κ : Clock) → A.Obj (insertClockCtx i κ Δ))
      (λ x → (κ : Clock) (α : Size≤ κ)
        → A.Mor (insertClockCtx i κ Δ) _ (x κ) ≡ x α)

  -- Morphism part
  □Mor : (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ)
    → □Obj Δ → □Obj Δ'
  proj₁ (□Mor Δ Δ' (x , p)) κ = A.Mor (insertClockCtx i κ Δ) _ (x κ)
  proj₂ (□Mor Δ Δ' (x , p)) κ α =
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
    ∎

  -- Preservation of identity
  □MorId : {Δ : ClockCtx n} {x : □Obj Δ}
    → □Mor Δ (coeClockCtx Δ) x ≡ x
  □MorId =
    Σ≡-uip (funext (λ _ → funext (λ _ → uip)))
           (funext (λ _ → A.MorId))

  -- Preservation of composition
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
