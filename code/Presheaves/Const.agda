{-
The constant presheaf on A is A on each object and on each morphism the identity.
-}
module Presheaves.Const where

open import Prelude
open import Presheaves.Presheaves

module _ {n : ℕ} (A : Set) where

  -- Object part
  ConstObj : ClockCtx n → Set
  ConstObj _ = A

  -- Morphism part
  ConstMor : (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ)
    → ConstObj Δ → ConstObj Δ'
  ConstMor _ _ x = x

  -- Preservation of identity
  ConstMorId : {Δ : ClockCtx n} {x : A}
    → ConstMor Δ (coeClockCtx Δ) x ≡ x
  ConstMorId = refl

  -- Preservation of composition
  ConstMorComp : {Δ : ClockCtx n} {Δ' : ClockCtx≤ Δ}
    → {Δ'' : ClockCtx≤ Δ'}{x : ConstObj Δ}
    → ConstMor Δ _ x ≡ ConstMor Δ' Δ'' (ConstMor Δ Δ' x)
  ConstMorComp = refl
  
  Const : PSh n
  Const = record
    { Obj = ConstObj
    ; Mor = ConstMor
    ; MorId = ConstMorId
    ; MorComp = ConstMorComp
    }
