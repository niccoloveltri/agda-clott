
module Const where

open import Presheaves
open import Data.Nat
open import ClockContexts
open import Relation.Binary.PropositionalEquality

module _ {n : ℕ} (A : Set) where

  ConstObj : ClockCtx n → Set
  ConstObj _ = A

  ConstMor : (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ)
    → ConstObj Δ → ConstObj Δ'
  ConstMor _ _ x = x

  ConstMorId : {Δ : ClockCtx n} {x : A}
    → ConstMor Δ (coeClockCtx Δ) x ≡ x
  ConstMorId = refl

  ConstMorComp : {Δ : ClockCtx n}{Δ' : ClockCtx≤ Δ}
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


