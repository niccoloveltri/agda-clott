module Exp where

open import Data.Product
open import Data.Nat
open import ClockContexts
open import Presheaves
open import Relation.Binary.PropositionalEquality

module _ {n : ℕ} (P Q : PSh n) where

  module P = PSh P
  module Q = PSh Q
  
  ExpObj : ClockCtx n → Set
  ExpObj Δ =
    Σ ((Δ' : ClockCtx≤ Δ) → P.Obj Δ' → Q.Obj Δ')
      (λ f → (Δ' : ClockCtx≤ Δ) (Δ'' : ClockCtx≤ Δ)
             (x : P.Obj Δ')
               → Q.Mor Δ' _ (f Δ' x)
                 ≡
                 f Δ'' (P.Mor Δ' _ x))

  ExpMor : (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ)
    → ExpObj Δ → ExpObj Δ'
  ExpMor Δ Δ' (f , p) = (λ _ → f _) , (λ _ _ → p _ _)

  ExpMorId : {Δ : ClockCtx n} {x : ExpObj Δ}
    → ExpMor Δ (coeClockCtx Δ) x ≡ x
  ExpMorId = refl

  ExpMorComp : {Δ : ClockCtx n} {Δ' : ClockCtx≤ Δ}
    → {Δ'' : ClockCtx≤ Δ'}{x : ExpObj Δ}
    → ExpMor Δ _ x ≡ ExpMor Δ' Δ'' (ExpMor Δ Δ' x)
  ExpMorComp = refl

  Exp : PSh n
  Exp = record
    { Obj = ExpObj
    ; Mor = ExpMor
    ; MorId = ExpMorId
    ; MorComp = ExpMorComp
    }

