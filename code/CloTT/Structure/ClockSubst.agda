{-
Substitution of terms.
This rule can be written as
Γ ⊢ a : A         Γ ,, x : A ⊢ t[x] : B
---------------------------------------
           Γ ⊢ t[x ↦ a]
-}
module CloTT.Structure.ClockSubst where

open import Data.Product
open import Prelude
open import CloTT.Structure.Contexts
open import CloTT.Structure.ContextOperations
open import CloTT.Structure.Types
open import CloTT.Structure.Terms
{-
module _ {n : ℕ} (A : Ty (suc n)) (i : Name (suc n)) (j : Name n) where

  private module A = Ty A

  clock-subst-obj : ClockCtx n → Set
  clock-subst-obj Δ = A.Obj (insertClockCtx i (Δ j) Δ)

  clock-subst-mor : (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ)
    → clock-subst-obj Δ → clock-subst-obj Δ'
  clock-subst-mor Δ Δ' x = A.Mor (insertClockCtx i (Δ j) Δ) _ x

  clock-subst : Ty n
  clock-subst = record
    { Obj = clock-subst-obj
    ; Mor = clock-subst-mor
    ; MorId = A.MorId
    ; MorComp = λ {Δ} → A.MorComp {insertClockCtx i (Δ j) Δ}
    }
-}

module _ {n : ℕ} (A : Ty (suc n)) (i : Name (suc n)) (j : Name (suc n)) where

  private module A = Ty A

  clock-subst-obj : ClockCtx (suc n) → Set
  clock-subst-obj Δ = A.Obj (Δ [ i ↦ Δ j ])

  clock-subst-mor : (Δ : ClockCtx (suc n)) (Δ' : ClockCtx≤ Δ)
    → clock-subst-obj Δ → clock-subst-obj Δ'
  clock-subst-mor Δ Δ' x = A.Mor (Δ [ i ↦ Δ j ]) _ x

  clock-subst : Ty (suc n)
  clock-subst = record
    { Obj = clock-subst-obj
    ; Mor = clock-subst-mor
    ; MorId = A.MorId
    ; MorComp = λ {Δ} → A.MorComp {Δ [ i ↦ Δ j ]}
    }
