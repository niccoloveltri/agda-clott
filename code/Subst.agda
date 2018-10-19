module Subst where

open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Basics
open import Presheaves
open import Contexts
open import ClockContexts
open import ContextOperations
open import Types
open import Terms
open import DefinitionalEquality

subst-Tm : {n : ℕ} {Γ : Ctx n} {A B : Ty n} (t : Tm (Γ ,, A) B) (x : Tm Γ A) → Tm Γ B
subst-Tm (t , p) (x , q) = (λ Δ y → t Δ (y , x Δ y))
                           , λ Δ Δ' y → trans (p Δ Δ' (y , x Δ y))
                                              (cong (λ z → t Δ' (_ , z)) (q Δ Δ' y))
