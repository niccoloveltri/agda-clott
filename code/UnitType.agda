module UnitType where

open import Data.Unit
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Basics
open import Presheaves
open import Terminal
open import Contexts
open import ContextOperations
open import Types
open import Terms
open import DefinitionalEquality
open import Subst
open import FunctionType

-- Formation Rule
Unit : {n : ℕ} → Ty n
Unit = Terminal

-- Introduction rule
* : {n : ℕ} → (Γ : Ctx n) → Tm Γ Unit
* Γ = (λ Δ x → tt) , (λ Δ Δ' x → refl)

-- Elimination rule
Unit-rec : {n : ℕ} → (Γ : Ctx n) → (A : Ty n) → (t : Tm Γ A) → Tm (Γ ,, Unit) A
Unit-rec Γ A (t , p) = (λ { Δ (x , tt) → t Δ x}) , λ { Δ Δ' (x , tt) → p Δ Δ' x}

-- Computation rule
Unit-rec-tt : {n : ℕ} → (Γ : Ctx n) → (A : Ty n) → (t : Tm Γ A)
            → def-eq
                Γ
                A
                (subst-Tm {_} {Γ} {Unit} {A} (Unit-rec Γ A t) (* Γ))
                t
Unit-rec-tt Γ A (t , p) Δ z = refl

Unit-eta : {n : ℕ} → (Γ : Ctx n) (t : Tm Γ Unit) → def-eq Γ Unit t (* Γ)
Unit-eta Γ t Δ z = refl
