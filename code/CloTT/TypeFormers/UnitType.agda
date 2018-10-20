{-
The unit type.
-}
module CloTT.TypeFormers.UnitType where

open import Data.Product
open import Data.Unit
open import Prelude
open import Presheaves
open import CloTT.Structure

-- Formation Rule
Unit : {n : ℕ} → Ty n
Unit = Terminal

-- Introduction rule
* : {n : ℕ} → (Γ : Ctx n) → Tm Γ Unit
proj₁ (* Γ) Δ x = tt
proj₂ (* Γ) Δ Δ' x = refl

-- Elimination rule
Unit-rec : {n : ℕ} → (Γ : Ctx n) → (A : Ty n) → (t : Tm Γ A)
  → Tm (Γ ,, Unit) A
proj₁ (Unit-rec Γ A (t , p)) Δ (x , tt) = t Δ x
proj₂ (Unit-rec Γ A (t , p)) Δ Δ' (x , tt) = p Δ Δ' x

-- Computation rule
Unit-rec-tt : {n : ℕ} → (Γ : Ctx n) → (A : Ty n) → (t : Tm Γ A)
  → def-eq Γ A
           (subst-Tm {_} {Γ} {Unit} {A} (Unit-rec Γ A t) (* Γ))
           t
Unit-rec-tt Γ A (t , p) Δ z = refl

Unit-eta : {n : ℕ} → (Γ : Ctx n) (t : Tm Γ Unit) → def-eq Γ Unit t (* Γ)
Unit-eta Γ t Δ z = refl
