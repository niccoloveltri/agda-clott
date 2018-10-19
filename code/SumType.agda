module SumType where

open import Data.Nat
open import Data.Product
open import Data.Sum
open import Size
open import Data.Fin
open import Relation.Binary.PropositionalEquality
open import Basics
open import Presheaves
open import Sum
open import Contexts
open import ClockContexts
open import ContextOperations
open import Types
open import Terms
open import DefinitionalEquality
open import Subst

-- Formation rule
_⊕_ : {n : ℕ} (A B : Ty n) → Ty n
A ⊕ B = Sum A B

-- Introduction rule
inl : {n : ℕ} (Γ : Ctx n) (A B : Ty n) (x : Tm Γ A) → Tm Γ (A ⊕ B)
inl Γ A B (x , p) = (λ Δ y → inj₁ (x Δ y)) , λ Δ Δ' y → cong inj₁ (p Δ Δ' y)

inr : {n : ℕ} (Γ : Ctx n) (A B : Ty n) (x : Tm Γ B) → Tm Γ (A ⊕ B)
inr Γ A B (x , p) = (λ Δ y → inj₂ (x Δ y)) , λ Δ Δ' y → cong inj₂ (p Δ Δ' y)

-- Elimination rule
sum-rec : {n : ℕ} (Γ : Ctx n) (A B C : Ty n)
          (left : Tm (Γ ,, A) C) (right : Tm (Γ ,, B) C)
          → Tm (Γ ,, (A ⊕ B)) C
sum-rec Γ A B C (left , p) (right , q) =
  (λ { Δ (x , inj₁ l) → left Δ (x , l) ; Δ (x , inj₂ r) → right Δ (x , r)})
  ,
  λ { Δ Δ' (x , inj₁ l) → p Δ Δ' (x , l) ; Δ Δ' (x , inj₂ r) → q Δ Δ' (x , r)}

-- Computation rule
sum-rec-inl : {n : ℕ} (Γ : Ctx n) (A B C : Ty n)
              (left : Tm (Γ ,, A) C) (right : Tm (Γ ,, B) C)
              (x : Tm Γ A)
              → def-eq
                Γ
                C
                (subst-Tm {_} {Γ} {A ⊕ B} {C} (sum-rec Γ A B C left right) (inl Γ A B x))
                (subst-Tm {_} {Γ} {A} {C} left x )
sum-rec-inl Γ A B C (left , p) (right , q) (x , r) Δ z = refl

sum-rec-inr : {n : ℕ} (Γ : Ctx n) (A B C : Ty n)
              (left : Tm (Γ ,, A) C) (right : Tm (Γ ,, B) C)
              (x : Tm Γ B)
              → def-eq
                Γ
                C
                (subst-Tm {_} {Γ} {A ⊕ B} {C} (sum-rec Γ A B C left right) (inr Γ A B x))
                (subst-Tm {_} {Γ} {B} {C} right x )
sum-rec-inr Γ A B C (left , p) (right , q) (x , r) Δ z = refl
