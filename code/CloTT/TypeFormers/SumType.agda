{-
The sum type.
-}
module CloTT.TypeFormers.SumType where

open import Data.Product
open import Data.Sum
open import Data.Unit
open import Prelude
open import Presheaves
open import CloTT.Structure

-- Formation rule
_⊕_ : {n : ℕ} (A B : Ty n) → Ty n
A ⊕ B = Sum A B

-- Introduction rule
inl : {n : ℕ} (Γ : Ctx n) (A B : Ty n) (x : Tm Γ A) → Tm Γ (A ⊕ B)
proj₁ (inl Γ A B (x , p)) Δ y = inj₁ (x Δ y)
proj₂ (inl Γ A B (x , p)) Δ Δ' y = cong inj₁ (p Δ Δ' y)

inr : {n : ℕ} (Γ : Ctx n) (A B : Ty n) (x : Tm Γ B) → Tm Γ (A ⊕ B)
proj₁ (inr Γ A B (x , p)) Δ y = inj₂ (x Δ y)
proj₂ (inr Γ A B (x , p)) Δ Δ' y = cong inj₂ (p Δ Δ' y)

-- Elimination rule
sum-rec : {n : ℕ} (Γ : Ctx n) (A B C : Ty n)
          (left : Tm (Γ ,, A) C) (right : Tm (Γ ,, B) C)
          → Tm (Γ ,, (A ⊕ B)) C
proj₁ (sum-rec Γ A B C (left , p) (right , q)) Δ (x , inj₁ l) = left Δ (x , l)
proj₁ (sum-rec Γ A B C (left , p) (right , q)) Δ (x , inj₂ r) = right Δ (x , r)
proj₂ (sum-rec Γ A B C (left , p) (right , q)) Δ Δ' (x , inj₁ l) = p Δ Δ' (x , l)
proj₂ (sum-rec Γ A B C (left , p) (right , q)) Δ Δ' (x , inj₂ r) = q Δ Δ' (x , r)

-- Computation rules
sum-rec-inl : {n : ℕ} (Γ : Ctx n) (A B C : Ty n)
  → (left : Tm (Γ ,, A) C) (right : Tm (Γ ,, B) C)
  → (x : Tm Γ A)
  → def-eq Γ C
           (subst-Tm {_} {Γ} {A ⊕ B} {C} (sum-rec Γ A B C left right) (inl Γ A B x))
           (subst-Tm {_} {Γ} {A} {C} left x )
sum-rec-inl Γ A B C (left , p) (right , q) (x , r) Δ z = refl

sum-rec-inr : {n : ℕ} (Γ : Ctx n) (A B C : Ty n)
  → (left : Tm (Γ ,, A) C) (right : Tm (Γ ,, B) C)
  → (x : Tm Γ B)
  → def-eq Γ C
           (subst-Tm {_} {Γ} {A ⊕ B} {C} (sum-rec Γ A B C left right) (inr Γ A B x))
           (subst-Tm {_} {Γ} {B} {C} right x )
sum-rec-inr Γ A B C (left , p) (right , q) (x , r) Δ z = refl
