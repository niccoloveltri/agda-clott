module FunctionType where

open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Basics
open import Presheaves
open import Exp
open import Contexts
open import ClockContexts
open import ContextOperations
open import Types
open import Terms
open import DefinitionalEquality
open import Subst

-- Formation rule
_⇒_ : {n : ℕ} (A B : Ty n) → Ty n
A ⇒ B = Exp A B

-- Introduction rule
lambda : {n : ℕ} {Γ : Ctx n} {A B : Ty n} (t : Tm (Γ ,, A) B) → Tm Γ (A ⇒ B)
lambda {n} {Γ} (t , p) =
  (λ Δ x →
    (λ Δ' z → t Δ' (ΓMor Δ Δ' x , z))
              ,
              λ Δ' Δ'' y →
                trans
                  (p Δ' _ (ΓMor Δ Δ' x , y))
                  (cong (λ z → t Δ'' (z , _)) (sym ΓMorComp)))
  , λ Δ Δ' x →
      Σ≡-uip (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
             (funext (λ Δ'' → (funext (λ z → cong (λ z → t Δ'' (z , _)) ΓMorComp))))
  where open PSh Γ renaming (Mor to ΓMor;MorComp to ΓMorComp)

-- Elimination rule
app : {n : ℕ} {Γ : Ctx n} {A B : Ty n} (f : Tm Γ (A ⇒ B)) (t : Tm Γ A) → Tm Γ B
app {n} {Γ} (f , p) (t , q) =
  (λ Δ x → let (f' , _) = f Δ x in f' _ (t Δ x))
  ,
  λ Δ Δ' x → let (f' , p') = f Δ x in
    trans (p' _ _ (t Δ x)) (cong₂ (λ z g → proj₁ g _ z) (q Δ Δ' x) (p Δ Δ' x))

-- Computation rule
beta : {n : ℕ} {Γ : Ctx n} {A B : Ty n} (t : Tm (Γ ,, A) B) (x : Tm Γ A)
     → def-eq Γ B (app {n} {Γ} {A} {B} (lambda {_} {Γ} {A} {B} t) x) (subst-Tm {_} {Γ} {A} {B} t x)
beta {n} {Γ} (t , p) (x , q) Δ z = cong (λ z → t Δ (z , _)) ΓMorId
  where open PSh Γ renaming (MorId to ΓMorId)

eta : {n : ℕ} {Γ : Ctx n} {A B : Ty n} (t : Tm Γ (A ⇒ B))
    → def-eq Γ
             (A ⇒ B)
             (lambda {_} {Γ} {A} {B} (app {_} {Γ ,, A} {A} {B} (weaken Γ A (A ⇒ B) t) (var Γ A)))
             t
eta (t , p) Δ x =
  Σ≡-uip (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
         (funext (λ Δ' → funext (λ z → sym (cong (λ h → proj₁ h _ z) (p Δ Δ' x)))))
