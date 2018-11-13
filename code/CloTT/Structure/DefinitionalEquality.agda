{-
Definitional equality between terms.
Two terms are definitionally equal if they agree on all contexts and inhabitants.
-}
module CloTT.Structure.DefinitionalEquality where

open import Data.Product
open import Prelude
open import Presheaves
open import CloTT.Structure.Contexts
open import CloTT.Structure.Types
open import CloTT.Structure.Terms

def-eq : {n : ℕ} (Γ : Ctx n) (A : Ty n) (s t : Tm Γ A) → Set
def-eq {n} Γ A (s , _) (t , _) = (Δ : ClockCtx n) (x : _) → s Δ x ≡ t Δ x

eq-is-def-eq : {n : ℕ} (Γ : Ctx n) (A : Ty n) (s t : Tm Γ A) → s ≡ t → def-eq Γ A s t
eq-is-def-eq Γ A s s refl Δ x = refl

def-eq-is-eq : {n : ℕ} (Γ : Ctx n) (A : Ty n) (s t : Tm Γ A) → def-eq Γ A s t → s ≡ t
def-eq-is-eq Γ A s t p =
  Σ≡-uip
    (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
    (funext (λ Δ → funext (λ x → p Δ x)))
