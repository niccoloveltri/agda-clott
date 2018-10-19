module DefinitionalEquality where

open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Basics
open import ClockContexts
open import Contexts
open import Presheaves
open import Types
open import Terms

def-eq : {n : ℕ} (Γ : Ctx n) (A : Ty n) (s t : Tm Γ A) → Set
def-eq {n} Γ A (s , _) (t , _) = (Δ : ClockCtx n) (x : _) → s Δ x ≡ t Δ x
