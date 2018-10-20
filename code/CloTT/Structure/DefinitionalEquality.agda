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
