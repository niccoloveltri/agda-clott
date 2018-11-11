{-
A Term is a natural transformation.
-}
module CloTT.Structure.Terms where

open import Data.Product
open import Prelude
open import CloTT.Structure.Contexts
open import CloTT.Structure.Types

Tm : (b : Bool)(Γ : Ctx b) (A : Ty b) → Set
Tm set Γ A = Γ → A
Tm tot Γ A = 
  Σ ((i : Size) → PSh.Obj Γ i → PSh.Obj A i)
         (λ f → (i : Size) (j : Size≤ i) (x : PSh.Obj Γ i)
              → PSh.Mor A i j (f i x) ≡ f j (PSh.Mor Γ i j x))
  
