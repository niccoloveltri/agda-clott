\AgdaHide{
\begin{code}
module CloTT.Structure.Terms where

open import Data.Product
open import Prelude
open import CloTT.Structure.ClockContexts
open import CloTT.Structure.Contexts
open import CloTT.Structure.Types

open PSh
\end{code}
}

A term of type $A$ in context $\Gamma$, is just a morphism from $A$ to $\Gamma$.
Again we need to distinguish two cases, because morphisms between sets are something different than morphisms between presheaves.
For sets, we just use functions.
For presheaves, we use natural transformations instead.

\begin{code}
Tm : {b : tag} (Γ : Ctx b) (A : Ty b) → Set
Tm {set} Γ A = Γ → A
Tm {tot} Γ A = 
  Σ[ θ ∈ ((i : Size) → Obj Γ i → Obj A i) ]
    ((i : Size) (j : Size< (↑ i)) (x : Obj Γ i)
      → Mor A i j (θ i x) ≡ θ j (Mor Γ i j x))
\end{code}

A natural transformation consists of a component
