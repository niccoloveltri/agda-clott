\AgdaHide{
\begin{code}
module CloTT.TypeFormers.ClockQuantification where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure
\end{code}
}

\begin{code}
□ : Ty tot → Ty set
□ A = 
    Σ ((i : Size) → PSh.Obj A i)
      (λ x → (i : Size) (j : Size< (↑ i))
        → PSh.Mor A i j (x i) ≡ x j)
\end{code}
