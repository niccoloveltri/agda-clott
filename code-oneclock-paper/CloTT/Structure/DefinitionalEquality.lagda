\AgdaHide{
\begin{code}
module CloTT.Structure.DefinitionalEquality where

open import Data.Product
open import Prelude
open import Presheaves
open import CloTT.Structure.Contexts
open import CloTT.Structure.Types
open import CloTT.Structure.Terms
\end{code}

\begin{code}
def-eq : {b : tag} (Γ : Ctx b) (A : Ty b) (s t : Tm b Γ A) → Set
def-eq {set} Γ A s t = (x : _) → s x ≡ t x
def-eq {tot} Γ A (s , _) (t , _) = (i : Size) (x : _) → s i x ≡ t i x
\end{code}

\begin{code}
trans-def-eq : {b : tag} {Γ : Ctx b} {A : Ty b} {s t u : Tm b Γ A}
  → def-eq Γ A s t → def-eq Γ A t u → def-eq Γ A s u
trans-def-eq {set} p q γ = trans (p γ) (q γ)
trans-def-eq {tot} p q i γ = trans (p i γ) (q i γ)  
\end{code}
