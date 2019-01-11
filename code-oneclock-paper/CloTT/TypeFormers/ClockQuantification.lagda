\AgdaHide{
\begin{code}
module CloTT.TypeFormers.ClockQuantification where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers.WeakenClock
open import CloTT.TypeFormers.FunctionType
open PSh
\end{code}
}

Following \cite{Mogelberg14}, clock quantification is modelled by
taking limits. 

\begin{code}
□ : Ty tot → Ty set
□ A = Σ[ f ∈ ((i : Size) → Obj A i) ]
        ((i : Size) (j : Size< (↑ i))
          → Mor A i j (f i) ≡ f j)
\end{code}

Semantically, clock quantification \F{□} is right adjoint to context
weakening \F{WC}. In other words, the types \F{Tm} (\F{WC} \Ar{Γ})
\Ar{A} and \F{Tm} \Ar{Γ} (\F{□} \Ar{A}) are isomorphic. The function
underlying the isomorphism is \F{box} and its inverse is \F{unbox}.


\begin{code}
box : (Γ : Ctx set) (A : Ty tot) (t : Tm (WC Γ) A) → Tm Γ (□ A)
proj₁ (box Γ A (t , p) x) i = t i x
proj₂ (box Γ A (t , p) x) i j = p i j x
\end{code}

\begin{code}
unbox : (Γ : Ctx set) (A : Ty tot) (t : Tm Γ (□ A)) → Tm (WC Γ) A
proj₁ (unbox Γ A t) i x = proj₁ (t x) i
proj₂ (unbox Γ A t) i j x = proj₂ (t x) i j
\end{code}
