\AgdaHide{
\begin{code}
module CloTT.TypeFormers.WeakenClock where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import Presheaves.Const
open import CloTT.Structure
\end{code}
}

\begin{code}
WC : Ty set → Ty tot
WC A = Const A
\end{code}

\AgdaHide{
\begin{code}
WC-fun : (Γ : Ctx set) (A : Ty set) → Tm Γ A → Tm (WC Γ) (WC A)
proj₁ (WC-fun Γ A t) _ = t
proj₂ (WC-fun Γ A t) _ _ _ = refl
\end{code}

\begin{code}
WC-unfun : (Γ : Ctx set) (A : Ty set) → Tm (WC Γ) (WC A) → Tm Γ A 
WC-unfun Γ A (t , p) = t ∞
\end{code}
}
