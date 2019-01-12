\AgdaHide{
\begin{code}
module CloTT.TypeFormers.WeakenClock where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import Presheaves.Const
open import CloTT.Structure

open NatTrans
\end{code}
}

We now show how to model context weakening and clock quantification.
The weakening of a context, i.e. the process of embedding contexts
from \IC{set} into contexts from \IC{tot}, is given by the constant
presheaf construction.

\begin{code}
WC : Ctx set → Ctx tot
WC Γ = Const Γ
\end{code}

\AgdaHide{
\begin{code}
WC-fun : (Γ : Ctx set) (A : Ty set) → Tm Γ A → Tm (WC Γ) (WC A)
nat-map (WC-fun Γ A t) _ = t
nat-com (WC-fun Γ A t) _ _ _ = refl
\end{code}

\begin{code}
WC-unfun : (Γ : Ctx set) (A : Ty set) → Tm (WC Γ) (WC A) → Tm Γ A 
WC-unfun Γ A t = nat-map t ∞
\end{code}
}
