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
from \IC{∅} into contexts from \IC{κ}, is given by the constant
presheaf construction.

\begin{code}
WC : Ctx ∅ → Ctx κ
WC Γ = Const Γ
\end{code}

\AgdaHide{
\begin{code}
WC-fun : (Γ : Ctx ∅) (A : Ty ∅) → Tm Γ A → Tm (WC Γ) (WC A)
nat-map (WC-fun Γ A t) _ = t
nat-com (WC-fun Γ A t) _ _ _ = refl
\end{code}

\begin{code}
WC-unfun : (Γ : Ctx ∅) (A : Ty ∅) → Tm (WC Γ) (WC A) → Tm Γ A 
WC-unfun Γ A t = nat-map t ∞
\end{code}
}
