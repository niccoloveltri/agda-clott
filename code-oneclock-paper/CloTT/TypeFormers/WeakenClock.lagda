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

Weakening a context is a map which takes a context in the empty clock
context and maps it to one in the clock context with just one clock.
Concretely, we define a presheaf using a type, and we do this via the constant presheaf.

\begin{code}
⇑ : SemCtx ∅ → SemCtx κ
⇑ Γ = Const Γ
\end{code}

\AgdaHide{
\begin{code}
sem-up : (Γ : SemCtx ∅) (A : SemTy ∅) → SemTm Γ A → SemTm (⇑ Γ) (⇑ A)
nat-map (sem-up Γ A t) _ = t
nat-com (sem-up Γ A t) _ _ _ = refl
\end{code}

\begin{code}
sem-down : (Γ : SemCtx ∅) (A : SemTy ∅) → SemTm (⇑ Γ) (⇑ A) → SemTm Γ A 
sem-down Γ A t = nat-map t ∞
\end{code}
}
