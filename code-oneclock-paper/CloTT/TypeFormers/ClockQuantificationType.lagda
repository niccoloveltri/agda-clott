\AgdaHide{
\begin{code}
module CloTT.TypeFormers.ClockQuantificationType where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers.WeakenClock
open import CloTT.TypeFormers.ClockQuantification
\end{code}
}

\begin{code}
box : (Γ : Ctx set) (A : Ty tot) (t : Tm tot (WC Γ) A) → Tm set Γ (□ A)
proj₁ (box Γ A (t , p) x) i = t i x
proj₂ (box Γ A (t , p) x) i j = p i j x
\end{code}

\begin{code}
unbox : (Γ : Ctx set) (A : Ty tot) (t : Tm set Γ (□ A)) → Tm tot (WC Γ) A
proj₁ (unbox Γ A t) i x = proj₁ (t x) i
proj₂ (unbox Γ A t) i j x = proj₂ (t x) i j
\end{code}

\begin{code}
box-beta : {Γ : Ctx set} {A : Ty tot} (t : Tm tot (WC Γ) A)
  → def-eq (WC Γ) A (unbox Γ A (box Γ A t)) t
box-beta t i x = refl
\end{code}

\begin{code}
box-eta : {Γ : Ctx set} {A : Ty tot} (t : Tm set Γ (□ A))
  → def-eq Γ (□ A) (box Γ A (unbox Γ A t)) t
box-eta t i = refl 
\end{code}
