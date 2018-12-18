\AgdaHide{
\begin{code}
module CloTT.TypeFormers.WeakenClock where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure

module _ (A : Ty set) where
\end{code}
}
  \begin{code}
  WCObj : Size → Set
  WCObj _ = A
  \end{code}

  \begin{code}
  WCMor : (i : Size) (j : Size< (↑ i))
    → WCObj i → WCObj j
  WCMor _ _ x = x
  \end{code}

  \begin{code}
  WCMorId : {i : Size} {x : WCObj i}
    → WCMor i i x ≡ x
  WCMorId = refl
  \end{code}
  
  \begin{code}
  WCMorComp : {i : Size} {j : Size< (↑ i)} {k : Size< (↑ j)}
    {x : WCObj i}
    → WCMor i k x ≡ WCMor j k (WCMor i j x)
  WCMorComp = refl
  \end{code}

  \begin{code}
  WC : Ty tot
  WC = record
    { Obj = WCObj
    ; Mor = WCMor
    ; MorId = WCMorId
    ; MorComp = WCMorComp
    }
  \end{code}

\begin{code}
WC-fun : (Γ : Ctx set) (A : Ty set) → Tm set Γ A → Tm tot (WC Γ) (WC A)
proj₁ (WC-fun Γ A t) _ = t
proj₂ (WC-fun Γ A t) _ _ _ = refl
\end{code}

\begin{code}
WC-unfun : (Γ : Ctx set) (A : Ty set) → Tm tot (WC Γ) (WC A) → Tm set Γ A 
WC-unfun Γ A (t , p) = t ∞
\end{code}
