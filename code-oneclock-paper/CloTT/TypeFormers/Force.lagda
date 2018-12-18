\AgdaHide{
\begin{code}
module CloTT.TypeFormers.Force where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers.Later
open import CloTT.TypeFormers.ClockQuantification
\end{code}
}

\begin{code}
force-tm : (Γ : Ctx set) (A : Ty tot) (t : Tm set Γ (□ (▻ A))) → Tm set Γ (□ A)
proj₁ (force-tm Γ A t x) j = proj₁ (proj₁ (t x) ∞) [ j ]
proj₂ (force-tm Γ A t x) i j =
  begin
    PSh.Mor A i j (proj₁ (proj₁ (t x) ∞) [ i ])
  ≡⟨ proj₂ (proj₁ (t x) ∞) [ i ] [ j ] ⟩
    proj₁ (proj₁ (t x) ∞) [ j ]
  ∎
\end{code}
