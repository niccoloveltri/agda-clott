\AgdaHide{
\begin{code}
module CloTT.TypeFormers.UnitType where

open import Data.Product
open import Data.Unit
open import Prelude
open import Presheaves
open import CloTT.Structure
\end{code}
}

\begin{code}
Unit : {b : tag} → Ty b
Unit {set} = ⊤
Unit {tot} = Terminal

⋆ : {b : tag} (Γ : Ctx b) → Tm Γ Unit
⋆ {set} Γ x = tt
proj₁ (⋆ {tot} Γ) i x = tt
proj₂ (⋆ {tot} Γ) i j x = refl

Unit-rec : {b : tag} (Γ : Ctx b) (A : Ty b)
  → Tm Γ A → Tm (Γ ,, Unit) A
Unit-rec {set} Γ A t x = t (proj₁ x)
proj₁ (Unit-rec {tot} Γ A t) i x = proj₁ t i (proj₁ x)
proj₂ (Unit-rec {tot} Γ A t) i j x =
  begin
    PSh.Mor A i j (proj₁ t i (proj₁ x))
  ≡⟨ proj₂ t i j (proj₁ x) ⟩
    proj₁ t j (proj₁ (ProdMor Γ Terminal i j x))
  ∎
\end{code}
