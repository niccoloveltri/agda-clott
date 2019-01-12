\AgdaHide{
\begin{code}
module CloTT.TypeFormers.UnitType where

open import Data.Product
open import Data.Unit
open import Prelude
open import Presheaves
open import CloTT.Structure

open NatTrans
open PSh
\end{code}
}

\begin{code}
Unit : {b : ClockContext} → Ty b
Unit {∅} = ⊤
Unit {κ} = Terminal

⋆ : {b : ClockContext} (Γ : Ctx b) → Tm Γ Unit
⋆ {∅} Γ x = tt
nat-map (⋆ {κ} Γ) i x = tt
nat-com (⋆ {κ} Γ) i j x = refl

Unit-rec : {b : ClockContext} (Γ : Ctx b) (A : Ty b)
  → Tm Γ A → Tm (Γ ,, Unit) A
Unit-rec {∅} Γ A t x = t (proj₁ x)
nat-map (Unit-rec {κ} Γ A t) i x = nat-map t i (proj₁ x)
nat-com (Unit-rec {κ} Γ A t) i j x =
  begin
    Mor A i j (nat-map t i (proj₁ x))
  ≡⟨ nat-com t i j (proj₁ x) ⟩
    nat-map t j (proj₁ (ProdMor Γ Terminal i j x))
  ∎
\end{code}
