\AgdaHide{
\begin{code}
module CloTT.TypeFormers.TypeIsomorphisms where

open import Data.Product
open import Data.Sum
open import Prelude
open import CloTT.Structure
open import CloTT.TypeFormers.ClockQuantification public
open import CloTT.TypeFormers.Force public
open import CloTT.TypeFormers.FunctionType public
open import CloTT.TypeFormers.Later public
open import CloTT.TypeFormers.LaterType public
open import CloTT.TypeFormers.ProductType public
open import CloTT.TypeFormers.SumType public
open import CloTT.TypeFormers.WeakenClock public

open PSh
\end{code}
}

\begin{code}
□const-tm : (Γ : Ctx set) (A : Ty set) → Tm Γ (□ (WC A) ⇒ A)
□const-tm Γ A γ (x , _) = x ∞

module _ (Γ : Ctx set) (A : Ty tot) (B : Ty tot) where
  sum-lem₁ : (t : □ (A ⊕ B)) (x : Obj A ∞)
    → proj₁ t ∞ ≡ inj₁ x
    → Σ (□ A) (λ s → (i : Size) → proj₁ t i ≡ inj₁ (proj₁ s i))
  proj₁ (proj₁ (sum-lem₁ (t , p) x q)) i = Mor A ∞ i x
  proj₂ (proj₁ (sum-lem₁ (t , p) x q)) i j = sym (MorComp A)
  proj₂ (sum-lem₁ (t , p) x q) i =
    begin
      t i
    ≡⟨ sym (p ∞ i) ⟩
      Mor (A ⊕ B) ∞ i (t ∞)
    ≡⟨ cong (Mor (A ⊕ B) ∞ i) q ⟩
      inj₁ (Mor A ∞ i x)
    ∎

  sum-lem₂ : (t : □ (A ⊕ B)) (x : Obj B ∞)
    → proj₁ t ∞ ≡ inj₂ x
    → Σ (□ B) (λ s → (i : Size) → proj₁ t i ≡ inj₂ (proj₁ s i))
  proj₁ (proj₁ (sum-lem₂ (t , p) x q)) i = Mor B ∞ i x
  proj₂ (proj₁ (sum-lem₂ (t , p) x q)) i j = sym (MorComp B)
  proj₂ (sum-lem₂ (t , p) x q) i =
    begin
      t i
    ≡⟨ sym (p ∞ i) ⟩
      Mor (A ⊕ B) ∞ i (t ∞)
    ≡⟨ cong (Mor (A ⊕ B) ∞ i) q ⟩
      inj₂ (Mor B ∞ i x)
    ∎
  
  □sum-tm : Tm Γ (□ (A ⊕ B) ⇒ (□ A ⊕ □ B))
  □sum-tm γ (t , p) with t ∞ | inspect t ∞
  □sum-tm γ (t , p) | inj₁ x | [ eq ] = inj₁ (proj₁ (sum-lem₁ (t , p) x eq))
  □sum-tm γ (t , p) | inj₂ y | [ eq ] = inj₂ (proj₁ (sum-lem₂ (t , p) y eq))
\end{code}
