\AgdaHide{
\begin{code}
module CloTT.Structure.Subst where

open import Data.Product
open import Prelude
open import CloTT.Structure.Contexts
open import CloTT.Structure.ContextOperations
open import CloTT.Structure.Types
open import CloTT.Structure.Terms
\end{code}
}

\begin{code}
subst-Tm : {b : tag} (Γ : Ctx b) (A B : Ty b)
  → (t : Tm (Γ ,, A) B) (α : Tm Γ A)
  → Tm Γ B
subst-Tm {set} Γ A B t α x = t (x , α x)
proj₁ (subst-Tm {tot} Γ A B (t , p) (α , q)) i x = t i (x , α i x)
proj₂ (subst-Tm {tot} Γ A B (t , p) (α , q)) i j x =
  begin
    PSh.Mor B i j (t i (x , α i x))
  ≡⟨ p i j (x , α i x) ⟩
    t j (PSh.Mor (Γ ,, A) i j (x , α i x))
  ≡⟨ cong (λ z → t j (_ , z)) (q i j x) ⟩
    t j (PSh.Mor Γ i j x , α j (PSh.Mor Γ i j x))
  ∎
\end{code}
