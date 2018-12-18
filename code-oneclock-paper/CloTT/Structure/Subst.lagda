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
subst-Tm : {b : tag} {Γ : Ctx b} {A B : Ty b}
  → (t : Tm b (Γ ,, A) B) (x : Tm b Γ A)
  → Tm b Γ B
subst-Tm {set} t x y = t (y , (x y))
proj₁ (subst-Tm {tot} (t , p) (x , q)) i y = t i (y , x i y)
proj₂ (subst-Tm {tot} {Γ} {A} {B} (t , p) (x , q)) i j y =
  begin
    PSh.Mor B i j (t i (y , x i y))
  ≡⟨ p i j (y , x i y) ⟩
    t j (PSh.Mor (Γ ,, A) i j (y , x i y))
  ≡⟨ cong (λ z → t j (_ , z)) (q i j y) ⟩
    t j (PSh.Mor Γ i j y , x j (PSh.Mor Γ i j y))
  ∎
\end{code}
