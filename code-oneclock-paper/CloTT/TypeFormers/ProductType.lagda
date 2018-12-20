\AgdaHide{
\begin{code}
module CloTT.TypeFormers.ProductType where

open import Data.Product
open import Data.Unit
open import Prelude
open import Presheaves
open import CloTT.Structure

open PSh
\end{code}
}

\begin{code}
_⊗_ : {b : tag} (A B : Ty b) → Ty b
_⊗_ {set} A B = A × B
_⊗_ {tot} A B = Prod A B
\end{code}

\begin{code}
pair : {b : tag} (Γ : Ctx b) (A B : Ty b) (x : Tm Γ A) (y : Tm Γ B)
  → Tm Γ (A ⊗ B)
pair {set} Γ A B x y t = x t , y t
proj₁ (pair {tot} Γ A B (x , p) (y , q)) i t = (x i t) , (y i t)
proj₂ (pair {tot} Γ A B (x , p) (y , q)) i j t =
  begin
    (Mor A i j (x i t) , Mor B i j (y i t))
  ≡⟨ cong (λ z → (z , _)) (p i j t) ⟩
    (x j (Mor Γ i j t) , Mor B i j (y i t))
  ≡⟨ cong (λ z → (_ , z)) (q i j t) ⟩
    (x j (Mor Γ i j t) , y j (Mor Γ i j t))
  ∎
\end{code}

\begin{code}
pr₁ : {b : tag} (Γ : Ctx b) (A B : Ty b) → Tm Γ (A ⊗ B) → Tm Γ A
pr₁ {set} Γ A B x t = proj₁ (x t)
proj₁ (pr₁ {tot} Γ A B (x , p)) i t = proj₁ (x i t)
proj₂ (pr₁ {tot} Γ A B (x , p)) i j t =
  begin
    Mor A i j (proj₁ (x i t))
  ≡⟨ cong proj₁ (p i j t) ⟩
    proj₁ (x j (Mor Γ i j t))
  ∎
\end{code}

\begin{code}
pr₂ : {b : tag} (Γ : Ctx b) (A B : Ty b) → Tm Γ (A ⊗ B) → Tm Γ B
pr₂ {set} Γ A B x t = proj₂ (x t)
proj₁ (pr₂ {tot} Γ A B (x , p)) i t = proj₂ (x i t)
proj₂ (pr₂ {tot} Γ A B (x , p)) i j t =
  begin
    Mor B i j (proj₂ (x i t))
  ≡⟨ cong proj₂ (p i j t) ⟩
    proj₂ (x j (Mor Γ i j t))
  ∎
\end{code}
