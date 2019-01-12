\AgdaHide{
\begin{code}
module CloTT.TypeFormers.ProductType where

open import Data.Product
open import Data.Unit
open import Prelude
open import Presheaves
open import CloTT.Structure

open PSh
open NatTrans
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
nat-map (pair {tot} Γ A B x y) i t = (nat-map x i t) , (nat-map y i t)
nat-com (pair {tot} Γ A B x y) i j t =
  begin
    (Mor A i j (nat-map x i t) , Mor B i j (nat-map y i t))
  ≡⟨ cong (λ z → (z , _)) (nat-com x i j t) ⟩
    (nat-map x j (Mor Γ i j t) , Mor B i j (nat-map y i t))
  ≡⟨ cong (λ z → (_ , z)) (nat-com y i j t) ⟩
    (nat-map x j (Mor Γ i j t) , nat-map y j (Mor Γ i j t))
  ∎
\end{code}

\begin{code}
pr₁ : {b : tag} (Γ : Ctx b) (A B : Ty b) → Tm Γ (A ⊗ B) → Tm Γ A
pr₁ {set} Γ A B x t = proj₁ (x t)
nat-map (pr₁ {tot} Γ A B x) i t = proj₁ (nat-map x i t)
nat-com (pr₁ {tot} Γ A B x) i j t =
  begin
    Mor A i j (proj₁ (nat-map x i t))
  ≡⟨ cong proj₁ (nat-com x i j t) ⟩
    proj₁ (nat-map x j (Mor Γ i j t))
  ∎
\end{code}

\begin{code}
pr₂ : {b : tag} (Γ : Ctx b) (A B : Ty b) → Tm Γ (A ⊗ B) → Tm Γ B
pr₂ {set} Γ A B x t = proj₂ (x t)
nat-map (pr₂ {tot} Γ A B x) i t = proj₂ (nat-map x i t)
nat-com (pr₂ {tot} Γ A B x) i j t =
  begin
    Mor B i j (proj₂ (nat-map x i t))
  ≡⟨ cong proj₂ (nat-com x i j t) ⟩
    proj₂ (nat-map x j (Mor Γ i j t))
  ∎
\end{code}
