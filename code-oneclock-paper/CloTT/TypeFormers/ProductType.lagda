\AgdaHide{
\begin{code}
module CloTT.TypeFormers.ProductType where

open import Data.Product
open import Data.Unit
open import Prelude
open import Presheaves
open import CloTT.Structure
\end{code}
}

\begin{code}
_⊗_ : {b : tag} (A B : Ty b) → Ty b
_⊗_ {set} A B = A × B
_⊗_ {tot} A B = Prod A B
\end{code}

\begin{code}
pair : {b : tag} (Γ : Ctx b) (A B : Ty b) (x : Tm b Γ A) (y : Tm b Γ B)
  → Tm b Γ (A ⊗ B)
pair {set} Γ A B x y t = x t , y t
proj₁ (pair {tot} Γ A B (x , p) (y , q)) i t = (x i t) , (y i t)
proj₂ (pair {tot} Γ A B (x , p) (y , q)) i j t =
  begin
    (PSh.Mor A i j (x i t) , PSh.Mor B i j (y i t))
  ≡⟨ cong (λ z → (z , _)) (p i j t) ⟩
    (x j (PSh.Mor Γ i j t) , PSh.Mor B i j (y i t))
  ≡⟨ cong (λ z → (_ , z)) (q i j t) ⟩
    (x j (PSh.Mor Γ i j t) , y j (PSh.Mor Γ i j t))
  ∎
\end{code}

\begin{code}
pr₁ : {b : tag} (Γ : Ctx b) (A B : Ty b) → Tm b Γ (A ⊗ B) → Tm b Γ A
pr₁ {set} Γ A B x t = proj₁ (x t)
proj₁ (pr₁ {tot} Γ A B (x , p)) i t = proj₁ (x i t)
proj₂ (pr₁ {tot} Γ A B (x , p)) i j t = cong proj₁ (p i j t)
\end{code}

\begin{code}
pr₂ : {b : tag} (Γ : Ctx b) (A B : Ty b) → Tm b Γ (A ⊗ B) → Tm b Γ B
pr₂ {set} Γ A B x t = proj₂ (x t)
proj₁ (pr₂ {tot} Γ A B (x , p)) i t = proj₂ (x i t)
proj₂ (pr₂ {tot} Γ A B (x , p)) i j t = cong proj₂ (p i j t)
\end{code}

\begin{code}
pr₁-pair : {b : tag} (Γ : Ctx b) (A B : Ty b) (x : Tm b Γ A) (y : Tm b Γ B)
  → def-eq Γ A
           (pr₁ Γ A B (pair Γ A B x y))
           x
pr₁-pair {set} Γ A B x y t = refl
pr₁-pair {tot} Γ A B x y i t = refl
\end{code}

\begin{code}
pr₂-pair : {b : tag} (Γ : Ctx b) (A B : Ty b) (x : Tm b Γ A) (y : Tm b Γ B)
  → def-eq Γ B
           (pr₂ Γ A B (pair Γ A B x y))
           y
pr₂-pair {set} Γ A B x y t = refl
pr₂-pair {tot} Γ A B x y i t = refl
\end{code}

\begin{code}
prod-eta : {b : tag} (Γ : Ctx b) (A B : Ty b) (x : Tm b Γ (A ⊗ B))
  → def-eq Γ (A ⊗ B)
           (pair Γ A B (pr₁ Γ A B x) (pr₂ Γ A B x)) 
           x
prod-eta {set} Γ A B x t = refl
prod-eta {tot} Γ A B x i t = refl
\end{code}
