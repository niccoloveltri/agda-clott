\AgdaHide{
\begin{code}
module CloTT.TypeFormers.SumType where

open import Data.Product
open import Data.Sum
open import Data.Unit
open import Prelude
open import Presheaves
open import CloTT.Structure
\end{code}

\begin{code}
_⊕_ : {b : tag} (A B : Ty b) → Ty b 
_⊕_ {set} A B = A ⊎ B
_⊕_ {tot} A B = Sum A B
\end{code}

\begin{code}
inl : {b : tag} (Γ : Ctx b) (A B : Ty b) (x : Tm b Γ A) → Tm b Γ (A ⊕ B)
inl {set} Γ A B t x = inj₁ (t x)
proj₁ (inl {tot} Γ A B (x , p)) Δ y = inj₁ (x Δ y)
proj₂ (inl {tot}Γ A B (x , p)) Δ Δ' y =
  begin
    inj₁ (PSh.Mor A Δ Δ' (x Δ y))
  ≡⟨ cong inj₁ (p Δ Δ' y) ⟩
    inj₁ (x Δ' (PSh.Mor Γ Δ Δ' y))
  ∎
\end{code}

\begin{code}
inr : {b : tag} (Γ : Ctx b) (A B : Ty b) (x : Tm b Γ B) → Tm b Γ (A ⊕ B)
inr {set} Γ A B t x = inj₂ (t x)
proj₁ (inr {tot} Γ A B (x , p)) Δ y = inj₂ (x Δ y)
proj₂ (inr {tot} Γ A B (x , p)) Δ Δ' y =
  begin
    inj₂ (PSh.Mor B Δ Δ' (x Δ y))
  ≡⟨ cong inj₂ (p Δ Δ' y) ⟩ 
    inj₂ (x Δ' (PSh.Mor Γ Δ Δ' y))
  ∎
\end{code}

\begin{code}
sum-rec : {b : tag} (Γ : Ctx b) (A B C : Ty b)
          (left : Tm b (Γ ,, A) C) (right : Tm b (Γ ,, B) C)
          → Tm b (Γ ,, (A ⊕ B)) C
sum-rec {set} Γ A B C left right (x , inj₁ l) = left (x , l)
sum-rec {set} Γ A B C left right (x , inj₂ r) = right (x , r)          
proj₁ (sum-rec {tot} Γ A B C (left , p) (right , q)) i (x , inj₁ l) = left i (x , l)
proj₁ (sum-rec {tot} Γ A B C (left , p) (right , q)) i (x , inj₂ r) = right i (x , r)
proj₂ (sum-rec {tot} Γ A B C (left , p) (right , q)) i j (x , inj₁ l) = p i j (x , l)
proj₂ (sum-rec {tot} Γ A B C (left , p) (right , q)) i j (x , inj₂ r) = q i j (x , r)
\end{code}

\begin{code}
sum-rec-inl : {b : tag} (Γ : Ctx b) (A B C : Ty b)
  → (left : Tm b (Γ ,, A) C) (right : Tm b (Γ ,, B) C)
  → (x : Tm b Γ A)
  → def-eq Γ C
           (subst-Tm (sum-rec Γ A B C left right) (inl Γ A B x))
           (subst-Tm left x)
sum-rec-inl {set} Γ A B C left right x z = refl
sum-rec-inl {tot} Γ A B C (left , p) (right , q) (x , r) i z = refl
\end{code}

\begin{code}
sum-rec-inr : {b : tag} (Γ : Ctx b) (A B C : Ty b)
  → (left : Tm b (Γ ,, A) C) (right : Tm b (Γ ,, B) C)
  → (x : Tm b Γ B)
  → def-eq Γ C
           (subst-Tm (sum-rec Γ A B C left right) (inr Γ A B x))
           (subst-Tm right x)
sum-rec-inr {set} Γ A B C left right x z = refl
sum-rec-inr {tot} Γ A B C (left , p) (right , q) (x , r) i z = refl
\end{code}
