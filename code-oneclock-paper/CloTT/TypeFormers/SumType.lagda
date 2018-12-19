\AgdaHide{
\begin{code}
module CloTT.TypeFormers.SumType where

open import Data.Product
open import Data.Sum
open import Data.Unit
open import Prelude
open import Presheaves
open import CloTT.Structure

open PSh
\end{code}
}

\begin{code}
_⊕_ : {b : tag} (A B : Ty b) → Ty b 
_⊕_ {set} A B = A ⊎ B
_⊕_ {tot} A B = Sum A B
\end{code}

\begin{code}
inl : {b : tag} (Γ : Ctx b) (A B : Ty b) (x : Tm Γ A) → Tm Γ (A ⊕ B)
inl {set} Γ A B t x = inj₁ (t x)
proj₁ (inl {tot} Γ A B (x , p)) Δ y = inj₁ (x Δ y)
proj₂ (inl {tot}Γ A B (x , p)) Δ Δ' y =
  begin
    inj₁ (Mor A Δ Δ' (x Δ y))
  ≡⟨ cong inj₁ (p Δ Δ' y) ⟩
    inj₁ (x Δ' (Mor Γ Δ Δ' y))
  ∎
\end{code}

\begin{code}
inr : {b : tag} (Γ : Ctx b) (A B : Ty b) (x : Tm Γ B) → Tm Γ (A ⊕ B)
inr {set} Γ A B t x = inj₂ (t x)
proj₁ (inr {tot} Γ A B (x , p)) Δ y = inj₂ (x Δ y)
proj₂ (inr {tot} Γ A B (x , p)) Δ Δ' y =
  begin
    inj₂ (Mor B Δ Δ' (x Δ y))
  ≡⟨ cong inj₂ (p Δ Δ' y) ⟩ 
    inj₂ (x Δ' (Mor Γ Δ Δ' y))
  ∎
\end{code}

\begin{code}
sum-rec : {b : tag} (Γ : Ctx b) (A B C : Ty b)
          (left : Tm (Γ ,, A) C) (right : Tm (Γ ,, B) C)
          → Tm (Γ ,, (A ⊕ B)) C
sum-rec {set} Γ A B C left right (x , inj₁ l) = left (x , l)
sum-rec {set} Γ A B C left right (x , inj₂ r) = right (x , r)          
proj₁ (sum-rec {tot} Γ A B C (left , p) (right , q)) i (x , inj₁ l) = left i (x , l)
proj₂ (sum-rec {tot} Γ A B C (left , p) (right , q)) i j (x , inj₁ l) =
  begin
    Mor C i j (left i (x , l))
  ≡⟨ p i j (x , l) ⟩
    left j (Mor Γ i j x , Mor A i j l)
  ∎ 
proj₁ (sum-rec {tot} Γ A B C (left , p) (right , q)) i (x , inj₂ r) = right i (x , r)
proj₂ (sum-rec {tot} Γ A B C (left , p) (right , q)) i j (x , inj₂ r) =
  begin
     Mor C i j (right i (x , r))
   ≡⟨ q i j (x , r) ⟩
     right j (Mor Γ i j x , Mor B i j r)
   ∎
\end{code}

\begin{code}
sum-rec-inl : {b : tag} (Γ : Ctx b) (A B C : Ty b)
  → (l : Tm (Γ ,, A) C) (r : Tm (Γ ,, B) C)
  → (x : Tm Γ A)
  → def-eq Γ C
           (sem-sub _ _ _ (sum-rec _ _ _ C l r) (sem-subst-tm _ _ _ (sem-idsub Γ) (inl Γ A B x)))
           (sem-sub _ _ _ l (sem-subst-tm _ _ _ (sem-idsub Γ) x))
sum-rec-inl {set} Γ A B C l r x z = refl
sum-rec-inl {tot} Γ A B C l r x i z = refl
\end{code}

\begin{code}
sum-rec-inr : {b : tag} (Γ : Ctx b) (A B C : Ty b)
  → (l : Tm (Γ ,, A) C) (r : Tm (Γ ,, B) C)
  → (x : Tm Γ B)
  → def-eq Γ C
           (sem-sub _ _ _ (sum-rec _ _ _ C l r) (sem-subst-tm _ _ _ (sem-idsub Γ) (inr Γ A B x)))
           (sem-sub _ _ _ r (sem-subst-tm _ _ _ (sem-idsub Γ) x))
sum-rec-inr {set} Γ A B C l r x z = refl
sum-rec-inr {tot} Γ A B C l r x i z = refl
\end{code}
