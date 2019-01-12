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
open NatTrans
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
nat-map (inl {tot} Γ A B x) Δ y = inj₁ (nat-map x Δ y)
nat-com (inl {tot}Γ A B x) Δ Δ' y = 
  begin
    inj₁ (Mor A Δ Δ' (nat-map x Δ y))
  ≡⟨ cong inj₁ (nat-com x Δ Δ' y) ⟩
    inj₁ (nat-map x Δ' (Mor Γ Δ Δ' y))
  ∎
\end{code}

\begin{code}
inr : {b : tag} (Γ : Ctx b) (A B : Ty b) (x : Tm Γ B) → Tm Γ (A ⊕ B)
inr {set} Γ A B t x = inj₂ (t x)
nat-map (inr {tot} Γ A B x) Δ y = inj₂ (nat-map x Δ y)
nat-com (inr {tot} Γ A B x) Δ Δ' y =
  begin
    inj₂ (Mor B Δ Δ' (nat-map x Δ y))
  ≡⟨ cong inj₂ (nat-com x Δ Δ' y) ⟩ 
    inj₂ (nat-map x Δ' (Mor Γ Δ Δ' y))
  ∎
\end{code}

\begin{code}
sum-rec : {b : tag} (Γ : Ctx b) (A B C : Ty b)
          (left : Tm (Γ ,, A) C) (right : Tm (Γ ,, B) C)
          → Tm (Γ ,, (A ⊕ B)) C
sum-rec {set} Γ A B C left right (x , inj₁ l) = left (x , l)
sum-rec {set} Γ A B C left right (x , inj₂ r) = right (x , r)          
nat-map (sum-rec {tot} Γ A B C left right) i (x , inj₁ l) = nat-map left i (x , l)
nat-com (sum-rec {tot} Γ A B C left right) i j (x , inj₁ l) =
  begin
    Mor C i j (nat-map left i (x , l))
  ≡⟨ nat-com left i j (x , l) ⟩
    nat-map left j (Mor Γ i j x , Mor A i j l)
  ∎ 
nat-map (sum-rec {tot} Γ A B C left right) i (x , inj₂ r) = nat-map right i (x , r)
nat-com (sum-rec {tot} Γ A B C left right) i j (x , inj₂ r) =
  begin
     Mor C i j (nat-map right i (x , r))
   ≡⟨ nat-com right i j (x , r) ⟩
     nat-map right j (Mor Γ i j x , Mor B i j r)
   ∎
\end{code}
