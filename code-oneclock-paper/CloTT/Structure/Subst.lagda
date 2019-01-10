\AgdaHide{
\begin{code}
module CloTT.Structure.Subst where

open import Data.Unit
open import Data.Product
open import Prelude
open import CloTT.Structure.ClockContexts
open import CloTT.Structure.Contexts
open import CloTT.Structure.ContextOperations
open import CloTT.Structure.Types
open import CloTT.Structure.Terms

open PSh
\end{code}
}

\begin{code}
sem-subst : {b : tag} (Γ Γ' : Ctx b) → Set
sem-subst {set} Γ Γ' = Γ → Γ'
sem-subst {tot} Γ Γ' =
  Σ ((i : Size) → Obj Γ i → Obj Γ' i)
    (λ f → (i : Size) (j : Size< (↑ i)) (x : Obj Γ i) →
           f j (Mor Γ i j x) ≡ Mor Γ' i j (f i x))

sem-ε : {b : tag} (Γ : Ctx b) → sem-subst Γ (∙ b)
sem-ε {set} Γ = λ _ → tt
proj₁ (sem-ε {tot} Γ) i x = tt
proj₂ (sem-ε {tot} Γ) i j x = refl

sem-idsub : {b : tag} (Γ : Ctx b) → sem-subst Γ Γ
sem-idsub {set} Γ = λ x → x
proj₁ (sem-idsub {tot} Γ) i x = x
proj₂ (sem-idsub {tot} Γ) i j x = refl

sem-subcomp : {b : tag} (Γ Γ' Γ'' : Ctx b) → sem-subst Γ' Γ'' → sem-subst Γ Γ' → sem-subst Γ Γ''
sem-subcomp {set} Γ Γ' Γ'' α β x = α(β x)
proj₁ (sem-subcomp {tot} Γ Γ' Γ'' α β) i x = proj₁ α i (proj₁ β i x) 
proj₂ (sem-subcomp {tot} Γ Γ' Γ'' α β) i j x =
  begin
    proj₁ α j (proj₁ β j (Mor Γ i j x))
  ≡⟨ cong (proj₁ α j) (proj₂ β i j x) ⟩
    proj₁ α j (Mor Γ' i j (proj₁ β i x))
  ≡⟨ proj₂ α i j (proj₁ β i x) ⟩
    Mor Γ'' i j (proj₁ α i (proj₁ β i x))
  ∎

sem-subst-tm : {b : tag} (Γ Γ' : Ctx b) (A : Ty b) → sem-subst Γ Γ' → Tm Γ A → sem-subst Γ (Γ' ,, A)
sem-subst-tm {set} Γ Γ' A α t x = α x , t x
proj₁ (sem-subst-tm {tot} Γ Γ' A (α , p) (t , q)) i x = (α i x) , t i x
proj₂ (sem-subst-tm {tot} Γ Γ' A (α , p) (t , q)) i j x =
  begin
    (α j (Mor Γ i j x) , t j (Mor Γ i j x))
  ≡⟨ cong (λ z → (z , _)) (p i j x) ⟩
    (Mor Γ' i j (α i x) , t j (Mor Γ i j x))
  ≡⟨ cong (λ z → (_ , z)) (sym (q i j x)) ⟩
    (Mor Γ' i j (α i x) , Mor A i j (t i x))
  ∎

sem-subpr : {b : tag} (Γ Γ' : Ctx b) (A : Ty b) → sem-subst Γ (Γ' ,, A) → sem-subst Γ Γ'
sem-subpr {set} Γ Γ' A α = λ z → proj₁ (α z)
proj₁ (sem-subpr {tot} Γ Γ' A (α , p)) i x = proj₁ (α i x)
proj₂ (sem-subpr {tot} Γ Γ' A (α , p)) i j x =
  begin
    proj₁ (α j (Mor Γ i j x))
  ≡⟨ cong proj₁ (p i j x) ⟩
    Mor Γ' i j (proj₁ (α i x))
  ∎

sem-sub : {b : tag} (Γ Γ' : Ctx b) (A : Ty b) → Tm Γ' A → sem-subst Γ Γ' → Tm Γ A
sem-sub {set} Γ Γ' A t α x = t(α x)
proj₁ (sem-sub {tot} Γ Γ' A (t , p) (α , q)) i x = t i (α i x)
proj₂ (sem-sub {tot} Γ Γ' A (t , p) (α , q)) i j x =
  begin
    Mor A i j (t i (α i x))
  ≡⟨ p i j (α i x) ⟩
    t j (Mor Γ' i j (α i x))
  ≡⟨ cong (t j) (sym (q i j x)) ⟩
    t j (α j (Mor Γ i j x))
  ∎
{-
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
-}
\end{code}
