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
sem-subst : {b : tag} → Ctx b → Ctx b → Set
sem-subst {set} Γ₁ Γ₂ = Γ₁ → Γ₂
sem-subst {tot} Γ₁ Γ₂ =
  Σ[ f ∈ ((i : Size) → Obj Γ₁ i → Obj Γ₂ i) ]
    ((i : Size) (j : Size< (↑ i)) (x : Obj Γ₁ i) →
      f j (Mor Γ₁ i j x) ≡ Mor Γ₂ i j (f i x))

sem-ε : {b : tag} (Γ : Ctx b) → sem-subst Γ (∙ b)
sem-ε {set} Γ = λ _ → tt
proj₁ (sem-ε {tot} Γ) i x = tt
proj₂ (sem-ε {tot} Γ) i j x = refl

sem-idsub : {b : tag} (Γ : Ctx b) → sem-subst Γ Γ
sem-idsub {set} Γ = λ x → x
proj₁ (sem-idsub {tot} Γ) i x = x
proj₂ (sem-idsub {tot} Γ) i j x = refl

sem-subcomp : {b : tag} (Γ₁ Γ₂ Γ₃ : Ctx b) → sem-subst Γ₂ Γ₃ → sem-subst Γ₁ Γ₂ → sem-subst Γ₁ Γ₃
sem-subcomp {set} Γ₁ Γ₂ Γ₃ α β x = α(β x)
proj₁ (sem-subcomp {tot} Γ₁ Γ₂ Γ₃ α β) i x = proj₁ α i (proj₁ β i x) 
proj₂ (sem-subcomp {tot} Γ₁ Γ₂ Γ₃ α β) i j x =
  begin
    proj₁ α j (proj₁ β j (Mor Γ₁ i j x))
  ≡⟨ cong (proj₁ α j) (proj₂ β i j x) ⟩
    proj₁ α j (Mor Γ₂ i j (proj₁ β i x))
  ≡⟨ proj₂ α i j (proj₁ β i x) ⟩
    Mor Γ₃ i j (proj₁ α i (proj₁ β i x))
  ∎

sem-subst-tm : {b : tag} (Γ₁ Γ₂ : Ctx b) (A : Ty b) → sem-subst Γ₁ Γ₂ → Tm Γ₁ A → sem-subst Γ₁ (Γ₂ ,, A)
sem-subst-tm {set} Γ₁ Γ₂ A α t x = α x , t x
proj₁ (sem-subst-tm {tot} Γ₁ Γ₂ A (α , p) (t , q)) i x = (α i x) , t i x
proj₂ (sem-subst-tm {tot} Γ₁ Γ₂ A (α , p) (t , q)) i j x =
  begin
    (α j (Mor Γ₁ i j x) , t j (Mor Γ₁ i j x))
  ≡⟨ cong (λ z → (z , _)) (p i j x) ⟩
    (Mor Γ₂ i j (α i x) , t j (Mor Γ₁ i j x))
  ≡⟨ cong (λ z → (_ , z)) (sym (q i j x)) ⟩
    (Mor Γ₂ i j (α i x) , Mor A i j (t i x))
  ∎

sem-subpr : {b : tag} (Γ₁ Γ₂ : Ctx b) (A : Ty b) → sem-subst Γ₁ (Γ₂ ,, A) → sem-subst Γ₁ Γ₂
sem-subpr {set} Γ₁ Γ₂ A α = λ z → proj₁ (α z)
proj₁ (sem-subpr {tot} Γ₁ Γ₂ A (α , p)) i x = proj₁ (α i x)
proj₂ (sem-subpr {tot} Γ₁ Γ₂ A (α , p)) i j x =
  begin
    proj₁ (α j (Mor Γ₁ i j x))
  ≡⟨ cong proj₁ (p i j x) ⟩
    Mor Γ₂ i j (proj₁ (α i x))
  ∎

sem-sub : {b : tag} (Γ₁ Γ₂ : Ctx b) (A : Ty b) → Tm Γ₂ A → sem-subst Γ₁ Γ₂ → Tm Γ₁ A
sem-sub {set} Γ₁ Γ₂ A t α x = t(α x)
proj₁ (sem-sub {tot} Γ₁ Γ₂ A (t , p) (α , q)) i x = t i (α i x)
proj₂ (sem-sub {tot} Γ₁ Γ₂ A (t , p) (α , q)) i j x =
  begin
    Mor A i j (t i (α i x))
  ≡⟨ p i j (α i x) ⟩
    t j (Mor Γ₂ i j (α i x))
  ≡⟨ cong (t j) (sym (q i j x)) ⟩
    t j (α j (Mor Γ₁ i j x))
  ∎
\end{code}
