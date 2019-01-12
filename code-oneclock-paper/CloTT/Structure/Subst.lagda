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
open NatTrans
\end{code}
}

The type theory we study, has explicit substitutions and we must also provide an interpretation for these.
Substitutions are maps from a context to a context.
Since contexts are presheaves, we interpret substitutions as natural transformations.
This leads to the following definition.

\begin{code}
sem-subst : {b : tag} → Ctx b → Ctx b → Set
sem-subst {set} Γ₁ Γ₂ = Γ₁ → Γ₂
sem-subst {tot} Γ₁ Γ₂ =
  Σ[ f ∈ ((i : Size) → Obj Γ₁ i → Obj Γ₂ i) ]
    ((i : Size) (j : Size< (↑ i)) (x : Obj Γ₁ i)
      → f j (Mor Γ₁ i j x) ≡ Mor Γ₂ i j (f i x))
\end{code}

Next we define the interpretation of operations on substitutions.
These all are defined in the expected way.
The identity substitution is interpreted as the identity transformation, the composition as the composition, and so on.
As an example, we show how an explicit substitution gives rise to an actual one.
We only give the component map and not the proof of naturality.

\begin{code}
sem-sub : {b : tag} (Γ₁ Γ₂ : Ctx b) (A : Ty b) → Tm Γ₂ A → sem-subst Γ₁ Γ₂ → Tm Γ₁ A
sem-sub {set} Γ₁ Γ₂ A t α x = t(α x)
nat-map (sem-sub {tot} Γ₁ Γ₂ A t α) i x = nat-map t i (proj₁ α i x)
\end{code}
\AgdaHide{
\begin{code}
nat-com (sem-sub {tot} Γ₁ Γ₂ A t α) i j x =
  begin
    Mor A i j (nat-map t i (proj₁ α i x))
  ≡⟨ nat-com t i j (proj₁ α i x) ⟩
    nat-map t j (Mor Γ₂ i j (proj₁ α i x))
  ≡⟨ cong (nat-map t j) (sym (proj₂ α i j x)) ⟩
    nat-map t j (proj₁ α j (Mor Γ₁ i j x))
  ∎
\end{code}
}

\AgdaHide{
\begin{code}
sem-idsub : {b : tag} (Γ : Ctx b) → sem-subst Γ Γ
sem-idsub {set} Γ x = x
proj₁ (sem-idsub {tot} Γ) i x = x
proj₂ (sem-idsub {tot} Γ) i j x = refl
\end{code}

\begin{code}
sem-ε : {b : tag} (Γ : Ctx b) → sem-subst Γ (∙ b)
sem-ε {set} Γ x = tt
proj₁ (sem-ε {tot} Γ) i x = tt
proj₂ (sem-ε {tot} Γ) i j x = refl
\end{code}

\begin{code}
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
\end{code}

\begin{code}
sem-subst-tm : {b : tag} (Γ₁ Γ₂ : Ctx b) (A : Ty b) → sem-subst Γ₁ Γ₂ → Tm Γ₁ A → sem-subst Γ₁ (Γ₂ ,, A)
sem-subst-tm {set} Γ₁ Γ₂ A α t x = α x , t x
proj₁ (sem-subst-tm {tot} Γ₁ Γ₂ A α t) i x = proj₁ α i x , nat-map t i x
proj₂ (sem-subst-tm {tot} Γ₁ Γ₂ A α t) i j x =
  begin
    (proj₁ α j (Mor Γ₁ i j x) , nat-map t j (Mor Γ₁ i j x))
  ≡⟨ cong (λ z → (z , _)) (proj₂ α i j x) ⟩
    (Mor Γ₂ i j (proj₁ α i x) , nat-map t j (Mor Γ₁ i j x))
  ≡⟨ cong (λ z → (_ , z)) (sym (nat-com t i j x)) ⟩
    (Mor Γ₂ i j (proj₁ α i x) , Mor A i j (nat-map t i x))
  ∎
\end{code}

\begin{code}
sem-subpr : {b : tag} (Γ₁ Γ₂ : Ctx b) (A : Ty b) → sem-subst Γ₁ (Γ₂ ,, A) → sem-subst Γ₁ Γ₂
sem-subpr {set} Γ₁ Γ₂ A α z = proj₁ (α z)
proj₁ (sem-subpr {tot} Γ₁ Γ₂ A (α , p)) i x = proj₁ (α i x)
proj₂ (sem-subpr {tot} Γ₁ Γ₂ A (α , p)) i j x =
  begin
    proj₁ (α j (Mor Γ₁ i j x))
  ≡⟨ cong proj₁ (p i j x) ⟩
    Mor Γ₂ i j (proj₁ (α i x))
  ∎
\end{code}
}
