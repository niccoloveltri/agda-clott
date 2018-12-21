\AgdaHide{
\begin{code}
module CloTT.Structure.ContextOperations where

open import Data.Unit
open import Data.Product
open import Prelude
open import Presheaves
open import CloTT.Structure.Contexts
open import CloTT.Structure.Types
open import CloTT.Structure.Terms
\end{code}
}

%The empty context in \IC{set} is the unit type \D{⊤}, while in
%\IC{tot} is the presheaf \D{Terminal}.

\AgdaHide{
\begin{code}
∙ : (b : tag) → Ctx b 
∙ set = ⊤
∙ tot = Terminal
\end{code}
}
%Context extension in \IC{set} is cartesian product, while in \IC{tot}
%is the operation \D{Prod} on presheaves.
\AgdaHide{
\begin{code}
_,,_ : {b : tag} → Ctx b → Ty b → Ctx b
_,,_ {set} Γ A = Γ × A
_,,_ {tot} Γ A = Prod Γ A
\end{code}


\begin{code}
var : {b : tag} (Γ : Ctx b) (A : Ty b) → Tm (Γ ,, A) A
var {set} Γ A = proj₂
proj₁ (var {tot} Γ A) i (γ , x) = x
proj₂ (var {tot} Γ A) i j (γ , x) = refl
\end{code}

\begin{code}
weaken : {b : tag} (Γ : Ctx b) (A B : Ty b)
  → Tm Γ B → Tm (Γ ,, A) B
weaken {set} Γ A B t (x , _) = t x
proj₁ (weaken {tot} Γ A B (t , p)) i (x₁ , x₂) = t i x₁
proj₂ (weaken {tot} Γ A B (t , p)) i j (x₁ , x₂) = p i j x₁
\end{code}
}
