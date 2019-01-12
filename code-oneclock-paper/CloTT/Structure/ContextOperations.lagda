\AgdaHide{
\begin{code}
module CloTT.Structure.ContextOperations where

open import Data.Unit
open import Data.Product
open import Prelude
open import Presheaves
open import CloTT.Structure.ClockContexts
open import CloTT.Structure.Contexts
open import CloTT.Structure.Types
open import CloTT.Structure.Terms

open NatTrans
\end{code}
}

To interpret simple type theory, we also need to give the context operations and type formers.
Since their definitions are standard, we do not discuss them formally.
For each operation, we need to make a case distinction based on the clock context.
The empty context is interpreted with the unit type and terminal presheaf and for context extension we use the product.
For the variable rule, we use the second projection and for weakening, we use the first projection.

\AgdaHide{
\begin{code}
∙ : (b : tag) → Ctx b
∙ set = ⊤
∙ tot = Terminal
\end{code}

\begin{code}
_,,_ : {b : tag} → Ctx b → Ty b → Ctx b
_,,_ {set} Γ A = Γ × A
_,,_ {tot} Γ A = Prod Γ A
\end{code}

\begin{code}
var : {b : tag} (Γ : Ctx b) (A : Ty b) → Tm (Γ ,, A) A
var {set} Γ A = proj₂
nat-map (var {tot} Γ A) i (γ , x) = x
nat-com (var {tot} Γ A) i j (γ , x) = refl
\end{code}

\begin{code}
weaken : {b : tag} (Γ : Ctx b) (A B : Ty b) → Tm Γ B → Tm (Γ ,, A) B
weaken {set} Γ A B t (x , _) = t x
nat-map (weaken {tot} Γ A B t) i (x₁ , x₂) = nat-map t i x₁
nat-com (weaken {tot} Γ A B t) i j (x₁ , x₂) = nat-com t i j x₁
\end{code}
}
