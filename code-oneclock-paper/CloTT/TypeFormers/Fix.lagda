\AgdaHide{
\begin{code}
module CloTT.TypeFormers.Fix where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers.Later
open import CloTT.TypeFormers.LaterType
open import CloTT.TypeFormers.FunctionType

open PSh
open ►Obj
open ExpObj
open NatTrans
\end{code}
}
We omit the semantic "corrispettivi" of the terms \IC{next} and
\IC{⊛}. Instead, we describe the construction of the fixed point
combinator \F{fix}. First we define a delayed fixed point combinator
\F{dfix}, which takes an element of \F{Tm} \Ar{Γ} (\F{►} \Ar{A} \F{⇒} \Ar{A}) and
returns an element of \F{Tm} \Ar{Γ} (\F{►} \Ar{A}). The definition of the
\Fi{nat-map} component of \F{dfix} \Ar{Γ A f} depends on an auxiliary term
\F{dfix₁}, which for a given size \Ar{i}, takes a function \Ar{f} in \F{ExpObj} (\F{►} \Ar{A})
\Ar{A i} and returns an element of \F{►Obj} \Ar{A i}.  Remember that
the \Fi{►cone} field of \F{►Obj} \Ar{A i} has type \F{Later}
(\Fi{Obj} \Ar{A}) \Ar{i}, which is a dependent function space with
domain \F{SizeLt} \Ar{i}. Therefore in the definition of \Fi{►cone} component of \F{dfix₁}
\Ar{A i f} we first assume an inhabitant of \F{SizeLt} \Ar{i} and we
pattern match on it, obtaining a size \Ar{j} : \F{Size<} \Ar{i}. Then we 
apply \Fi{fun} \Ar{f j} to \F{dfix₁} \Ar{A j f}. Notice
that the recursive call is applied to the size \Ar{j}, which is strictly
smaller than \Ar{i}. The termination of this recursive definition
is ensured by the employment of \F{SizeLt} \Ar{i} in the
definition of \F{Later} \Ar{A i}. Notice that by using \F{Size<}
\Ar{i} instead, which results in the same definition but without the
need for pattern matching, we would have constructed a non-productive
recursive definition that would have been correcly rejected by Agda's
termination checker. The use of the inductive family \F{SizeLt} is
therefore crucial in the definition of \F{dfix₁} since it prevents it
from unfolding indefinitely. We omit the construction of the \Fi{►com}
component of \F{dfix₁} \Ar{A i f}, which moreover requires the
employment of \F{elimLt} for being accepted by the termination checker.
We also omit the definition of the \Fi{nat-com} component of \F{dfix}
\Ar{Γ A f}.
\begin{code}
dfix₁ : (A : Ty κ) (i : Size) → ExpObj (► A) A i → ►Obj A i
►cone (dfix₁ A i f) [ j ] = fun f j (dfix₁ A j f)
\end{code}
\AgdaHide{
\begin{code}
►com (dfix₁ A i f) [ j ] [ k ] = 
  begin
    Mor A j k (fun f j (dfix₁ A j f))
  ≡⟨ funcom f j k (dfix₁ A j f) ⟩
    fun f k (►Mor A j k (dfix₁ A j f))
  ≡⟨ cong (fun f k) (►eq (λ {_ → refl})) ⟩
    fun f k (dfix₁ A k f)
  ∎
\end{code}
}
\begin{code}
dfix : (Γ : Ctx κ) (A : Ty κ) (f : Tm Γ (► A ⇒ A)) → Tm Γ (► A)
nat-map (dfix Γ A f) i γ = dfix₁ A i (nat-map f i γ)
\end{code}
\AgdaHide{
\begin{code}
nat-com (dfix Γ A f) i j γ = ►eq (λ {k → cong (λ a → fun a k (dfix₁ A k a)) (nat-com f i j γ)})
\end{code}
}
The semantic fixed point operation is obtained by applying the
function \AB{f} to \F{dfix} \Ar{Γ A f}.
\begin{code}
sem-fix : (Γ : Ctx κ) (A : Ty κ) (f : Tm Γ (► A ⇒ A)) → Tm Γ A
\end{code}

\AgdaHide{
\begin{code}
sem-fix Γ A f = sem-app-map Γ (► A) A f (dfix Γ A f)
\end{code}
}
