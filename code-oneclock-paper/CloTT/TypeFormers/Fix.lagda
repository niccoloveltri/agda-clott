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
We omit the semantic equivalents of the terms \IC{next} and \IC{⊛}.
Instead, we discuss the interpretation of the delayed fixpoint combinator \AIC{dfix}.
%The \Fi{nat-map} component of \F{sem-dfix} depends on
First we introduce an auxiliary term \F{sem-dfix₁}, which for each semantic \IC{κ}-type \Ar{A}, size \Ar{i} and returns a map of type \F{ExpObj} (\F{►} \Ar{A}) \Ar{A i} → \F{►Obj} \Ar{A i}.
Here we only show the definition of the \Fi{►cone} component of \F{sem-dfix₁} \Ar{A i f}.
Given an inhabitant of \F{SizeLt} \Ar{i}, we pattern matching on it obtaining a size \Ar{j} : \F{Size<} \Ar{i}.
Then we apply the function \AFi{fun} \Ar{f} \Ar{j} to \F{sem-dix₁} \AB{A} \AB{j} \AB{f}.
%%Since \AFi{fun} \Ar{f} \Ar{j} is a function from \F{►Obj} \AB{A} \AB{j} to \AFi{Obj} \AB{A} \AB{j}, it suffices to define an inhabitant of type \F{►Obj} \AB{A} \AB{j}.
%%For this, we use \F{sem-dix₁} \AB{A} \AB{j} \AB{f}.
%%This leads to the following definition.

\begin{code}
sem-dfix₁ : (A : SemTy κ) (i : Size) → ExpObj (► A) A i → ►Obj A i
►cone (sem-dfix₁ A i f) [ j ] = fun f j (sem-dfix₁ A j f)
\end{code}
\AgdaHide{
\begin{code}
►com (sem-dfix₁ A i f) [ j ] [ k ] =
  begin
    Mor A j k (fun f j (sem-dfix₁ A j f))
  ≡⟨ funcom f j k (sem-dfix₁ A j f) ⟩
    fun f k (►Mor A j k (sem-dfix₁ A j f))
  ≡⟨ cong (fun f k) (►eq (λ {_ → refl})) ⟩
    fun f k (sem-dfix₁ A k f)
  ∎
\end{code}
}
This definition is accepted by Agda's termination checker because
every recursive call is applied to a strictly smaller size.  Moreover,
the usage of \F{SizeLt} in the definition of \F{Later} prevents
infinite unfolding.  By using \F{►ObjTry} instead of \F{►Obj}, we
would have constructed a non-productive recursive definition that
Agda would have rightly rejected.

%%Note the recursive call of \F{sem-dfix₁}.
%%The termination is guaranteed by the usage of \F{SizeLt} \Ar{i} in the definition of \F{Later} \Ar{A i}.
%%The foremost reason is that the sizes decrease in every recursive call.
%%In addition, the usage of \F{SizeLt} prevents infinite unfolding.
%%If we used the same definition but with \F{Size<} \Ar{i} instead, we would have constructed a non-productive recursive definition that would have been correcly rejected by Agda's termination checker.

The \Fi{nat-map} component of \F{sem-dfix} can be easily defined using \F{sem-dfix₁}. We omit the construction of the \Fi{nat-com} component.
\begin{code}
sem-dfix : (Γ : SemCtx κ) (A : SemTy κ) (f : SemTm Γ (► A ⇒ A)) → SemTm Γ (► A)
nat-map (sem-dfix Γ A f) i γ = sem-dfix₁ A i (nat-map f i γ)
\end{code}
\AgdaHide{
\begin{code}
nat-com (sem-dfix Γ A f) i j γ = ►eq (λ {k → cong (λ a → fun a k (sem-dfix₁ A k a)) (nat-com f i j γ)})
\end{code}
}
\AgdaHide{
\begin{code}
sem-fix : (Γ : SemCtx κ) (A : SemTy κ) (f : SemTm Γ (► A ⇒ A)) → SemTm Γ A
sem-fix Γ A f = sem-app-map Γ (► A) A f (sem-dfix Γ A f)
\end{code}
}
