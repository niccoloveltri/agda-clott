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
We omit the semantic equivalents of \IC{next} and \IC{⊛}.
To interpret the delayed fixpoint combinator \AIC{dfix}, we introduce an auxiliary term \F{sem-dfix₁}, for which we only show how to construct the field \Fi{►cone}.
This is defined using self-application.
%This is intuitively defined as self-application of the function argument \Ar{f}.
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
This definition is accepted by Agda's termination checker for two reasons:
\begin{itemize}
  \item every recursive call is applied to a strictly smaller size;
  \item the usage of \F{SizeLt} in place of \F{Size<} in the definition of \F{Later} prevents indefinite unfolding, which would have happened if we used \F{►ObjTry} instead of \F{►Obj}.
\end{itemize}
In fact, replacing \F{►Obj} for \F{►ObjTry} as the return type of \F{sem-dfix₁} but keeping the same definition, with \Ar{j} in place of \IC{[} \Ar{j} \IC{]}, we would obtain the following non-terminating sequence of reductions:
\begin{align*}
& \text{\Fi{►cone} (\F{sem-dfix₁} \Ar{A i f})} \\
& \qquad = \text{λ \Ar{j} → \Fi{fun} \Ar{f j} (\F{sem-dfix₁} \Ar{A j f})} \\
& \qquad = \text{λ \Ar{j} → \Fi{fun} \Ar{f j} (\AgdaRecord{record} \{ \Fi{►cone} = λ \Ar{k} → \Fi{fun} \Ar{f k} (\F{sem-dfix₁} \Ar{A k f}) ; \Fi{►com} = \dots \})} \\
& \qquad =  \dots
\end{align*}

\remove{
This definition is accepted by Agda's termination checker because
every recursive call is applied to a strictly smaller size.  Moreover,
the usage of \F{SizeLt} in the definition of \F{Later} prevents the definition from unfolding indefinitely, which would have happened by using \F{►ObjTry} instead of \F{►Obj}.
%, the field \AFi{►cone}
%would have
%been defined by lambda abstraction meaning that we could
%unfolded indefinitely.
This is a non-terminating recursive definition, which Agda would have rightly rejected.
}
The termination of the \Fi{►com} component of \F{sem-dfix₁} additionally relies on the presence of \F{elimLt} in the definition of \F{LaterLim}.

%%Note the recursive call of \F{sem-dfix₁}.
%%The termination is guaranteed by the usage of \F{SizeLt} \Ar{i} in the definition of \F{Later} \Ar{A i}.
%%The foremost reason is that the sizes decrease in every recursive call.
%%In addition, the usage of \F{SizeLt} prevents infinite unfolding.
%%If we used the same definition but with \F{Size<} \Ar{i} instead, we would have constructed a non-productive recursive definition that would have been correcly rejected by Agda's termination checker.

The field \Fi{nat-map} of \F{sem-dfix} is defined using \F{sem-dfix₁}. We omit the
%construction of the
\Fi{nat-com} component.
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
