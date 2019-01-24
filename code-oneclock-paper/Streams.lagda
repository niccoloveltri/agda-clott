\AgdaHide{
\begin{code}
module Streams where

open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Prelude
open import Prelude.Syntax
\end{code}
}

\subsection{Example: Streams}
We give a taste of how to program with streams in \GTT. First we construct a function \F{cons-inv} which is definable using \IC{primrec}.
\begin{code}
cons-inv : ∀ {Δ} {Γ : Context Δ} (P : Poly Δ) → Term Γ (μ P) → Term Γ (evalP P (μ P))
\end{code}
\AgdaHide{
\begin{code}
cons-inv {Γ = Γ} P = app-map (primrec P (Pmap P (lambdaTm (π₁ (varTm Γ (μ P ⊠ evalP P (μ P))))))) 
\end{code}
}
The type of guarded streams over a \IC{∅}-type \Ar{A} is the least fixpoint of the functor with code \IC{∁} (\IC{⇑} \Ar{A}) \IC{⊠} \IC{▻P I}.
\begin{code}
g-Str : Type ∅ → Type κ
g-Str A = μ (∁ (⇑ A) ⊠ ▻P I)
\end{code}
The head of a guarded stream \Ar{xs} is computed in three steps. First
we apply \F{cons-inv} to \Ar{xs}, obtaining a \GTT\ pair of type \IC{∁} (\IC{⇑} \Ar{A}) \IC{⊠} \IC{▻P} (\F{g-Str} \Ar{A}). Then we take the first projection of this pair using the constructor \IC{π₁} and we conclude with an application of \IC{↓}, which is necessary since \Ar{A} is a \IC{∅}-type.
\begin{code}
g-hd : {Γ : Context ∅} {A : Type ∅} → Term (⇑ Γ) (g-Str A) → Term Γ A
g-hd {Γ}{A} xs = ↓ (π₁ (cons-inv ((∁ (⇑ A)) ⊠ (▻P I)) xs))
\end{code}
The tail of a guarded stream is computed in a similar way, using \IC{π₂} instead of \IC{π₁} and without the application of \IC{↓} in the last step. Notice that the tail is a \GTT\ term of type \IC{▻} (\F{g-Str} \Ar{A}), meaning that it is available only one time step ahead from now.
\begin{code}
g-tl : {Γ : Context κ} {A : Type ∅} → Term Γ (g-Str A) → Term Γ (▻ (g-Str A))
g-tl {Γ}{A} xs = π₂ (cons-inv ((∁ (⇑ A)) ⊠ (▻P I)) xs)
\end{code}
The usual type of streams over \Ar{A} is obtained by applying the \IC{□} modality to \F{g-Str} \Ar{A}.
\begin{code}
Str : Type ∅ → Type ∅
Str A = □ (g-Str A)
\end{code}
The head of a stream \Ar{xs} is computed by applying the function \F{g-hd} to the unboxing of \Ar{xs}.
\begin{code}
hd : {Γ : Context ∅} {A : Type ∅} → Term Γ (Str A) → Term Γ A
hd xs = g-hd (unbox-q xs)
\end{code}
For computing the tail of a stream \Ar{xs} we first apply the function \F{g-tl} to the unboxing of \Ar{xs}, obtaining an element of \F{Term} (\IC{⇑} \Ar{Γ}) (\IC{▻} (\F{g-Str} \Ar{A})). Then we \IC{box-q} followed by \IC{force}.
\begin{code}
tl : {Γ : Context ∅} {A : Type ∅} → Term Γ (Str A) → Term Γ (Str A)
tl xs = force (box-q (g-tl (unbox-q xs)))
\end{code}
Given a \GTT\ term \Ar{a} of type \Ar{A}, we can construct the constant guarded stream over \Ar{a} using the fixpoint combinator.
\begin{code}
g-const : {Γ : Context ∅} {A : Type ∅} → Term Γ A → Term (⇑ Γ) (g-Str A)
g-const a = fix-tm (lambdaTm (cons _ [ wk (⇡ a) & varTm _ _ ]))
\end{code}
\NV{Here we use wk, which we have not introduced. Also, it would be nice to have the first argument of cons implicit. Similarly, the two arguments of varTm should be implicit.}
The constant stream over \Ar{a} is obtained by boxing the guarded stream \F{g-const} \Ar{a}.
\begin{code}
const-str : {Γ : Context ∅} {A : Type ∅} → Term Γ A → Term Γ (Str A)
const-str a = box-q (g-const a)
\end{code}

\AgdaHide{
\begin{code}
weakenSΓ : {Δ : ClockContext} {Γ : Context Δ} {A B : Type Δ} → Term Γ (A ⟶ B) → Subst (Γ , A) (Γ , B)
weakenSΓ {_} {Γ} {A} {B} s = pr (idsub (Γ , A)) ,s appTm s
\end{code}

\begin{code}
pfix-tm : {Γ : Context κ} {A B : Type κ}
  → Term (Γ , (A ⟶ ▻ B)) (A ⟶ B) → Term Γ (A ⟶ B)
pfix-tm {Γ}{A}{B} f = fix-tm (lambdaTm (sub f (weakenSΓ (lambdaTm (lambdaTm (sub (varTm Γ (▻ (A ⟶ B))) (pr (idsub ((Γ , ▻ (A ⟶ B)) , A))) ⊛ next (varTm (Γ , ▻ (A ⟶ B)) A)))))))
\end{code}

\begin{code}
oddrec : {Γ : Context ∅} {A : Type ∅} → Term (⇑ Γ , (⇑ (Str A) ⟶ ▻ (g-Str A))) (⇑ (Str A) ⟶ g-Str A)
oddrec {Γ} {A} =
  let s = ,-weaken _ _ o weakenSA _ (pr (idsub _))
      f = wk (varTm _ _)
      xs = varTm _ _
  in
  lambdaTm (cons _ [ sub (⇡ (hd xs)) s & app-map f (sub (⇡ (tl xs)) s) ])
\end{code}

\begin{code}
odd : {Γ : Context ∅} {A : Type ∅} → Term Γ (Str A) → Term Γ (Str A)
odd xs = box-q (app-map (pfix-tm oddrec) (⇡ xs))
\end{code}
}
