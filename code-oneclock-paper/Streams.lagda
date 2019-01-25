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

\NV{This section is definitely too long. Perhaps hd and tl can be
defined directly without introducing g-hd and g-tl. We could also skip
the constant stream and refer to the Agda formalization.}

We give a taste of how to program with streams in \GTT. First we construct a function \F{cons-inv} which is definable using \IC{primrec}.
\begin{code}
cons-inv : ∀ {Δ} {Γ : Ctx Δ} (P : Poly Δ) → Tm Γ (μ P) → Tm Γ (eval P (μ P))
\end{code}
\AgdaHide{
\begin{code}
cons-inv {Γ = Γ} P = _$_ (primrec P (Pmap P (lambda (π₁ (var Γ (μ P ⊠ eval P (μ P))))))) 
\end{code}
}
The type of guarded streams over a \IC{∅}-type \Ar{A} is the least fixpoint of the functor with code \IC{∁} (\IC{⇑} \Ar{A}) \IC{⊠} \IC{▻P I}.
\begin{code}
g-Str : Ty ∅ → Ty κ
g-Str A = μ (∁ (⇡ A) ⊠ ▻ I)
\end{code}
The head of a guarded stream \Ar{xs} is computed in three steps. First
we apply \F{cons-inv} to \Ar{xs}, obtaining a \GTT\ pair of type \IC{∁} (\IC{⇡} \Ar{A}) \IC{⊠} \IC{▻P} (\F{g-Str} \Ar{A}). Then we take the first projection of this pair using the constructor \IC{π₁} and we conclude with an application of \IC{down}, which is necessary since \Ar{A} is a \IC{∅}-type.
\begin{code}
g-hd : {Γ : Ctx ∅} {A : Ty ∅} → Tm (⇡ Γ) (g-Str A) → Tm Γ A
g-hd {Γ}{A} xs = down (π₁ (cons-inv ((∁ (⇡ A)) ⊠ (▻ I)) xs))
\end{code}
The tail of a guarded stream is computed in a similar way, using \IC{π₂} instead of \IC{π₁} and without the application of \IC{down} in the last step. Notice that the tail is a \GTT\ term of type \IC{▻} (\F{g-Str} \Ar{A}), meaning that it is available only one time step ahead from now.
\begin{code}
g-tl : {Γ : Ctx κ} {A : Ty ∅} → Tm Γ (g-Str A) → Tm Γ (▻ (g-Str A))
g-tl {Γ}{A} xs = π₂ (cons-inv ((∁ (⇡ A)) ⊠ (▻ I)) xs)
\end{code}
The usual type of streams over \Ar{A} is obtained by applying the \IC{□} modality to \F{g-Str} \Ar{A}.
\begin{code}
Str : Ty ∅ → Ty ∅
Str A = □ (g-Str A)
\end{code}
The head of a stream \Ar{xs} is computed by applying the function \F{g-hd} to the unboxing of \Ar{xs}.
\begin{code}
hd : {Γ : Ctx ∅} {A : Ty ∅} → Tm Γ (Str A) → Tm Γ A
hd xs = g-hd (unbox xs)
\end{code}
For computing the tail of a stream \Ar{xs} we first apply the function \F{g-tl} to the unboxing of \Ar{xs}, obtaining an element of \F{Tm} (\IC{⇡} \Ar{Γ}) (\IC{▻} (\F{g-Str} \Ar{A})). Then we \IC{box-q} followed by \IC{force}.
\begin{code}
tl : {Γ : Ctx ∅} {A : Ty ∅} → Tm Γ (Str A) → Tm Γ (Str A)
tl xs = force (box (g-tl (unbox xs)))
\end{code}
Given a \GTT\ term \Ar{a} of type \Ar{A}, we can construct the constant guarded stream over \Ar{a} using the fixpoint combinator.
\begin{code}
g-const : {Γ : Ctx ∅} {A : Ty ∅} → Tm Γ A → Tm (⇡ Γ) (g-Str A)
g-const a = fix (lambda (cons _ [ wk (up a) & var _ _ ]))
\end{code}
\NV{Here we use wk, which we have not introduced. Also, it would be nice to have the first argument of cons implicit. Similarly, the two arguments of varTm should be implicit.}
The constant stream over \Ar{a} is obtained by boxing the guarded stream \F{g-const} \Ar{a}.
\begin{code}
const-str : {Γ : Ctx ∅} {A : Ty ∅} → Tm Γ A → Tm Γ (Str A)
const-str a = box (g-const a)
\end{code}

\AgdaHide{
\begin{code}
weakenSΓ : {Δ : ClockCtx} {Γ : Ctx Δ} {A B : Ty Δ} → Tm Γ (A ⟶ B) → Sub (Γ , A) (Γ , B)
weakenSΓ {_} {Γ} {A} {B} s = pr (id (Γ , A)) , app s
\end{code}

\begin{code}
pfix-tm : {Γ : Ctx κ} {A B : Ty κ}
  → Tm (Γ , (A ⟶ ▻ B)) (A ⟶ B) → Tm Γ (A ⟶ B)
pfix-tm {Γ}{A}{B} f = fix (lambda (sub f (weakenSΓ (lambda (lambda (sub (var Γ (▻ (A ⟶ B))) (pr (id ((Γ , ▻ (A ⟶ B)) , A))) ⊛ next (var (Γ , ▻ (A ⟶ B)) A)))))))
\end{code}

\begin{code}
oddrec : {Γ : Ctx ∅} {A : Ty ∅} → Tm (⇡ Γ , (⇡ (Str A) ⟶ ▻ (g-Str A))) (⇡ (Str A) ⟶ g-Str A)
oddrec {Γ} {A} =
  let s = ,⇡ _ _ ∘ upA _ (pr (id _))
      f = wk (var _ _)
      xs = var _ _
  in
  lambda (cons _ [ sub (up (hd xs)) s & f $ (sub (up (tl xs)) s) ])
\end{code}

\begin{code}
odd : {Γ : Ctx ∅} {A : Ty ∅} → Tm Γ (Str A) → Tm Γ (Str A)
odd xs = box ((pfix-tm oddrec) $ (up xs))
\end{code}
}
