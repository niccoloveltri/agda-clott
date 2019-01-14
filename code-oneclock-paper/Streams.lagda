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
g-Str : Type ∅ → Type κ
g-Str A = μ ((∁ (⇑ A)) ⊠ (▻P I))
\end{code}

\begin{code}
cons-inv : {Δ : ClockContext} {Γ : Context Δ} (P : Poly Δ) → Term Γ (μ P) → Term Γ (evalP P (μ P))
cons-inv {Γ = Γ} P = app-map (primrec P (lambdaTm (π₁ (varTm Γ (evalP P (μ P) ⊠ evalP P (evalP P (μ P)))))))
\end{code}

\begin{code}
g-hd : {Γ : Context ∅} {A : Type ∅} → Term (⇑ Γ) (g-Str A) → Term Γ A
g-hd {Γ}{A} xs = ↓ (π₁ (cons-inv ((∁ (⇑ A)) ⊠ (▻P I)) xs))
\end{code}

\begin{code}
g-tl : {Γ : Context κ} {A : Type ∅} → Term Γ (g-Str A) → Term Γ (▻ (g-Str A))
g-tl {Γ}{A} xs = π₂ (cons-inv ((∁ (⇑ A)) ⊠ (▻P I)) xs)
\end{code}

\begin{code}
Str : Type ∅ → Type ∅
Str A = □ (g-Str A)
\end{code}

\begin{code}
hd : {Γ : Context ∅} {A : Type ∅} → Term Γ (Str A) → Term Γ A
hd xs = g-hd (unbox-q xs)
\end{code}

\begin{code}
tl : {Γ : Context ∅} {A : Type ∅} → Term Γ (Str A) → Term Γ (Str A)
tl xs = force (box-q (g-tl (unbox-q xs)))
\end{code}

\begin{code}
oddrec : {Γ : Context ∅} {A : Type ∅} → Term (⇑ Γ , (⇑ (Str A) ⟶ ▻ (g-Str A))) (⇑ (Str A) ⟶ g-Str A)
oddrec {Γ} {A} =
  let s = ,-weaken _ _ o weakenSA _ (pr (idsub _))
      f = ⇑m _ _ _ (varTm _ _)
      xs = varTm _ _
  in
  lambdaTm (cons _ [ sub (⇡ (hd xs)) s & app-map f (sub (⇡ (tl xs)) s) ])
\end{code}

\begin{code}
odd : {Γ : Context ∅} {A : Type ∅} → Term Γ (Str A) → Term Γ (Str A)
odd xs = box-q (app-map (pfix-tm oddrec) (⇡ xs))
\end{code}
