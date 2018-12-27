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

pfix-tm : {Γ : Context κ} {A B : Type κ}
  → Term (Γ , (A ⟶ later B)) (A ⟶ B) → Term Γ (A ⟶ B)
pfix-tm {Γ}{A}{B} f = fix-tm (lambdaTm (sub f (weakenSΓ (lambdaTm (lambdaTm (sub (varTm Γ (later (A ⟶ B))) (pr (idsub ((Γ , later (A ⟶ B)) , A))) ⊛ next (varTm (Γ , later (A ⟶ B)) A)))))))

g-Str : Type ∅ → Type κ
g-Str A = μ ((∁ (weakenT A)) ⊠ (► I))

cons-inv : {Δ : ClockContext} {Γ : Context Δ} (P : Poly Δ) → Term Γ (μ P) → Term Γ (evalP P (μ P))
cons-inv {Γ = Γ} P = app-map (primrec P (lambdaTm (π₁ (varTm Γ (evalP P (μ P) ⊠ evalP P (evalP P (μ P)))))))

g-hd : {Γ : Context ∅} {A : Type ∅} → Term (weakenC Γ) (g-Str A) → Term Γ A
g-hd {Γ}{A} xs = ↓ (π₁ (cons-inv ((∁ (weakenT A)) ⊠ (► I)) xs)) 

g-tl : {Γ : Context κ} {A : Type ∅} → Term Γ (g-Str A) → Term Γ (later (g-Str A))
g-tl {Γ}{A} xs = π₂ (cons-inv ((∁ (weakenT A)) ⊠ (► I)) xs)

Str : Type ∅ → Type ∅
Str A = clock-q (g-Str A)

hd : {Γ : Context ∅} {A : Type ∅} → Term Γ (Str A) → Term Γ A
hd xs = g-hd (unbox-q xs)

tl : {Γ : Context ∅} {A : Type ∅} → Term Γ (Str A) → Term Γ (Str A)
tl xs = force (box-q (g-tl (unbox-q xs))) 

oddrec : {Γ : Context ∅} {A : Type ∅} → Term (weakenC Γ , (weakenT (Str A) ⟶ later (g-Str A))) (weakenT (Str A) ⟶ g-Str A)
oddrec {Γ} {A} =
  let s = ,-weaken _ _ o weakenSA _ (pr (idsub _))
  in
  lambdaTm (cons _ [ sub (⇡ (hd (varTm _ _))) s & sub (varTm _ _) (pr (pr (idsub _)) ,s app-map (weakenTm _ _ _ (varTm _ _)) (sub (⇡ (tl (varTm _ _))) s))  ])

odd : {Γ : Context ∅} {A : Type ∅} → Term Γ (Str A) → Term Γ (Str A)
odd xs = box-q (app-map (pfix-tm oddrec) (⇡ xs))

\end{code}
