\AgdaHide{
\begin{code}
module GuardedTT where

open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Prelude
open import Prelude.Syntax
open import Presheaves
open import CloTT

open interpret-syntax
\end{code}
}

\begin{code}
sem : interpret-syntax
semClockContext sem = tag
semType sem = Ty
semContext sem = Ctx
semSubst sem = sem-subst
semTerm sem = Tm
_∼_ sem = def-eq _ _
⟦ sem ⟧CCtx = ⟦_⟧Δ
⟦ sem ⟧Type = ⟦_⟧A
⟦ sem ⟧Ctx = ⟦_⟧Γ
⟦ sem ⟧Subst = ⟦_⟧sub
⟦ sem ⟧Tm = ⟦_⟧tm
λ-β sem = sem-λ-β
λ-η sem = sem-λ-η
⊠-β₁ sem = sem-⊠-β₁
⊠-β₂ sem = sem-⊠-β₂
⊠-η sem = sem-⊠-η
⊞-β₁ sem = sem-⊞-β₁
⊞-β₂ sem = sem-⊞-β₂
𝟙-β sem = sem-𝟙-β
𝟙-η sem = sem-𝟙-η
□-β sem = sem-□-β
□-η sem = sem-□-η
next-id sem = sem-next-id
next-comp sem = sem-next-comp
next-⊛ sem = sem-next-⊛
next-λ sem = sem-next-λ
fix-f sem = sem-fix-f
fix-u sem = sem-fix-u

sem-consistent-help : ⊤ ⊎ ⊤ → Set
sem-consistent-help (inj₁ x) = ⊤
sem-consistent-help (inj₂ y) = ⊥

sem-consistent : consistent sem
sem-consistent p = subst sem-consistent-help (p ⊤.tt) ⊤.tt
\end{code}
