\AgdaHide{
\begin{code}
module CloTT.TypeFormers.ClockQuantification where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers.WeakenClock
open import CloTT.TypeFormers.FunctionType

open PSh
open NatTrans
\end{code}
}

Following \cite{Mogelberg14}, clock quantification is modelled by
taking limits. Given a type a presheaf \Ar{A}, we take \F{■} \Ar{A}
to be the limit of \Ar{A}.  Formally the limit of \Ar{A} is constructed as
record with two fields. The field \AFi{■cone} is given by a family of
element \Ar{f i} in \Fi{Obj} \Ar{A i} for each size \Ar{i}.
The field \AFi{■com} is a proof that the restriction of \Ar{f i} to a size \Ar{j}
smaller than \Ar{i} is equal to \Ar{f j}.
\begin{code}
record ■ (A : SemTy κ) : SemTy ∅ where
  field
    ■cone : (i : Size) → Obj A i
    ■com : (i : Size) (j : Size< (↑ i)) → Mor A i j (■cone i) ≡ ■cone j
\end{code}
\AgdaHide{
\begin{code}
open ■

■eq' : {A : SemTy κ} {s t : ■ A} → ■cone s ≡ ■cone t → s ≡ t
■eq' {_} {s} {t} refl = cong (λ z → record { ■cone = ■cone s ; ■com = z })
                             (funext (λ _ → funext λ _ → uip))

■eq : {A : SemTy κ} {s t : ■ A} → ((i : Size) → ■cone s i ≡ ■cone t i) → s ≡ t
■eq p = ■eq' (funext p)
\end{code}
}

Semantically, clock quantification \F{■} is right adjoint to context
weakening \F{⇑}. In other words, the types \F{Tm} (\F{⇑} \Ar{Γ})
\Ar{A} and \F{Tm} \Ar{Γ} (\F{■} \Ar{A}) are isomorphic. The function
underlying the isomorphism is \F{box} and its inverse is \F{unbox}.
\begin{code}
sem-box : (Γ : SemCtx ∅) (A : SemTy κ) (t : SemTm (⇑ Γ) A) → SemTm Γ (■ A)
■cone (sem-box Γ A t x) i        = nat-map t i x
■com (sem-box Γ A t x) i j       = nat-com t i j x

sem-unbox : (Γ : SemCtx ∅) (A : SemTy κ) (t : SemTm Γ (■ A)) → SemTm (⇑ Γ) A
nat-map (sem-unbox Γ A t) i x    = ■cone (t x) i
nat-com (sem-unbox Γ A t) i j x  = ■com (t x) i j
\end{code}
