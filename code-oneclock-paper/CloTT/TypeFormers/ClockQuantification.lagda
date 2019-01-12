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
taking limits. Given a type \Ar{A} in the semantic clock context
\IC{κ}, i.e. a presheaf, we take \F{□} \Ar{A} to be the limit of
\Ar{A}.  Formally the limit of \Ar{A} is constructed as a
$\Sigma$-type. The first component is given by for each size \Ar{i} an
element \Ar{f i} in \Fi{Obj} \Ar{A i}. The second component is a proof
that the restriction of \Ar{f i} to a size \Ar{j} smaller than \Ar{i}
is equal to \Ar{f j}.

\begin{code}
record ■ (A : Ty κ) : Ty ∅ where
  field
    ■cone : (i : Size) → Obj A i
    ■com : (i : Size) (j : Size< (↑ i)) → Mor A i j (■cone i) ≡ ■cone j
open ■
\end{code}

\AgdaHide{
\begin{code}
■eq' : {A : Ty κ} {s t : ■ A} → ■cone s ≡ ■cone t → s ≡ t
■eq' {_} {s} {t} refl = cong (λ z → record { ■cone = ■cone s ; ■com = z })
                             (funext (λ _ → funext λ _ → uip))

■eq : {A : Ty κ} {s t : ■ A} → ((i : Size) → ■cone s i ≡ ■cone t i) → s ≡ t
■eq p = ■eq' (funext p)
\end{code}
}

Semantically, clock quantification \F{■} is right adjoint to context
weakening \F{WC}. In other words, the types \F{Tm} (\F{WC} \Ar{Γ})
\Ar{A} and \F{Tm} \Ar{Γ} (\F{■} \Ar{A}) are isomorphic. The function
underlying the isomorphism is \F{box} and its inverse is \F{unbox}.


\begin{code}
box : (Γ : Ctx ∅) (A : Ty κ) (t : Tm (WC Γ) A) → Tm Γ (■ A)
■cone (box Γ A t x) i = nat-map t i x
■com (box Γ A t x) i j = nat-com t i j x
\end{code}

\begin{code}
unbox : (Γ : Ctx ∅) (A : Ty κ) (t : Tm Γ (■ A)) → Tm (WC Γ) A
nat-map (unbox Γ A t) i x = ■cone (t x) i
nat-com (unbox Γ A t) i j x = ■com (t x) i j
\end{code}
