\AgdaHide{
\begin{code}
module CloTT.TypeFormers.Force where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers.Later
open import CloTT.TypeFormers.ClockQuantification

open PSh
open ■
open ►Obj
\end{code}
}

Finally we show the semantic description of the force operation , which
relies on the auxiliary definition \F{sem-force'}. Given a term \Ar{t}
in \F{■} (\F{►} \Ar{A}) we can contruct a term in \F{■} \Ar{A} as follows:
\begin{code}
sem-force' : (A : Ty κ) → ■ (► A) → ■ A
■cone (sem-force' A t) i = ►cone (■cone t ∞) [ i ]
■com (sem-force' A t) i j = ►com (■cone t ∞) [ i ] [ j ]
\end{code}
Notice the employment of the size \F{∞}. Moreover we also make use of the
\Fi{►com} field of \F{►Obj} \Ar{A i}.
The definition of the force combinator \F{sem-force} is a simple instance of \F{sem-force'}.
\begin{code}
sem-force : (Γ : Ctx ∅) (A : Ty κ) (t : Tm Γ (■ (► A))) → Tm Γ (■ A)
\end{code}
\AgdaHide{
\begin{code}
■cone (sem-force Γ A t x) j = ►cone (■cone (t x) ∞) [ j ]
■com (sem-force Γ A t x) i j = ►com (■cone (t x) ∞) [ i ] [ j ]
\end{code}
}
