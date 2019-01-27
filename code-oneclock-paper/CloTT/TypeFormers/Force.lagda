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

Finally we show the semantic description of the force operation.
For this, we define an auxilliary function \AF{sem-force'}.
Given a type \AB{A} and an inhabitant \AB{t} of \F{■}(\F{►} \Ar{A}), our
goal is to define an element of \F{■} \AB{A}.
This means that for each size \AB{i} we have to give an element of \AFi{Obj} \AB{A} \AB{i}.
Note that \AFi{■cone} \AB{t} gives for each size \AB{j} an inhabitant of \F{Later} \AB{A} \AB{j}.
If we find a size greater than \AB{i}, then we can use \AFi{■cone} \AB{t} for the desired element.
Since \F{∞} is bigger than \AB{i}, we define

\begin{code}
sem-force' : (A : SemTy κ) → ■ (► A) → ■ A
■cone (sem-force' A t) i = ►cone (■cone t ∞) [ i ]
■com (sem-force' A t) i j = ►com (■cone t ∞) [ i ] [ j ]
\end{code}

\begin{code}
sem-force : (Γ : SemCtx ∅) (A : SemTy κ) (t : SemTm Γ (■ (► A))) → SemTm Γ (■ A)
sem-force Γ A t x = sem-force' A (t x)
\end{code}
