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

Finally, we describe the interpretation of the \AIC{force} operation.
We first define an auxilliary function \AF{sem-force'}.  Given a type
\AB{A} and an inhabitant \AB{t} of \F{■}(\F{►} \Ar{A}), our goal is to
construct an element of \F{■} \AB{A}. For the \AFi{■cone} component,
we are given a size \AB{i} and we have to return an element of \AFi{Obj} \AB{A}
\AB{i}. We know that \AFi{■cone} \AB{t} \F{∞} has type \F{►Obj} \Ar{A}
\F{∞}. Therefore \Fi{►cone} (\Fi{■cone} \Ar{t} \F{∞}) \IC{[} \Ar{i}
\IC{]} has type \AFi{Obj} \AB{A}
\AB{i}, since the size \F{∞} is bigger than \AB{i}. The \AFi{■com} component of \F{sem-force'} is constructed similarly.
%%Note that \AFi{■cone} \AB{t} gives for each size \AB{j} an inhabitant of \F{Later} \AB{A} \AB{j}.
%%If we find a size greater than \AB{i}, then we can use \AFi{■cone} \AB{t} for the desired element.
%%Since \F{∞} is bigger than \AB{i}, we define
\begin{code}
sem-force' : (A : SemTy κ) → ■ (► A) → ■ A
■cone (sem-force' A t) i = ►cone (■cone t ∞) [ i ]
■com (sem-force' A t) i j = ►com (■cone t ∞) [ i ] [ j ]
\end{code}
The semantic force operation follows immediately from \F{sem-force'}.
\begin{code}
sem-force : (Γ : SemCtx ∅) (A : SemTy κ) (t : SemTm Γ (■ (► A))) → SemTm Γ (■ A)
sem-force Γ A t x = sem-force' A (t x)
\end{code}
