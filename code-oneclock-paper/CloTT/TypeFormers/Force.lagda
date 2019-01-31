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

Finally, we sow how to interpret \AIC{force} and for that, we first define an auxilliary function \AF{sem-force'}.
Given a type \AB{A} and an inhabitant \AB{t} of \F{■}(\F{►} \Ar{A}), this map gives an element of \F{■} \AB{A}.
For \AFi{■cone} (\AF{sem-force'} \AB{t}), we need to give an element of \AFi{Obj} \AB{A} for each size \AB{i}.

To define this element, we use that the type of \AB{t} uses both the box and later modality.
Using the field \AFi{■cone} of \AB{t}, we get an term \AB{t'} of type \F{►Obj} \AB{A} \AB{i} for each size \AB{i}.
Note that we also have a function \AFi{►cone} \AB{t'} which gives for each size \AB{j} smaller than \AB{i} an \AFi{Obj} \AB{A} \AB{i}.
Hence, for an inhabitant of \AFi{Obj} \AB{A} \AB{i}, it suffices to find a size \AB{j} greater than \AB{i}.
Since \F{∞} is bigger than each size \AB{i}, we define
\remove{
Finally, we describe the interpretation of the term \AIC{force}.
We first define an auxilliary function \AF{sem-force'}.  Given a type
\AB{A} and an inhabitant \AB{t} of \F{■}(\F{►} \Ar{A}), this map gives an element of \F{■} \AB{A}.
For \AFi{■cone} (\AF{sem-force'} \AB{t}), we need to give an element of \AFi{Obj} \AB{A} for each size \AB{i}.
By definition, \AFi{■cone} \AB{t} \F{∞} has type \F{►Obj} \Ar{A} \F{∞}.
Since the size \F{∞} is bigger than \AB{i}, we can apply \Fi{►cone} (\Fi{■cone} \Ar{t} \F{∞}) to \IC{[} \Ar{i} \IC{]} to obtain an inhabitant of type \AFi{Obj} \AB{A}
\AB{i}.
We define the field \AFi{■com} of \F{sem-force'} similarly.
}
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
