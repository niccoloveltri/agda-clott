\AgdaHide{
\begin{code}
module CloTT.Structure.Types where

open import Prelude
open import Presheaves public
\end{code}
}
Note that \GTT\ is a simple type theory and thus types do not depend on contexts.
For this reason, we define the type \F{SemTy} of semantic types is the same way as \F{SemCtx}.

\AgdaHide{
\begin{code}
SemTy : ClockCtx → Set₁
SemTy ∅ = Set
SemTy κ = PSh
\end{code}
}
