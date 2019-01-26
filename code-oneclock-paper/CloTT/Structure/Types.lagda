\AgdaHide{
\begin{code}
module CloTT.Structure.Types where

open import Prelude
open import Presheaves public
\end{code}
}

Note that we are modelling a simple type theory and thus types do not depend on contexts.
For this reason, we interpet types the same way as contexts.

\begin{code}
SemTy : ClockCtx → Set₁
SemTy ∅ = Set
SemTy κ = PSh
\end{code}


