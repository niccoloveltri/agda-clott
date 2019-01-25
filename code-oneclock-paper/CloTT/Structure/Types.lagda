\AgdaHide{
\begin{code}
module CloTT.Structure.Types where

open import Prelude
open import Presheaves public
\end{code}
}

Types are defined in a similar way.
Note that we are modelling a simple type theory and thus types do not depend on contexts.
For this reason, we can interpet types the same way as contexts.

\begin{code}
SemTy : ClockCtx → Set₁
SemTy ∅ = Set
SemTy κ = PSh
\end{code}


