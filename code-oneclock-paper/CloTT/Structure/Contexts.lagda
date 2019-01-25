\AgdaHide{
\begin{code}
module CloTT.Structure.Contexts where

open import Prelude
open import Presheaves public
\end{code}
}

For the semantics, we first give an interpretation of contexts, types, and terms.
Since contexts depending on clock contexts, there are two cases to consider.
If the clock context is empty, then we interpret the context as a set.
Otherwise, there is a single clock, and then we use presheaves.

\begin{code}
SemCtx : ClockCtx → Set₁
SemCtx ∅ = Set
SemCtx κ = PSh
\end{code}
