\AgdaHide{
\begin{code}
module CloTT.Structure.Contexts where

open import Prelude
open import Presheaves public
\end{code}
}

Next we define how to interpret contexts.
Note that in the syntax, contexts depend on clock contexts.
Hence, the interpretation should depend on \AD{tag}, which is the interpretation of clock contexts.

There are two possible cases.
Either the clock context is empty and then the context is a set.
Otherwise, there is a single clock and then we use presheaves.

\begin{code}
Ctx : ClockContext → Set₁
Ctx ∅ = Set
Ctx κ = PSh
\end{code}
