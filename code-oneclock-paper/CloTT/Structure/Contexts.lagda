\AgdaHide{
\begin{code}
module CloTT.Structure.Contexts where

open import Prelude
open import Presheaves public
\end{code}
}

\begin{code}
Ctx : tag → Set₁
Ctx set = Set
Ctx tot = PSh
\end{code}
