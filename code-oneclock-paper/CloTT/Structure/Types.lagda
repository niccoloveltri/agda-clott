\AgdaHide{
\begin{code}
module CloTT.Structure.Types where

open import Prelude
open import Presheaves public
\end{code}
}

\begin{code}
Ty : tag → Set₁
Ty set = Set
Ty tot = PSh
\end{code}


