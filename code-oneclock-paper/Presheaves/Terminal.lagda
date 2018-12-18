\AgdaHide{
\begin{code}
module Presheaves.Terminal where

open import Data.Unit
open import Presheaves.Const 
open import Presheaves.Presheaves
\end{code}
}

\begin{code}
Terminal : PSh
Terminal = Const ⊤
\end{code}
