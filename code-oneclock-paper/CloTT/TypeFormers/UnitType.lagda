\AgdaHide{
\begin{code}
module CloTT.TypeFormers.UnitType where

open import Data.Product
open import Data.Unit
open import Prelude
open import Presheaves
open import CloTT.Structure
\end{code}
}

\begin{code}
Unit : (b : tag) → Ty b
Unit set = ⊤
Unit tot = Terminal
\end{code}


