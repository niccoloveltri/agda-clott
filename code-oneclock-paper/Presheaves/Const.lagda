\AgdaHide{
\begin{code}
module Presheaves.Const where

open import Prelude
open import Presheaves.Presheaves

module _ (A : Set) where
\end{code}
}

  \begin{code}
  ConstObj : Size → Set
  ConstObj _ = A
  \end{code}

  \begin{code}
  ConstMor : (i : Size) (j : Size< (↑ i))
    → ConstObj i → ConstObj j
  ConstMor _ _ x = x
  \end{code}

  \begin{code}
  ConstMorId : {i : Size} {x : A}
    → ConstMor i i x ≡ x
  ConstMorId = refl
  \end{code}
  
  \begin{code}
  ConstMorComp : {i : Size} {j : Size< (↑ i)} {k : Size< (↑ j)}
    → {x : ConstObj i}
    → ConstMor i k x ≡ ConstMor j k (ConstMor i j x)
  ConstMorComp = refl
  \end{code}

  \AgdaHide{
  \begin{code}
  Const : PSh
  Const = record
    { Obj = ConstObj
    ; Mor = ConstMor
    ; MorId = ConstMorId
    ; MorComp = ConstMorComp
    }
  \end{code}
  }
