\AgdaHide{
\begin{code}
module Presheaves.Const where

open import Prelude
open import Presheaves.Presheaves

module _ (A : Set) where
\end{code}


  \begin{code}
  ConstObj : Size → Set
  ConstObj i = A
  \end{code}

  \begin{code}
  ConstMor : (i : Size) (j : Size< (↑ i))
    → ConstObj i → ConstObj j
  ConstMor i j x = x
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
}

There are several operations on presheaves.
We do not discuss them in detail since their definitions can be readily found in the literature.

The first operation takes a constant presheaf.
Given a set \AB{A}, we define a presheaf which sends each size to \AB{A}.
Morphisms are sent to the identity function and then the functor laws hold by reflexivity.

\begin{code}
Const : Set → PSh
\end{code}

\AgdaHide{
\begin{code}
Const A = record
  { Obj = ConstObj A
  ; Mor = ConstMor A
  ; MorId = ConstMorId A
  ; MorComp = ConstMorComp A
  }
\end{code}
}
