\AgdaHide{
\begin{code}
module Presheaves.Product where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves

module _  (P Q : PSh) where
  open PSh
\end{code}
}

Products and sums of presheaves are defined pointwise.
More precisely, we define the product as follows
  \begin{code}
  ProdObj : Size → Set
  ProdObj i = Obj P i × Obj Q i
  \end{code}
The sum is defined similarly.
\AgdaHide{
  \begin{code}
  ProdMor : (i : Size) (j : Size< (↑ i))
    → ProdObj i → ProdObj j
  ProdMor i j = map (Mor P i j) (Mor Q i j)
  \end{code}

  \begin{code}
  ProdMorId : {i : Size} {x : ProdObj i}
    → ProdMor i i x ≡ x
  ProdMorId {i} {x} =
    begin
      (Mor P i i (proj₁ x) , Mor Q i i (proj₂ x))
    ≡⟨ cong (λ z → (z , _)) (MorId P) ⟩
      (proj₁ x , Mor Q i i (proj₂ x))
    ≡⟨ cong (λ z → (_ , z)) (MorId Q) ⟩
      x
    ∎
  \end{code}
  
  \begin{code}
  ProdMorComp : {i : Size} {j : Size< (↑ i)} {k : Size< (↑ j)}
    → {x : ProdObj i}
    → ProdMor i k x ≡ ProdMor j k (ProdMor i j x)
  ProdMorComp {i} {j} {k} {x} =
    begin
      (Mor P i k (proj₁ x) , Mor Q i k (proj₂ x))
    ≡⟨ cong (λ z → (z , _)) (MorComp P) ⟩
      (Mor P j k (Mor P i j (proj₁ x)) , Mor Q i k (proj₂ x))
    ≡⟨ cong (λ z → (_ , z)) (MorComp Q) ⟩
      (Mor P j k (Mor P i j (proj₁ x)) , Mor Q j k (Mor Q i j (proj₂ x)))
    ∎
  \end{code}

\begin{code}
Prod : PSh → PSh → PSh
\end{code}

\begin{code}
Prod P Q = record
  { Obj = ProdObj P Q
  ; Mor = ProdMor P Q
  ; MorId = ProdMorId P Q
  ; MorComp = ProdMorComp P Q
  }
\end{code}
}
