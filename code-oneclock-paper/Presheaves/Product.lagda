\AgdaHide{
\begin{code}
module Presheaves.Product where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves

module _  (P Q : PSh) where

  private module P = PSh P
  private module Q = PSh Q
\end{code}
}

  \begin{code}
  ProdObj : Size → Set
  ProdObj i = P.Obj i × Q.Obj i
  \end{code}
  
  \begin{code}
  ProdMor : (i : Size) (j : Size< (↑ i))
    → ProdObj i → ProdObj j
  ProdMor i j = map (P.Mor i j) (Q.Mor i j)
  \end{code}

  \begin{code}
  ProdMorId : {i : Size} {x : ProdObj i}
    → ProdMor i i x ≡ x
  ProdMorId {i} {x} =
    begin
      (P.Mor i i (proj₁ x) , Q.Mor i i (proj₂ x))
    ≡⟨ cong (λ z → (z , Q.Mor i i (proj₂ x))) P.MorId ⟩
      (proj₁ x , Q.Mor i i (proj₂ x))
    ≡⟨ cong (λ z → (proj₁ x , z)) Q.MorId ⟩
      x
    ∎
  \end{code}
  
  \begin{code}
  ProdMorComp : {i : Size} {j : Size< (↑ i)} {k : Size< (↑ j)}
    → {x : ProdObj i}
    → ProdMor i k x ≡ ProdMor j k (ProdMor i j x)
  ProdMorComp {i} {j} {k} {x} =
    begin
      (P.Mor i k (proj₁ x) , Q.Mor i k (proj₂ x))
    ≡⟨ cong (λ z → (z , Q.Mor i k (proj₂ x))) P.MorComp ⟩
       (P.Mor j k (P.Mor i j (proj₁ x)) , Q.Mor i k (proj₂ x))
    ≡⟨ cong (λ z → (P.Mor j k (P.Mor i j (proj₁ x)) , z)) Q.MorComp ⟩
      (P.Mor j k (P.Mor i j (proj₁ x)) , Q.Mor j k (Q.Mor i j (proj₂ x)))
    ∎
  \end{code}

  \begin{code}
  Prod : PSh
  Prod = record
    { Obj = ProdObj
    ; Mor = ProdMor
    ; MorId = ProdMorId
    ; MorComp = ProdMorComp
    }
  \end{code}
