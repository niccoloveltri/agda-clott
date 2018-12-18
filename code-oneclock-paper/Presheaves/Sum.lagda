\AgdaHide{
\begin{code}
module Presheaves.Sum where

open import Data.Sum
open import Prelude
open import Presheaves.Presheaves

module _ (P Q : PSh) where

  private module P = PSh P
  private module Q = PSh Q
\end{code}
}
  \begin{code}
  SumObj : Size → Set
  SumObj i = P.Obj i ⊎ Q.Obj i
  \end{code}

  \begin{code}
  SumMor : (i : Size) (j : Size< (↑ i))
    → SumObj i → SumObj j
  SumMor i j = map (P.Mor i j) (Q.Mor i j)
  \end{code}
  
  \begin{code}
  SumMorId : {i : Size} {x : SumObj i}
    → SumMor i i x ≡ x
  SumMorId {i} {inj₁ p} =
    begin
      inj₁ (P.Mor i i p)
    ≡⟨ cong inj₁ P.MorId ⟩
      inj₁ p
    ∎
  SumMorId {i} {inj₂ q} =
    begin
      inj₂ (Q.Mor i i q)
    ≡⟨ cong inj₂ Q.MorId ⟩
      inj₂ q
    ∎
  \end{code}

  \begin{code}
  SumMorComp : {i : Size} {j : Size< (↑ i)} {k : Size< (↑ j)}
    → {x : SumObj i}
    → SumMor i k x ≡ SumMor j k (SumMor i j x)
  SumMorComp {i} {j} {k} {inj₁ p} =
    begin
      inj₁ (P.Mor i k p)
    ≡⟨ cong inj₁ P.MorComp ⟩
      inj₁ (P.Mor j k (P.Mor i j p))
    ∎
  SumMorComp {i} {j} {k} {inj₂ q} =
    begin
      inj₂ (Q.Mor i k q)
    ≡⟨ cong inj₂ Q.MorComp ⟩
      inj₂ (Q.Mor j k (Q.Mor i j q))
    ∎
  \end{code}

  \begin{code}
  Sum : PSh
  Sum = record
    { Obj = SumObj
    ; Mor = SumMor
    ; MorId = SumMorId
    ; MorComp = λ {_}{_}{_}{x} → SumMorComp {x = x}
    }
  \end{code}
