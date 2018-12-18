\AgdaHide{
\begin{code}
module Presheaves.Sum where

open import Data.Sum
open import Prelude
open import Presheaves.Presheaves

module _ (P Q : PSh) where
  open PSh
\end{code}
}
  \begin{code}
  SumObj : Size → Set
  SumObj i = Obj P i ⊎ Obj Q i
  \end{code}

  \begin{code}
  SumMor : (i : Size) (j : Size< (↑ i))
    → SumObj i → SumObj j
  SumMor i j = map (Mor P i j) (Mor Q i j)
  \end{code}
  
  \begin{code}
  SumMorId : {i : Size} {x : SumObj i}
    → SumMor i i x ≡ x
  SumMorId {i} {inj₁ p} =
    begin
      inj₁ (Mor P i i p)
    ≡⟨ cong inj₁ (MorId P) ⟩
      inj₁ p
    ∎
  SumMorId {i} {inj₂ q} =
    begin
      inj₂ (Mor Q i i q)
    ≡⟨ cong inj₂ (MorId Q) ⟩
      inj₂ q
    ∎
  \end{code}

  \begin{code}
  SumMorComp : {i : Size} {j : Size< (↑ i)} {k : Size< (↑ j)}
    → {x : SumObj i}
    → SumMor i k x ≡ SumMor j k (SumMor i j x)
  SumMorComp {i} {j} {k} {inj₁ p} =
    begin
      inj₁ (Mor P i k p)
    ≡⟨ cong inj₁ (MorComp P) ⟩
      inj₁ (Mor P j k (Mor P i j p))
    ∎
  SumMorComp {i} {j} {k} {inj₂ q} =
    begin
      inj₂ (Mor Q i k q)
    ≡⟨ cong inj₂ (MorComp Q) ⟩
      inj₂ (Mor Q j k (Mor Q i j q))
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
