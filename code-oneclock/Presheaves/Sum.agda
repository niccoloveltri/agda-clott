{-
In this file, we define the sum of presheaves.
It is defined pointwise.
-}
module Presheaves.Sum where

open import Data.Sum
open import Prelude
open import Presheaves.Presheaves

module _ (P Q : PSh) where

  private module P = PSh P
  private module Q = PSh Q

  -- Object part
  SumObj : Size → Set
  SumObj i = P.Obj i ⊎ Q.Obj i

  -- Morphism part
  SumMor : (i : Size) (j : Size≤ i)
    → SumObj i → SumObj j
  SumMor i j = map (P.Mor i j) (Q.Mor i j)

  -- Preservation of identity
  SumMorId : {i : Size} {x : SumObj i}
    → SumMor i i x ≡ x
  SumMorId {x = inj₁ p} = cong inj₁ P.MorId
  SumMorId {x = inj₂ q} = cong inj₂ Q.MorId

  -- Preservation of composition
  SumMorComp : {i : Size} {j : Size≤ i} {k : Size≤ j}
    → {x : SumObj i}
    → SumMor i k x ≡ SumMor j k (SumMor i j x)
  SumMorComp {x = inj₁ p} = cong inj₁ P.MorComp
  SumMorComp {x = inj₂ q} = cong inj₂ Q.MorComp
  
  Sum : PSh
  Sum = record
    { Obj = SumObj
    ; Mor = SumMor
    ; MorId = SumMorId
    ; MorComp = λ {_}{_}{_}{x} → SumMorComp {x = x}
    }
