{-
In this file, we define the product of presheaves.
It is defined pointwise.
-}
module Presheaves.Product where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves

module _  (P Q : PSh) where

  private module P = PSh P
  private module Q = PSh Q

  -- Object part
  ProdObj : Size → Set
  ProdObj i = P.Obj i × Q.Obj i

  -- Morphism part
  ProdMor : (i : Size) (j : Size≤ i)
    → ProdObj i → ProdObj j
  ProdMor i j = map (P.Mor i j) (Q.Mor i j)

  -- Preservation of identity
  ProdMorId : {i : Size} {x : ProdObj i}
    → ProdMor i i x ≡ x
  ProdMorId = cong₂ _,_ P.MorId Q.MorId

  -- Preservation of composition
  ProdMorComp : {i : Size} {j : Size≤ i} {k : Size≤ j}
    → {x : ProdObj i}
    → ProdMor i k x ≡ ProdMor j k (ProdMor i j x)
  ProdMorComp = cong₂ _,_ P.MorComp Q.MorComp
  
  Prod : PSh
  Prod = record
    { Obj = ProdObj
    ; Mor = ProdMor
    ; MorId = ProdMorId
    ; MorComp = ProdMorComp
    }
