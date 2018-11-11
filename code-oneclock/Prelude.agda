module Prelude where
  open import Size public
  open import Function public
  open import Data.Bool public hiding (_≟_; decSetoid) renaming (false to set; true to tot)
  open import Data.Nat public hiding (_≟_)
  open import Relation.Binary.PropositionalEquality public
  open ≡-Reasoning public
  
  open import Prelude.Basics public

