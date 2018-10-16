module Terminal where

open import Const 
open import Data.Unit
open import Data.Nat
open import Presheaves

Terminal : {n : ℕ} → PSh n
Terminal = Const ⊤
