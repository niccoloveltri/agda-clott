{-
In this file, we define the main operations on contexts.
1. We always have the empty context.
2. Contexts can be extended with types
3. We can use variables in the context. This represents the following rule.
Γ ,, A ⊢ x : A
4. We can weaken the context. This represents the following rule
  Γ ⊢ t : B
--------------
Γ ,, A ⊢ t : B
-}
module CloTT.Structure.ContextOperations where

open import Data.Product
open import Prelude
open import Presheaves
open import CloTT.Structure.Contexts
open import CloTT.Structure.Types
open import CloTT.Structure.Terms

-- 1. The empty context
--∙ : Ctx set -- ∙ = \.
--∙ = {!!}

-- 2. Context extension
_,,_ : {b : Bool} → Ctx b → Ty b → Ctx b
_,,_ {set} Γ A = Γ × A
_,,_ {tot} Γ A = Prod Γ A

-- 3. The variable rule
var : {b : Bool} (Γ : Ctx b) (A : Ty b) → Tm b (Γ ,, A) A
var {set} Γ A = proj₂
proj₁ (var {tot} Γ A) i (γ , x) = x
proj₂ (var {tot} Γ A) i j (γ , x) = refl


-- 4. Weakening
weaken : {b : Bool}(Γ : Ctx b) (A B : Ty b) → Tm b Γ B → Tm b (Γ ,, A) B
weaken {set} Γ A B t (x , _) = t x
proj₁ (weaken {tot} Γ A B (t , p)) i (x₁ , x₂) = t i x₁
proj₂ (weaken {tot} Γ A B (t , p)) i j (x₁ , x₂) = p i j x₁
