{-
The later modality as a presheaf.
We start by presenting a modality ▻.
Given a type A depending on n clocks and a name i, it returns a type ▻ A depending on n clocks.
The type ▻ A represents A, but lazily evaluated.
Lazy computations can be forced by providing a resources and these resources are ticks.
It is defined coinductively and force is how to make observations.
We define bisimilarity of lazy computations and we postulate that bisimilar computations are equal.
Lastly, we show that we can turn this into a type.

The structure of this file is as follows:
1. The ▻ modality
2. Bisimilarity implies equality
3. Object part
4. Morphism part
5. Preservation of identity
6. Preservation of composition
-}
module CloTT.TypeFormers.Later where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure

data SizeLt (i : Size) : Set where
  [_] : (j : Size< i) → SizeLt i

size : ∀ {i} → SizeLt i → Size
size [ j ] = j

Later : (Size → Set) → Size → Set
Later A i = (j : SizeLt i) → A (size j)

module _ (A : Ty tot) where

  -- 3. Object part
  ▻Obj : (i : Size) → Set
  ▻Obj i =
    Σ (Later (PSh.Obj A) i)
      (λ x → (j : Size< i) (k : Size≤ j)
        → PSh.Mor A j k (x [ j ]) ≡ x [ k ])

  -- 4. Morphism part
  ▻Mor : (i : Size) (j : Size≤ i)
    → ▻Obj i → ▻Obj j
  ▻Mor i j (x , p) = x , p

  -- 5. Preservation of identity
  ▻MorId : {i : Size} {x : ▻Obj i}
             → ▻Mor i i x ≡ x
  ▻MorId = refl

  -- 6. Preservation of composition
  ▻MorComp : {i : Size} {j : Size≤ i} {k : Size≤ j} {x : ▻Obj i}
               → ▻Mor i k x ≡ ▻Mor j k (▻Mor i j x)
  ▻MorComp = refl

  ▻ : Ty tot
  ▻ = record
    { Obj = ▻Obj
    ; Mor = ▻Mor
    ; MorId = ▻MorId
    ; MorComp = ▻MorComp
    }

{-
-- 1. The Later modality
record Later (A : Size → Set) (i : Size) : Set where
  coinductive
  field
    force : (j : Size< i) → A j
open Later public

-- 2. Bisimilarity implies equality
Bisim : {A : Size → Set} {i : Size} (x y : Later A i) → Set
Bisim x y = force x ≡ force y

postulate
  bisim : {A : Size → Set} {i : Size} {x y : Later A i} → Bisim x y → x ≡ y

module _ (A : Ty tot) where


  -- 3. Object part
  ▻Obj : (i : Size) → Set
  ▻Obj i =
    Σ (Later (PSh.Obj A) i)
      (λ x → (j : Size< i) (k : Size≤ j)
        → PSh.Mor A j k (force x j)
          ≡
          force x k) 

  -- 4. Morphism part
  ▻Mor : (i : Size) (j : Size≤ i)
    → ▻Obj i → ▻Obj j
  ▻Mor i j (x , p) = x , p

  -- 5. Preservation of identity
  ▻MorId : {i : Size} {x : ▻Obj i}
             → ▻Mor i i x ≡ x
  ▻MorId = refl

  -- 6. Preservation of composition
  ▻MorComp : {i : Size} {j : Size≤ i} {k : Size≤ j} {x : ▻Obj i}
               → ▻Mor i k x ≡ ▻Mor j k (▻Mor i j x)
  ▻MorComp = refl

  ▻ : Ty tot
  ▻ = record
    { Obj = ▻Obj
    ; Mor = ▻Mor
    ; MorId = ▻MorId
    ; MorComp = ▻MorComp
    }
-}
