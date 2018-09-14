module Clocks where

open import Size public
open import Level renaming (suc to lsuc; zero to lzero) public
open import Relation.Binary.PropositionalEquality public
open ≡-Reasoning public
open import Function hiding (const) public
open import Data.Product public

-- A clock is a size. 

Clock = Size

κ₀ : Clock
κ₀ = ∞

-- A tick on a clock κ is a size strictly smaller than κ.

Tick : Clock → Set
Tick κ = Size< κ

Size≤ : Clock → Set
Size≤ κ = Size< (↑ κ)

Tick= : Clock → Set
Tick= κ = Size≤ κ

{-
-- Less or equal relation on sizes

data _≤ˢ_ : Size → Size → Set where
  refl≤ˢ : {κ : Size} → κ ≤ˢ κ
  <-≤ˢ : {κ : Size} → (α : Size< κ) → α ≤ˢ κ

Size≤ : Clock → Set
Size≤ κ = Σ Size (λ α → α ≤ˢ κ)

Tick= : Clock → Set
Tick= κ = Size≤ κ

tick : {κ : Clock} → Tick= κ → Clock
tick (α , _) = α

trans≤ˢ : {κ κ' κ'' : Size} → κ ≤ˢ κ' → κ' ≤ˢ κ'' → κ ≤ˢ κ''
trans≤ˢ refl≤ˢ q = q
trans≤ˢ (<-≤ˢ α) refl≤ˢ = <-≤ˢ α
trans≤ˢ (<-≤ˢ α) (<-≤ˢ β) = <-≤ˢ α

coeˢ : {κ : Clock} (α : Tick= κ) → Tick (tick α) → Tick= κ
coeˢ (α , p) β = β , (trans≤ˢ (<-≤ˢ β) p)

coe : ∀{ℓ} {A : Clock → Set ℓ} {κ : Clock}
  → ((β : Tick= κ) → A (tick β))
  → (α : Tick κ) (β : Tick= α) → A (tick β)
coe g α (β , p) = g (β , trans≤ˢ p (<-≤ˢ α))

coe-eq : ∀{ℓ} {A : Clock → Set ℓ} {κ : Clock}
  → (g : (β : Tick= κ) → A (tick β))
  → (α : Tick κ) (β : Tick α) (γ : Tick= β)
  → coe (coe g α) β γ ≡ coe g β γ
coe-eq g α β (.β , refl≤ˢ) = refl
coe-eq g α β (.γ , <-≤ˢ γ) = refl
-}
