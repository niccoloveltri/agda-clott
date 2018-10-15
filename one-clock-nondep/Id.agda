module Id where

open import Clocks
open import Types
open import Fun

Id : ∀{ℓ} (c : Ty ℓ)
  → (x y : Tm ℓ c) → Clock → Set ℓ
Id (ty A nA aA _) (tm x nx) (tm y ny) κ = x κ ≡ y κ  

nextId : ∀{ℓ} (c : Ty ℓ)
  → (x y : Tm ℓ c)
  → (κ : Clock) (α : Tick= κ)
  → Tm.τ x κ ≡ Tm.τ y κ → Tm.τ x α ≡ Tm.τ y α
nextId (ty A nA aA _) (tm x nx) (tm y ny) κ α p =
  trans (sym (nx κ α)) (trans (cong (nA κ α) p) (ny κ α))

nextId-ass : ∀{ℓ} (c : Ty ℓ)
  → (x y : Tm ℓ c)
  → (κ : Clock) (α : Tick= κ) (β : Tick= α) (ρ : Id c x y κ)
  → nextId c x y α β (nextId c x y κ α ρ) ≡ nextId c x y κ β ρ
nextId-ass c x y κ α β ρ = uip

nextId-id : ∀{ℓ} (c : Ty ℓ)
  → (x y : Tm ℓ c)
  → (κ : Clock) (p : Id c x y κ) → nextId c x y κ κ p ≡ p
nextId-id c x y κ p = uip

Idᵀʸ : ∀{ℓ} (c : Ty ℓ)
  → (x y : Tm ℓ c) → Ty ℓ
Idᵀʸ c x y = ty (Id c x y) (nextId c x y) (nextId-ass c x y) (nextId-id c x y)

syntax Idᵀʸ c x y = x ≡[ c ] y 

toId : ∀{ℓ} {c : Ty ℓ}
  → {x y : Tm ℓ c}
  → ((κ : Clock) → Ty.A (Idᵀʸ c x y) κ)
  → Tm ℓ (x ≡[ c ] y)
toId p = tm p r
  where
    r : ∀ κ α → _
    r _ _ = uip

{-
Id⇒ : ∀{ℓ} {c d : ClTy ℓ}
  → {f g : ClTm ℓ (c ⇒ d)}
  → ((x : ClTm ℓ c) → ClTm ℓ (app f x ≡[ d ] app g x))
  → ClTm ℓ (f ≡[ c ⇒ d ] g)
Id⇒ {ℓ}{c}{f = f}{g} p = toId {x = f}{g}
  (λ κ → Pi-eq (funext (λ α → funext (λ x → {!ClTm.τ (p x') α!}))))
  where
    x' : ClTm ℓ c
    x' = tm {!!} {!!}
-}    
