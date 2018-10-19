
module Later where

open import Basics
open import Types
open import Data.Nat
open import Data.Fin
open import Data.Fin.Properties
open import Data.Product
open import ClockContexts
open import Size
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module _ {n : ℕ} (A : Ty n) (i : Fin n) where

  module A = Ty A

  record ▻ (Δ : ClockCtx n) : Set where
    coinductive
    field
      force : (α : TickCtx Δ i) → A.Obj (Δ [ i ↦ α ])
  open ▻

  _∼_ : {Δ : ClockCtx n} (x y : ▻ Δ) → Set
  x ∼ y = force x ≡ force y

  postulate
    bisim : {Δ : ClockCtx n} {x y : ▻ Δ} → x ∼ y → x ≡ y

  LaterObj : (Δ : ClockCtx n) → Set
  LaterObj Δ =
    Σ (▻ Δ)
      (λ x → (α : Tick (Δ i)) (α' : Size≤ α)
        → A.Mor (Δ [ i ↦ α ]) _ (force x α)
          ≡
          force x (transSize< {Δ i}{α} α')) 

  LaterObj' : (Δ : ClockCtx n) → Set
  LaterObj' Δ =
    Σ (▻ Δ)
      (λ x → (α : Tick (Δ i)) (α' : Size< α)
        → A.Mor (Δ [ i ↦ α ]) _ (force x α)
          ≡
          force x (transSize< {Δ i}{α} α'))

  LaterMor' : (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ)
    → ▻ Δ → ▻ Δ'
  force (LaterMor' Δ Δ' x) α =
    A.Mor (Δ [ i ↦ α ]) _ (force x (transSize<2 {Δ i}{Δ' i} α))

  LaterMor : (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ)
    → LaterObj Δ → LaterObj Δ'
  LaterMor Δ Δ' (x , p) =
    LaterMor' Δ Δ' x ,
    (λ {α α' →
      begin
        A.Mor (Δ' [ i ↦ α ]) _
          (A.Mor (Δ [ i ↦ α ]) _ (force x (transSize<2 {Δ i}{Δ' i} α)))
      ≡⟨ sym A.MorComp ⟩ 
        A.Mor (Δ [ i ↦ α ]) _ (force x (transSize<2 {Δ i}{Δ' i} α))
      ≡⟨ A.MorComp ⟩
        A.Mor (Δ [ i ↦ α' ]) _ (A.Mor (Δ [ i ↦ α ] ) _ (force x _))
      ≡⟨ cong (A.Mor (Δ [ i ↦ α' ]) _) (p _ _) ⟩ 
        A.Mor (Δ [ i ↦ α' ]) _
          (force x (transSize<2 {Δ i} α'))
      ∎})

  forceLaterMorId : {Δ : ClockCtx n} {x : ▻ Δ}
             → force (LaterMor' Δ (coeClockCtx Δ) x) ≡ force x
  forceLaterMorId = funext (λ {j → A.MorId})

  LaterMorId : {Δ : ClockCtx n} {x : LaterObj Δ}
             → LaterMor Δ (coeClockCtx Δ) x ≡ x
  LaterMorId {Δ} {x₁ , x₂} =
     Σ≡-uip (funext (λ {_ → funext (λ _ → uip)}))
            (bisim (forceLaterMorId {_} {x₁}))

  forceLaterMorComp : {Δ : ClockCtx n} {Δ' : ClockCtx≤ Δ} {Δ'' : ClockCtx≤ Δ'} {x : ▻ Δ}
               → force (LaterMor' Δ _ x) ≡ force (LaterMor' Δ' Δ'' (LaterMor' Δ Δ' x))
  forceLaterMorComp = funext (λ {j → A.MorComp})

  LaterMorComp : {Δ : ClockCtx n} {Δ' : ClockCtx≤ Δ} {Δ'' : ClockCtx≤ Δ'} {x : LaterObj Δ}
               → LaterMor Δ _ x ≡ LaterMor Δ' Δ'' (LaterMor Δ Δ' x)
  LaterMorComp {_} {_} {_} {x₁ , x₂} =
    Σ≡-uip (funext (λ {_ → funext (λ _ → uip)}))
           (bisim (forceLaterMorComp {_} {_} {_} {x₁}))

  Later : Ty n
  Later = record
    { Obj = LaterObj
    ; Mor = LaterMor
    ; MorId = LaterMorId
    ; MorComp = LaterMorComp
    }


{-

  LaterObj : (Δ : ClockCtx n) → Set
  LaterObj Δ =
    Σ (▻ Δ)
      (λ x → (α : Tick (Δ i)) (α' : Size≤ ((Δ [ i ↦ α ]) i))
        → A.Mor (Δ [ i ↦ α ]) ((Δ [ i ↦ α ]) [ i ↦ α' ]≤) (force x α)
          ≡
          subst A.Obj {!!} (force x {!!}))
{-
      (λ x → (α : Tick (Δ i)) (α' : Size≤ α)
        → A.Mor (Δ [ i ↦ α ]) ((Δ [ i ↦ α ])
                [ i ↦ subst Size≤ (sym (id[↦] {Δ = Δ}{i}{α})) α' ]≤) (force x α)
          ≡
          subst A.Obj {!!} (force x (transSize< {Δ i}{α} α' ))) 
-}


  Later : Ty n
  Later = record
    { Obj = {!!} --LaterObj
    ; Mor = {!!}
    ; MorId = {!!}
    ; MorComp = {!!}
    }
-}
