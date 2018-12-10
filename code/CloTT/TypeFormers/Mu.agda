module CloTT.TypeFormers.Mu where

open import Data.Sum renaming (map to map⊎)
open import Data.Product renaming (map to map×)
open import Prelude
open import Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers.Later
open import CloTT.TypeFormers.ProductType
open import CloTT.TypeFormers.FunctionType

-- A grammar for polynomials
data Poly : ℕ → Set₁ where
  ∁ : ∀{n} → Ty n → Poly n
  I : ∀{n} → Poly n
  _⊞_ _⊠_ : ∀{n} → Poly n → Poly n → Poly n
  ► : ∀{n} → Poly n → Name n → Poly n

-- Evaluation of polynomials into natural transformations
eval : ∀{n} → Poly n → Ty n → Ty n
eval (∁ X) A = X
eval I A = A
eval (P ⊞ Q) A = Sum (eval P A) (eval Q A)
eval (P ⊠ Q) A = Prod (eval P A) (eval Q A)
eval (► P i) A = Later (eval P A) i

{-
Ideally, we would like to define the objects of a μ-type as follows:

data μObj {n : ℕ} (P : Poly n) (Δ : ClockCtx n) : Set where
  sup : Ty.Obj (eval P ?) Δ → μObj P Δ

But the hole expects a presheaf in Ty n.
μObj P should be the object part of this presheaf.
My idea was to define the rest of the structure of the presheaf by mutual induction with μObj.
I.e. to have somthing like:

mutual
  data μObj {n : ℕ} (P : Poly n) (Δ : ClockCtx n) : Set where
    sup : Ty.Obj (eval P (μ P)) Δ → μObj P Δ

  μMor : {n : ℕ} (P : Poly n) (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ) → μObj P Δ → μObj P Δ'
  μMor P Δ Δ' t = {!!}

  μMorId : {n : ℕ} (P : Poly n) {Δ : ClockCtx n}{x : μObj P Δ} → μMor P Δ _ x ≡ x
  μMorId P = {!!}

  μMorComp : {n : ℕ} (P : Poly n) {Δ : ClockCtx n} {Δ' : ClockCtx≤ Δ} {Δ'' : ClockCtx≤ Δ'} {x : μObj P Δ}
    → μMor P Δ _ x ≡ μMor P Δ' Δ'' (μMor P Δ Δ' x)
  μMorComp P = {!!}

  μ : {n : ℕ} → Poly n → Ty n
  μ P = record { Obj = μObj P ; Mor = μMor P ; MorId = μMorId P ; MorComp = λ {Δ}{Δ'}{Δ''}{x} → μMorComp P {Δ}{Δ'}{Δ''}{x} }


But this is rejected by the positivity checker.
So in the 1-clock case I decided to define eval in several pieces.
-}

-- First, following the formalization of the 1-clock model, I define ▻ differently.
-- Here it takes as input A : ClockCtx n → Set, not A : Ty n.

record ▻' {n : ℕ} (A : ClockCtx n → Set) (i : Name n) (Δ : ClockCtx n) : Set where
  coinductive
  field
    force : (α : TickCtx Δ i) → A (Δ [ i ↦ α ])
open ▻' public

Bisim' : ∀{n} {A} {i} {Δ : ClockCtx n} (x y : ▻' A i Δ) → Set
Bisim' x y = force x ≡ force y

postulate
  bisim' : ∀{n} {A} {i} {Δ : ClockCtx n} {x y : ▻' A i Δ} → Bisim' x y → x ≡ y

-- Then I defined the different pieces of eval by mutual recursion.
evalObj : {n : ℕ} (P : Poly n)
         (A : ClockCtx n → Set)
         (m : (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ) → A Δ → A Δ')
         (c : {Δ : ClockCtx n} {Δ' : ClockCtx≤ Δ} {Δ'' : ClockCtx≤ Δ'} {x : A Δ} → m Δ _ x ≡ m Δ' Δ'' (m Δ Δ' x))
        → ClockCtx n → Set
evalMor : {n : ℕ} (P : Poly n)
         (A : ClockCtx n → Set)
         (m : (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ) → A Δ → A Δ')
         (c : {Δ : ClockCtx n} {Δ' : ClockCtx≤ Δ} {Δ'' : ClockCtx≤ Δ'} {x : A Δ} → m Δ _ x ≡ m Δ' Δ'' (m Δ Δ' x))
         (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ) → evalObj P A m c Δ → evalObj P A m c Δ'
evalMorComp : {n : ℕ} (P : Poly n)
         (A : ClockCtx n → Set)
         (m : (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ) → A Δ → A Δ')
         (c : {Δ : ClockCtx n} {Δ' : ClockCtx≤ Δ} {Δ'' : ClockCtx≤ Δ'} {x : A Δ} → m Δ _ x ≡ m Δ' Δ'' (m Δ Δ' x))
         {Δ : ClockCtx n} {Δ' : ClockCtx≤ Δ} {Δ'' : ClockCtx≤ Δ'} {x : evalObj P A m c Δ}
         → evalMor P A m c Δ _ x ≡ evalMor P A m c Δ' Δ'' (evalMor P A m c Δ Δ' x)
evalObj (∁ X) A m c = Ty.Obj X
evalObj I A m c = A
evalObj (P ⊞ Q) A m c Δ = evalObj P A m c Δ ⊎ evalObj Q A m c Δ
evalObj (P ⊠ Q) A m c Δ = evalObj P A m c Δ × evalObj Q A m c Δ
evalObj (► P i) A m c Δ =
  Σ (▻' (evalObj P A m c) i Δ)
    (λ x → (α : Tick (Δ i)) (α' : Size≤ α) → evalMor P A m c  (Δ [ i ↦ α ]) _ (force x α) ≡ force x (transSize<≤ {Δ i} {α} α'))
evalMor (∁ X) A m c Δ Δ' x = Ty.Mor X Δ Δ' x
evalMor I A m c Δ Δ' x = m Δ Δ' x
evalMor (P ⊞ Q) A m c Δ Δ' (inj₁ x) = inj₁ (evalMor P A m c Δ Δ' x)
evalMor (P ⊞ Q) A m c Δ Δ' (inj₂ x) = inj₂ (evalMor Q A m c Δ Δ' x)
evalMor (P ⊠ Q) A m c Δ Δ' (x , y) = (evalMor P A m c Δ Δ' x) , (evalMor Q A m c Δ Δ' y)
force (proj₁ (evalMor (► P i) A m c Δ Δ' (x , p))) α = evalMor P A m c (Δ [ i ↦ α ]) _ (force x _)
proj₂ (evalMor (► P i) A m c Δ Δ' (x , p)) α α' =
  begin
    evalMor P A m c (Δ' [ i ↦ α ]) _ (evalMor P A m c (Δ [ i ↦ α ]) _ (force x _))
  ≡⟨ sym (evalMorComp P A m c) ⟩
    evalMor P A m c (Δ [ i ↦ α ]) _ (force x _)
  ≡⟨ evalMorComp P A m c ⟩
    evalMor P A m c (Δ [ i ↦ α' ]) _ (evalMor P A m c (Δ [ i ↦ α ]) _ (force x _))
  ≡⟨ cong (evalMor P A m c (Δ [ i ↦ α' ]) _) (p _ α') ⟩
    evalMor P A m c (Δ [ i ↦ α' ]) _ (force x _)
  ∎
evalMorComp (∁ X) A m c = Ty.MorComp X
evalMorComp I A m c = c
evalMorComp (P ⊞ Q) A m c {x = inj₁ x} = cong inj₁ (evalMorComp P A m c)
evalMorComp (P ⊞ Q) A m c {x = inj₂ x} = cong inj₂ (evalMorComp Q A m c)
evalMorComp (P ⊠ Q) A m c = cong₂ _,_ (evalMorComp P A m c) (evalMorComp Q A m c)
evalMorComp (► P i) A m c = Σ≡-uip (funext (λ { _ → funext (λ _ → uip)})) (bisim' (funext (λ { _ → evalMorComp P A m c })))

-- Notice that in the 1-clock case I define evalObj and evalMor mutually, but evalMorComp is not necessary.
-- Here the situation is more complicated and one needs evalMorComp to deal with the ► case in the construction of evalMor. 

-- In the 1-clock case, the following definition is accepted.
-- Here, I get two errors: a positivity error and a non-termination error.
-- As in the 1-clock case, I need to define a function eval-μMor that practically behaves like evalMor,
-- but in the 1-clock case is needed to convince the termination checker.

-- Formation rule
mutual
  data μObj {n : ℕ} (P : Poly n) (Δ : ClockCtx n) : Set where
    sup : evalObj P (μObj P) (μMor P) (μMorComp P) Δ → μObj P Δ

  μMor : ∀{n}(P : Poly n) (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ) → μObj P Δ → μObj P Δ'
  μMor P Δ Δ' (sup t) = sup (eval-μMor P P Δ Δ' t)

  μMorComp : ∀{n}(P : Poly n) {Δ : ClockCtx n} {Δ' : ClockCtx≤ Δ} {Δ'' : ClockCtx≤ Δ'} {x : μObj P Δ}
    → μMor P Δ _ x ≡ μMor P Δ' Δ'' (μMor P Δ Δ' x)
  μMorComp P = {!!}

  eval-μMor : ∀{n} (P Q : Poly n) (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ)
    → evalObj Q (μObj P) (μMor P) (μMorComp P) Δ → evalObj Q (μObj P) (μMor P) (μMorComp P) Δ'
  eval-μMor P (∁ X) Δ Δ' x = Ctx.Mor X Δ Δ' x
  eval-μMor P I Δ Δ' x = μMor P Δ Δ' x
  eval-μMor P (Q ⊞ Q₁) Δ Δ' (inj₁ x) = inj₁ (eval-μMor P Q Δ Δ' x)
  eval-μMor P (Q ⊞ Q₁) Δ Δ' (inj₂ y) = inj₂ (eval-μMor P Q₁ Δ Δ' y)
  eval-μMor P (Q ⊠ Q₁) Δ Δ' (x , y) = (eval-μMor P Q Δ Δ' x) , (eval-μMor P Q₁ Δ Δ' y)
  force (proj₁ (eval-μMor P (► Q i) Δ Δ' (x , p))) α = eval-μMor P Q (Δ [ i ↦ α ]) _ (force x _)
  proj₂ (eval-μMor P (► Q i) Δ Δ' x) = {!!}

