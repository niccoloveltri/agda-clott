module CloTT where

open import Prelude
open import Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers

data Type : ℕ → Set where
  𝟙 : (n : ℕ) → Type n
  prod : (n : ℕ) → Type n → Type n → Type n
  sum : (n : ℕ) → Type n → Type n → Type n
  arrow : (n : ℕ) → Type n → Type n → Type n
  clock-quant : (n : ℕ) → Name n → Type (suc n) → Type n
  later : (n : ℕ) → Name n → Type n → Type n

data Context : ℕ → Set where
  empty : (n : ℕ) → Context n
  extend : (n : ℕ) → Context n → Type n → Context n

data Term : (n : ℕ) → Context n → Type n → Set where
  var-t : {n : ℕ} (Γ : Context n) (A : Type n) → Term n (extend n Γ A) A
  weaken-t : {n : ℕ} (Γ : Context n) (A B : Type n) → Term n Γ B → Term n (extend n Γ A) B
  ⋆ : {n : ℕ} (Γ : Context n) → Term n Γ (𝟙 n)
  lambda-t : {n : ℕ} (Γ : Context n) (A B : Type n) → Term n (extend n Γ A) B → Term n Γ (arrow n A B)
  app-t : {n : ℕ} (Γ : Context n) (A B : Type n) → Term n Γ (arrow n A B) → Term n Γ A → Term n Γ B
  pair-t : {n : ℕ} (Γ : Context n) (A B : Type n) → Term n Γ A → Term n Γ B → Term n Γ (prod n A B)
  prj1-t : {n : ℕ} (Γ : Context n) (A B : Type n) → Term n Γ (prod n A B) → Term n Γ A
  prj2-t : {n : ℕ} (Γ : Context n) (A B : Type n) → Term n Γ (prod n A B) → Term n Γ B
  inlt : {n : ℕ} (Γ : Context n) (A B : Type n) → Term n Γ A → Term n Γ (sum n A B)
  inrt : {n : ℕ} (Γ : Context n) (A B : Type n) → Term n Γ B → Term n Γ (sum n A B)
  case : {n : ℕ} (Γ : Context n) (A B C : Type n) → Term n (extend n Γ A) C → Term n (extend n Γ B) C → Term n (extend n Γ (sum n A B)) C
  pure-t : {n : ℕ} (Γ : Context n) (κ : Name n) (A : Type n) → Term n Γ A → Term n Γ (later n κ A)
  fmap-t : {n : ℕ} (Γ : Context n) (κ : Name n) (A B : Type n) → Term n Γ (later n κ (arrow n A B)) → Term n Γ (later n κ A) → Term n Γ (later n κ B)
