\AgdaHide{
\begin{code}
module Prelude.Basics where

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Size
\end{code}
}

\begin{code}
postulate
  funext : {A : Set} {B : A → Set} {f g : (x : A) → B x}
    → ((x : A) → f x ≡ g x) → f ≡ g

uip : {A : Set} {x y : A} {p q : x ≡ y} → p ≡ q
uip {p = refl} {refl} = refl
\end{code}

\begin{code}
data tag : Set where
  set : tag
  tot : tag
\end{code}

\AgdaHide{
\begin{code}
Σ≡ : {A : Set}{P : A → Set}
  → {a a' : A} {p : P a} {p' : P a'}
  → (e : a ≡ a') → subst P e p ≡ p' → (a , p) ≡ (a' , p')
Σ≡ refl refl = refl

isProp : Set → Set
isProp P = {x y : P} → x ≡ y

Σ≡-uip : {A : Set}{P : A → Set}
  → ({a : A} → isProp (P a))
  → {a a' : A} {p : P a} {p' : P a'}
  → (e : a ≡ a') → (a , p) ≡ (a' , p')
Σ≡-uip q refl = cong (_,_ _) q
\end{code}

Dependent functions preserve equality
\begin{code}
cong-dep : {A : Set}{P : A → Set}
  → (f : (a : A) → P a)
  → {x y : A} 
  → (e : x ≡ y) → subst P e (f x) ≡ f y
cong-dep f refl = refl
\end{code}

Functions with two arguments preserve equality
\begin{code}
cong₂-dep : {A B : Set}{P : A → Set}
  → (f : (a : A) (p : P a) → B)
  → {a a' : A} {p : P a} {p' : P a'}
  → (e : a ≡ a') → subst P e p ≡ p' → f a p ≡ f a' p'
cong₂-dep f refl refl = refl
\end{code}

Transport of a composition
\begin{code}
subst-trans : {A : Set}{P : A → Set}
  → {x y z : A}(e : x ≡ y)(e' : y ≡ z)
  → {p : P x}
  → subst P e' (subst P e p) ≡ subst P (trans e e') p
subst-trans refl refl = refl
\end{code}
}
