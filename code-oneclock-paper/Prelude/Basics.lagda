\AgdaHide{
\begin{code}
module Prelude.Basics where

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Size
\end{code}
}

We work in Martin-L\"of type theory extended with functional
extensionality, uniqueness of identity proofs (\F{uip}) and sized
types.  Practically, we work in Agda, which supports sized types and
where \F{uip} holds by default. In this section we give a brief
overview of these principles and we introduce the basic
type-theoretical definitions thet we employ in our formalization.

We write \Ar{=} for judgemental equality and \Ar{≡} for propositional
equality. Implicit arguments of functions are delimited by curly
brackets. We write \F{Set} and \F{Set₁} for the first and second
universe of types. We do not use higher universes.

The principle of functional extensionality states that two parallel
functions \Ar{f} and \Ar{g} are equal whenever \Ar{f x} and \Ar{g x}
are equal for all inputs \Ar{x}. This principle is not provable in
Agda, so we need to postulate it.

\begin{code}
postulate
  funext : {A : Set} {B : A → Set} {f g : (x : A) → B x}
    → ((x : A) → f x ≡ g x) → f ≡ g
\end{code}

Uniqueness of identity proofs states that there exist at most one
identity proof between any two terms. Agda natively supports this
principle, so we can easily construct a proof for it.

\begin{code}
uip : {A : Set} {x y : A} {p q : x ≡ y} → p ≡ q
uip {A} {x} {y} {refl} {refl} = refl
\end{code}

Lastly, we use sized types \cite{A-sized,AVW-normalization} for productivity checks.
This works with the following principle: if in each recursive call the sizes decrease, then the function is productive.

Let us be more concrete.
In Agda, there is a type \AD{Size}.
This type is ordered meaning that for every \AB{i} we have a type \AD{Size<} \AB{i}.
There is a coercion from \AD{Size<} \AB{i} to \AD{Size}.
We use that this order is well-founded and for this reason, functions are productive if in every recursive call some size decreases \cite{A-sized}.
Lastly, we use the size \F{∞}, and for each size \AB{i} we have \AB{i} : \AD{Size<} \F{∞}.

\AgdaHide{
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
