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
overview of these principles and we introduce the basic Agda notation
%type-theoretical definitions
that we employ in our formalization.

We write \Ar{=} for judgemental equality and \Ar{≡} for propositional
equality. Implicit arguments of functions are delimited by curly
brackets. We write \F{Set} and \F{Set₁} for the first and second
universe of types. In addition, Agda supports higher universes and
these are denoted by \F{Set} \AB{ℓ} for each universe level \AB{ℓ}.

The principle of functional extensionality states that every two
functions \Ar{f} and \Ar{g} in the same function space are
 equal whenever \Ar{f x} and \Ar{g x} are equal for all
inputs \Ar{x}. This principle is not provable in Agda, so we need to
postulate it.
\begin{code}
postulate
  funext : {A : Set} {B : A → Set} {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g
\end{code}

Uniqueness of identity proofs states that all proofs of identity are
equal. Agda natively supports this principle and we can prove it by
induction.
\begin{code}
uip : {A : Set} {x y : A} {p q : x ≡ y} → p ≡ q
uip {A} {x} {y} {refl} {refl} = refl
\end{code}

Agda also natively support sized types
\cite{A-sized,AVW-normalization}. Intuitively, a sized type is a type
annotated with an abstract ordinal indicating the number of possible
unfoldings that can be performed of elements of the type.  These
abstract ordinals, called sizes, assist the termination checker in
assessing the well-definedness of corecursive definitions.
In Agda there is a type \AD{Size} of sizes and a type \AD{Size<}
\AB{i} of sizes strictly smaller than \AB{i}.  Every size \AB{j} :
\AD{Size<} \AB{i} is coerced to \AB{j} : \AD{Size}. The order relation
on sizes is transitive: if \AB{j} : \AD{Size<} \AB{i} and \AB{k} :
\AD{Size<} \AB{j} then \AB{k} : \AD{Size<} \AB{i}.
The order relation is also well-founded, which allows the definition of productive corecursive functions \cite{A-sized}. We will see this principle at work on the construction of the semantic fixpoint operation in Section \ref{sec:later}.
There is a successor operation \F{↑} on sizes and a greatest size
\F{∞}, \ie \AB{i} : \AD{Size<} \F{∞} for each size \AB{i}. Practically
sized types are used in combination with coinductive records for the
specification of coinductive types \NV{Cite Andreas}. Data of a
coinductive type at size \F{∞} can be subjected to an infinite number
of observations.

%Lastly, we use the size \F{∞}, and for each size \AB{i} we have .
%% Let us be more concrete.
%% In Agda, there is a type \AD{Size}.
%% This type is ordered meaning that for every size \AB{i} we have a type \AD{Size<} \AB{i} of sizes smaller than \AB{i}.
%% There is a coercion from \AD{Size<} \AB{i} to \AD{Size}.
%% The most important of this order, is that it is well-founded.
%% This is used by the productivity checker of Agda, which uses that functions are productive if in every recursive call some size decreases \cite{A-sized}.
%% Lastly, we use the size \F{∞}, and for each size \AB{i} we have \AB{i} : \AD{Size<} \F{∞}.

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
