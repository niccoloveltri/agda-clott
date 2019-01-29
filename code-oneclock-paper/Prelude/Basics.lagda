\AgdaHide{
\begin{code}
module Prelude.Basics where

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Size
\end{code}
}

We work in Martin-L\"of type theory extended with functional
extensionality, uniqueness of identity proofs (UIP), and sized
types.  Practically, we work in Agda, which supports sized types and
where UIP holds by default. In this section, we give a brief
overview of these principles and we introduce the basic Agda notation
%type-theoretical definitions
that we employ in our formalization.

We write \Ar{=} for judgemental equality and \F{≡} for propositional
equality. Implicit arguments of functions are delimited by curly
brackets. We write \F{Set} and \F{Set₁} for the first and second
universe of types. In addition, Agda supports higher universes and
these are denoted by \F{Set} \AB{ℓ} for universe levels \AB{ℓ}.

The principle of functional extensionality states that every two
functions \Ar{f} and \Ar{g} in the same function space are
 equal whenever \Ar{f x} and \Ar{g x} are equal for all
inputs \Ar{x}. This principle is not provable in Agda, so we need to
postulate it.
\begin{code}
postulate
  funext : {A : Set} {B : A → Set} {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g
\end{code}

UIP states that all proofs of an identity are propositionally
equal. Agda natively supports this principle, which is therefore easily derivable.
%and we can prove it by
%pattern matching on the two equality proofs \Ar{p} and \Ar{q}.
\begin{code}
uip : {A : Set} {x y : A} {p q : x ≡ y} → p ≡ q
\end{code}
\AgdaHide{
\begin{code}
uip {A} {x} {y} {refl} {refl} = refl
\end{code}
}

Agda also natively support sized types
\cite{AVW-normalization}. Intuitively, a sized type is a type
annotated with an abstract ordinal indicating the number of possible
unfoldings that can be performed of elements of the type.  These
abstract ordinals, called sizes, assist the termination checker in
assessing the well-definedness of corecursive definitions.

In Agda, there is a type \AD{Size} of sizes and a type \AD{Size<} \AB{i} of
sizes strictly smaller than \AB{i}.  Every size \AB{j} : \AD{Size<}
\AB{i} is coerced to \AB{j} : \AD{Size}. The order relation on sizes
is transitive, which means that whenever \AB{j} : \AD{Size<} \AB{i} and \AB{k} : \AD{Size<}
\AB{j}, then \AB{k} : \AD{Size<} \AB{i}.  The order relation is also
well-founded, and we use that to define productive corecursive
functions.
\remove{We will see this principle at work on the
construction of the semantic fixpoint operation in Section
\ref{sec:later}.}
There is a successor operation \F{↑} on sizes and a size \F{∞} such that \AB{i} : \AD{Size<} \F{∞} for all
\AB{i}.
\remove{A sized type \Ar{A} is an inhabitant of \AD{Size} \Ar{→}
\AD{Set} and \Ar{A i} consists of elements of \Ar{A} which can be
subjected to \Ar{i}-many observations. In particular, elements of
\Ar{A} \F{∞} can undergo an infinite number of observations.}
Notice that \F{∞} also satisfies \F{∞} : \F{Size< ∞}, but we
do not make use of this property in our development.

Combining sizes with coinductive records allows the definition of coinductive types
\cite{Copatterns}. An example of this encoding can be found
in Abel and Chapman's work \cite{AC14}.


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
