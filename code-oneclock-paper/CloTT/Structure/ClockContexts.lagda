\AgdaHide{
\begin{code}
module CloTT.Structure.ClockContexts where
\end{code}
}

Our goal is to make an interpretation of the syntax as defined in \Cref{sec:syntax}.
For this, we first need to interpret clock contexts and for those there are two possibilities.
It is either empty or we have a single clock.
In the first case, we use the tag \AIC{set} to indicate we interpret types and contexts as sets.
In the second case, we use \AIC{tot}, which says we work in some topos of trees.

\begin{code}
data tag : Set where
  set : tag
  tot : tag
\end{code}
