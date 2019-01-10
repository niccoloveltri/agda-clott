\AgdaHide{
\begin{code}
module CloTT.Structure.ClockContexts where
\end{code}
}

Our goal is to make an interpretation of the syntax as defined in \Cref{sec:syntax}.
\begin{code}
data tag : Set where
  set : tag
  tot : tag
\end{code}
