\AgdaHide{
\begin{code}
module CloTT.TypeFormers.Force where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers.Later
open import CloTT.TypeFormers.ClockQuantification

open PSh
open ■
open ►Obj
\end{code}
}

Finally we give a semantic definition of the force operation. 

\begin{code}
sem-force : (Γ : Ctx set) (A : Ty tot) (t : Tm Γ (■ (► A))) → Tm Γ (■ A)
■cone (sem-force Γ A t x) j = ►cone (■cone (t x) ∞) [ j ]
■com (sem-force Γ A t x) i j = ►com (■cone (t x) ∞) [ i ] [ j ]
\end{code}
