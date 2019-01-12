\AgdaHide{
\begin{code}
module CloTT.TypeFormers.LaterType where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers.Later
open import CloTT.TypeFormers.FunctionType

open PSh
open ►Obj
open ExpObj
\end{code}
}

\begin{code}
pure : (Γ : Ctx tot) (A : Ty tot) (t : Tm Γ A) → Tm Γ (► A)
►cone (proj₁ (pure Γ A t) i x) [ j ] = proj₁ t j (Mor Γ i j x)
\end{code}

\AgdaHide{
\begin{code}
►com (proj₁ (pure Γ A t) i x) [ j ] [ k ] = 
  begin
    Mor A j k (proj₁ t j (Mor Γ i j x))
  ≡⟨ proj₂ t j k (Mor Γ i j x)  ⟩
    proj₁ t k (Mor Γ j k (Mor Γ i j x))
  ≡⟨ cong (proj₁ t k) (sym (MorComp Γ)) ⟩
    proj₁ t k (Mor Γ i k x)
  ∎
proj₂ (pure Γ A t) i j x = ►eq (λ { j → cong (proj₁ t j) (MorComp Γ) })
\end{code}
}

\AgdaHide{
\begin{code}
fmap : (Γ : Ctx tot) (A B : Ty tot) 
          → (f : Tm Γ (► (A ⇒ B))) (t : Tm Γ (► A))
          → Tm Γ (► B)
►cone (proj₁ (fmap Γ A B (f , p) (t , _)) i x) [ j ] = fun (►cone (f i x) [ j ]) j (►cone (t i x) [ j ])
►com (proj₁ (fmap Γ A B (f , p) (t , q)) i x) [ j ] [ k ] =
  begin
    Mor B j k (fun (►cone (f i x) [ j ]) j (►cone (t i x) [ j ]))
  ≡⟨ funcom (►cone (f i x) [ j ]) j k (►cone (t i x) [ j ]) ⟩ 
    fun (►cone (f i x) [ j ]) k (Mor A j k (►cone (t i x) [ j ]))
  ≡⟨ cong (fun (►cone (f i x) [ j ]) k) (►com (t i x) [ j ] [ k ]) ⟩
    fun (►cone (f i x) [ j ]) k (►cone (t i x) [ k ]) 
  ≡⟨ cong (λ z → fun z k (►cone (t i x) [ k ])) (sym (►com (f i x) [ j ] [ j ])) ⟩ 
    fun (Mor (A ⇒ B) j j (►cone (f i x) [ j ])) k (►cone (t i x) [ k ])
  ≡⟨ cong (λ z → fun z k (►cone (t i x) [ k ])) (►com (f i x) [ j ] [ k ]) ⟩
    fun (►cone (f i x) [ k ]) k (►cone (t i x) [ k ])
  ∎
proj₂ (fmap Γ A B f t) i j x =
  ►eq (λ {k → cong₂ (λ a b → fun (►cone a [ k ]) k (►cone b [ k ]))
                    (proj₂ f i j x)
                    (proj₂ t i j x)})
\end{code}
}
