\AgdaHide{
\begin{code}
module CloTT.DefinitionalEqualities where

open import Data.Product
open import Data.Sum
open import Data.Unit
open import Prelude
open import Prelude.Syntax
open import Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers
open import CloTT.InterpretSyntax

open PSh
open ■
open ►Obj
open ExpObj
open NatTrans
\end{code}
}

\begin{code}

sem-λ-β : {Δ : ClockContext} {Γ : Context Δ} {A B : Type Δ} (t : Term (Γ , A) B) → def-eq _ _ ⟦ appTm (lambdaTm t) ⟧tm ⟦ t ⟧tm
sem-λ-β {∅} {Γ} {A} {B} t x = refl
sem-λ-β {κ} {Γ} {A} {B} t i x =
  begin
    nat-map ⟦ t ⟧tm i (Mor ⟦ Γ ⟧Γ i i (proj₁ x) , proj₂ x)
  ≡⟨ cong (λ z → nat-map ⟦ t ⟧tm i (z , _)) (MorId ⟦ Γ ⟧Γ) ⟩
    nat-map ⟦ t ⟧tm i x
  ∎

sem-λ-η : {Δ : ClockContext} {Γ : Context Δ} {A B : Type Δ} (t : Term Γ (A ⟶ B)) → def-eq _ _ ⟦ lambdaTm (appTm t) ⟧tm ⟦ t ⟧tm
sem-λ-η {∅} {Γ} {A} {B} f x = refl
sem-λ-η {κ} {Γ} {A} {B} f i x = funeq (λ j y → cong (λ z → fun z j y) (sym (nat-com ⟦ f ⟧tm i j x)))

sem-⊠-β₁ : {Δ : ClockContext} {Γ : Context Δ} {A B : Type Δ} (t₁ : Term Γ A) (t₂ : Term Γ B) → def-eq _ _ ⟦ π₁ [ t₁ & t₂ ] ⟧tm ⟦ t₁ ⟧tm
sem-⊠-β₁ {∅} {Γ} {A} {B} t₁ t₂ x = refl
sem-⊠-β₁ {κ} {Γ} {A} {B} t₁ t₂ i x = refl

sem-⊠-β₂ : {Δ : ClockContext} {Γ : Context Δ} {A B : Type Δ} (t₁ : Term Γ A) (t₂ : Term Γ B) → def-eq _ _ ⟦ π₂ [ t₁ & t₂ ] ⟧tm ⟦ t₂ ⟧tm
sem-⊠-β₂ {∅} {Γ} {A} {B} t₁ t₂ x = refl
sem-⊠-β₂ {κ} {Γ} {A} {B} t₁ t₂ i x = refl

sem-⊠-η : {Δ : ClockContext} {Γ : Context Δ} {A B : Type Δ} (t : Term Γ (A ⊠ B)) → def-eq _ _ ⟦ [ π₁ t & π₂ t ] ⟧tm ⟦ t ⟧tm
sem-⊠-η {∅} {Γ} {A} {B} t x = refl
sem-⊠-η {κ} {Γ} {A} {B} t i x = refl

sem-⊞-β₁ : {Δ : ClockContext} {Γ : Context Δ} {A B C : Type Δ} (l : Term (Γ , A) C) (r : Term (Γ , B) C) (t : Term Γ A)
  → def-eq _ _ ⟦ sub (⊞rec C l r) (idsub Γ ,s in₁ B t) ⟧tm ⟦ sub l (idsub Γ ,s t) ⟧tm
sem-⊞-β₁ {∅} {Γ} {A} {B} {C} l r t x = refl
sem-⊞-β₁ {κ} {Γ} {A} {B} {C} l r t i x = refl

sem-⊞-β₂ : {Δ : ClockContext} {Γ : Context Δ} {A B C : Type Δ} (l : Term (Γ , A) C) (r : Term (Γ , B) C) (t : Term Γ B)
  → def-eq _ _ ⟦ sub (⊞rec C l r) (idsub Γ ,s in₂ A t) ⟧tm ⟦ sub r (idsub Γ ,s t) ⟧tm
sem-⊞-β₂ {∅} {Γ} {A} {B} {C} l r t x = refl
sem-⊞-β₂ {κ} {Γ} {A} {B} {C} l r t i x = refl

sem-𝟙-β : {Γ : Context ∅} {A : Type ∅} (t : Term Γ A) → def-eq _ _ ⟦ sub (unit-rec t) (idsub Γ ,s tt) ⟧tm ⟦ t ⟧tm
sem-𝟙-β {Γ} {A} t x = refl

sem-𝟙-η : {Γ : Context ∅} (t : Term Γ 𝟙) → def-eq ⟦ Γ ⟧Γ ⟦ 𝟙 ⟧A ⟦ t ⟧tm ⟦ tt {Γ} ⟧tm
sem-𝟙-η t x = refl

sem-□-β : {Γ : Context ∅} {A : Type κ} (t : Term (weakenC Γ) A) → def-eq ⟦ weakenC Γ ⟧Γ ⟦ A ⟧A ⟦ unbox-q (box-q t) ⟧tm ⟦ t ⟧tm
sem-□-β {Γ} {A} t i x = refl

sem-□-η : {Γ : Context ∅} {A : Type κ} (t : Term Γ (□ A)) → def-eq ⟦ Γ ⟧Γ ⟦ □ A ⟧A ⟦ box-q (unbox-q t) ⟧tm ⟦ t ⟧tm
sem-□-η t x = refl

sem-⇡-β : {Γ : Context ∅} {A : Type ∅} (t : Term Γ A) → def-eq ⟦ Γ ⟧Γ ⟦ A ⟧A ⟦ ↓ (⇡ t) ⟧tm ⟦ t ⟧tm
sem-⇡-β t x = refl

sem-⇡-η : {Γ : Context ∅} {A : Type ∅} (t : Term (weakenC Γ) (weakenT A)) → def-eq ⟦ weakenC Γ ⟧Γ ⟦ weakenT A ⟧A ⟦ ⇡ (↓ t) ⟧tm ⟦ t ⟧tm
sem-⇡-η t = nat-com ⟦ t ⟧tm ∞

sem-next-id : {Γ : Context κ} {A : Type κ} (t : Term Γ (▻ A)) → def-eq ⟦ Γ ⟧Γ ⟦ ▻ A ⟧A ⟦ next (idmap A) ⊛ t ⟧tm ⟦ t ⟧tm
sem-next-id t i x = ►eq (λ {_ → refl})

sem-next-⊛ : {Γ : Context κ} {A B : Type κ} (f : Term Γ (A ⟶ B)) (t : Term Γ A) → def-eq ⟦ Γ ⟧Γ ⟦ ▻ B ⟧A ⟦ next f ⊛ next t ⟧tm ⟦ next (app-map f t) ⟧tm
sem-next-⊛ f t i x = ►eq (λ {_ → refl})

sem-next-comp : {Γ : Context κ} {A B C : Type κ} (g : Term Γ (▻ (B ⟶ C))) (f : Term Γ (▻ (A ⟶ B))) (t : Term Γ (▻ A))
  → def-eq ⟦ Γ ⟧Γ ⟦ ▻ C ⟧A ⟦ ((next compmap ⊛ g) ⊛ f) ⊛ t  ⟧tm ⟦ g ⊛ (f ⊛ t) ⟧tm
sem-next-comp g f t i x = ►eq (λ {_ → refl})

sem-next-λ : {Γ : Context κ} {A B : Type κ} (f : Term Γ (▻ (A ⟶ B))) (t : Term Γ A)
  → def-eq ⟦ Γ ⟧Γ ⟦ ▻ B ⟧A ⟦ f ⊛ next t ⟧tm ⟦ next (lambdaTm (app-map (varTm _ _) (weakenTm _ _ _ t))) ⊛ f ⟧tm
sem-next-λ {Γ} f t i x = ►eq (λ { j → cong (λ z → fun (►cone (nat-map ⟦ f ⟧tm i x) [ j ]) j (nat-map ⟦ t ⟧tm j z)) (sym (MorId ⟦ Γ ⟧Γ))})

dfix-eq : (Γ : Ctx κ) (A : Ty κ) (f : Tm Γ (► A ⇒ A))
  → def-eq {κ} Γ (► A) (dfix Γ A f) (sem-next Γ A (sem-fix Γ A f))
dfix-eq Γ A f i γ = ►eq (λ {j → cong (λ a → fun a j (dfix₁ A j a)) (nat-com f i j γ)})

fix-eq : (Γ : Ctx κ) (A : Ty κ) (f : Tm Γ (► A ⇒ A))
  → def-eq Γ A
           (sem-fix Γ A f)
           (sem-app-map Γ (► A) A f (sem-next Γ A (sem-fix Γ A f)))
fix-eq Γ A f i x = cong (fun (nat-map f i x) i) (dfix-eq Γ A f i x)

sem-fix-f : {Γ : Context κ} {A : Type κ} (f : Term Γ (▻ A ⟶ A))
  → def-eq ⟦ Γ ⟧Γ ⟦ A ⟧A
           ⟦ fix-tm f ⟧tm
           ⟦ app-map f (next (fix-tm f)) ⟧tm
sem-fix-f f = fix-eq _ _ ⟦ f ⟧tm

dfix-un : (Γ : Ctx κ) (A : Ty κ) (f : Tm Γ (► A ⇒ A)) (u : Tm Γ A) (i : Size) (x : Obj Γ i)
  → def-eq Γ A (sem-app-map Γ (► A) A f (sem-next Γ A u)) u
  → dfix₁ A i (nat-map f i x) ≡ nat-map (sem-next Γ A u) i x
dfix-un Γ A z₁ z₂ i x r =
  let f = nat-map z₁ in
  let p = nat-com z₁ in
  let u = nat-map z₂ in
  let q = nat-com z₂ in
  ►eq'
  (funext (λ {[ j ] →
    begin
      fun (f i x) j (dfix₁ A j (f i x))
    ≡⟨ cong (λ z → fun z j (dfix₁ A j z)) (p i j x) ⟩
      fun (f j (Mor Γ i j x)) j (dfix₁ A j (f j (Mor Γ i j x)))
    ≡⟨ cong (fun (f j (Mor Γ i j x)) j) (dfix-un Γ A z₁ z₂ j (Mor Γ i j x) r) ⟩
      fun (f j (Mor Γ i j x)) j (nat-map (sem-next Γ A z₂) j (Mor Γ i j x))
    ≡⟨ r j (Mor Γ i j x) ⟩
      u j (Mor Γ i j x)
    ∎
    }))

fix-un : (Γ : Ctx κ) (A : Ty κ) (f : Tm Γ (► A ⇒ A)) (u : Tm Γ A)
  → def-eq Γ A (sem-app-map Γ (► A) A f (sem-next Γ A u)) u
  → def-eq Γ A (sem-fix Γ A f) u
fix-un Γ A f u p i x =
  begin
    nat-map (sem-fix Γ A f) i x
  ≡⟨ cong (λ z → fun (nat-map f i x) i z) (dfix-un Γ A f u i x p) ⟩
    nat-map (sem-app-map Γ (► A) A f (sem-next Γ A u)) i x
  ≡⟨ p i x ⟩
    nat-map u i x
  ∎

sem-fix-u : {Γ : Context κ} {A : Type κ} (f : Term Γ (▻ A ⟶ A)) (u : Term Γ A)
  → def-eq ⟦ Γ ⟧Γ ⟦ A ⟧A
           ⟦ app-map f (next u) ⟧tm
           ⟦ u ⟧tm
  → def-eq ⟦ Γ ⟧Γ ⟦ A ⟧A
           ⟦ fix-tm f ⟧tm
           ⟦ u ⟧tm
sem-fix-u f u p = fix-un _ _ ⟦ f ⟧tm ⟦ u ⟧tm p

sem-sub-idl : {Δ : ClockContext} {Γ Γ' : Context Δ} (s : Subst Γ Γ') → subst-eq _ _ ⟦ idsub Γ' o s ⟧sub ⟦ s ⟧sub
sem-sub-idl {∅} s x = refl
sem-sub-idl {κ} s i x = refl

sem-sub-idr : {Δ : ClockContext} {Γ Γ' : Context Δ} (s : Subst Γ Γ') → subst-eq _ _ ⟦ s o idsub Γ ⟧sub ⟦ s ⟧sub
sem-sub-idr {∅} s x = refl
sem-sub-idr {κ} s i x = refl

sem-sub-assoc : {Δ : ClockContext} {Γ₁ Γ₂ Γ₃ Γ₄ : Context Δ} (s₁ : Subst Γ₁ Γ₂) (s₂ : Subst Γ₂ Γ₃) (s₃ : Subst Γ₃ Γ₄)
  → subst-eq _ _ ⟦ s₃ o (s₂ o s₁) ⟧sub ⟦ (s₃ o s₂) o s₁ ⟧sub
sem-sub-assoc {∅} s₁ s₂ s₃ x = refl
sem-sub-assoc {κ} s₁ s₂ s₃ i x = refl

sem-sub-π₁β : {Δ : ClockContext} {Γ Γ' : Context Δ} {A : Type Δ} {t : Term Γ A} (s : Subst Γ Γ')
  → subst-eq _ _ ⟦ pr (s ,s t) ⟧sub ⟦ s ⟧sub
sem-sub-π₁β {∅} s x = refl
sem-sub-π₁β {κ} s i x = refl

sem-sub-εη : {Δ : ClockContext} {Γ : Context Δ} (s : Subst Γ •) → subst-eq _ _ ⟦ s ⟧sub ⟦ ε Γ ⟧sub
sem-sub-εη {∅} s x = refl
sem-sub-εη {κ} s i x = refl

sem-sub-,o : {Δ : ClockContext} {Γ₁ Γ₂ Γ₃ : Context Δ} {A : Type Δ} {t : Term Γ₂ A} (s₁ : Subst Γ₁ Γ₂) (s₂ : Subst Γ₂ Γ₃)
  → subst-eq _ _ ⟦ (s₂ ,s t) o s₁ ⟧sub ⟦ (s₂ o s₁) ,s sub t s₁ ⟧sub
sem-sub-,o {∅} s₁ s₂ x = refl
sem-sub-,o {κ} s₁ s₂ i x = refl

sem-sub-η : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} (s : Subst Γ (Γ , A))
  → subst-eq _ _ ⟦ pr s ,s sub (varTm Γ A) s ⟧sub ⟦ s ⟧sub
sem-sub-η {∅} s x = refl
sem-sub-η {κ} s i x = refl

sem-primrec-set : (P Q : Poly ∅) (Γ : Context ∅) (A : Type ∅)
  → (t : Term Γ ((evalP P (μ P) ⊠ evalP P A) ⟶ A))
  → (x : ⟦ Γ ⟧Γ) (a : ⟦ evalP Q (μ P) ⟧A)
  → primrec-set' P Q A (⟦ t ⟧tm x) (consset' P Q a) ≡ (a , ⟦ Pmap Q (primrec P t) ⟧tm x a) -- (a , ⟦ Pmap Q (primrec P t) ⟧tm x a)
sem-primrec-set P (∁ X) Γ A t x a = refl
sem-primrec-set P I Γ A t x a = refl
sem-primrec-set P (Q ⊞ R) Γ A t x (inj₁ a) =
  cong₂ _,_ (cong (inj₁ ∘ proj₁) (sem-primrec-set P Q Γ A t x a))
            (cong (inj₁ ∘ proj₂) (sem-primrec-set P Q Γ A t x a))
sem-primrec-set P (Q ⊞ R) Γ A t x (inj₂ a) =
  cong₂ _,_ (cong (inj₂ ∘ proj₁) (sem-primrec-set P R Γ A t x a))
            (cong (inj₂ ∘ proj₂) (sem-primrec-set P R Γ A t x a))
sem-primrec-set P (Q ⊠ R) Γ A t x (a₁ , a₂) =
  cong₂ _,_ (cong₂ _,_ (cong proj₁ (sem-primrec-set P Q Γ A t x a₁))
                       (cong proj₁ (sem-primrec-set P R Γ A t x a₂)))
            (cong₂ _,_ (cong proj₂ (sem-primrec-set P Q Γ A t x a₁))
                       (cong proj₂ (sem-primrec-set P R Γ A t x a₂)))

sem-primrec-psh : (P Q : Poly κ) (Γ : Context κ) (A : Type κ)
  → (t : Term Γ ((evalP P (μ P) ⊠ evalP P A) ⟶ A))
  → (i : Size) (x : Obj ⟦ Γ ⟧Γ i) (j : Size< (↑ i)) (a : Obj ⟦ evalP Q (μ P) ⟧A j)
  → primrec-psh'₁₁ P Q A i (nat-map ⟦ t ⟧tm i x) j (cons₁' P Q j a) ≡ (a , fun(nat-map ⟦ Pmap Q (primrec P t) ⟧tm i x) j a)
sem-primrec-psh P (∁ X) Γ A t i x j a = refl
sem-primrec-psh P I Γ A t i x j a = refl
sem-primrec-psh P (Q ⊞ R) Γ A t i x j (inj₁ a) =
  cong₂ _,_ (cong (inj₁ ∘ proj₁) (sem-primrec-psh P Q Γ A t i x j a))
            (trans (cong (inj₁ ∘ proj₂) (sem-primrec-psh P Q Γ A t i x j a))
                   (cong (λ z → inj₁ (fun z j a)) (nat-com ⟦ Pmap Q (primrec P t) ⟧tm i j x)))
sem-primrec-psh P (Q ⊞ R) Γ A t i x j (inj₂ a) =
  cong₂ _,_ (cong (inj₂ ∘ proj₁) (sem-primrec-psh P R Γ A t i x j a))
            (trans (cong (inj₂ ∘ proj₂) (sem-primrec-psh P R Γ A t i x j a))
                   (cong (λ z → inj₂ (fun z j a)) (nat-com ⟦ Pmap R (primrec P t) ⟧tm i j x)))
sem-primrec-psh P (Q ⊠ R) Γ A t i x j (a₁ , a₂) =
  cong₂ _,_ (cong₂ _,_ (cong proj₁ (sem-primrec-psh P Q Γ A t i x j a₁))
                       (cong proj₁ (sem-primrec-psh P R Γ A t i x j a₂)))
            (cong₂ _,_ (trans (cong proj₂ (sem-primrec-psh P Q Γ A t i x j a₁))
                              (cong (λ z → fun z j a₁) (nat-com ⟦ Pmap Q (primrec P t) ⟧tm i j x)))
                       (trans (cong proj₂ (sem-primrec-psh P R Γ A t i x j a₂))
                              (cong (λ z → fun z j a₂) (nat-com ⟦ Pmap R (primrec P t) ⟧tm i j x))))
sem-primrec-psh P (▻P Q) Γ A t i x j z =
  cong₂ _,_
        (►eq (λ {k → cong proj₁ (sem-primrec-psh P Q Γ A t i x k (►cone z [ k ]))}))
        (►eq (λ {k → trans (cong proj₂ (sem-primrec-psh P Q Γ A t i x k (►cone z [ k ])))
                           (cong (λ y → fun y k (►cone z [ k ]))
                                 (trans (nat-com ⟦ Pmap Q (primrec P t) ⟧tm i k x)
                                        (cong (nat-map ⟦ Pmap Q (primrec P t) ⟧tm k) (MorComp ⟦ Γ ⟧Γ))))}))

μweakenμ-help : (P Q : Poly ∅) (i : Size) (x : μObj' ⟦ weakenP P ⟧poly ⟦ weakenP Q ⟧poly i)
  → μweaken-help P Q (weakenμ-help P Q i x) i ≡ x
μweakenμ-help P (∁ X) i (∁ps x) = refl
μweakenμ-help P I i (I x) = cong I (μweakenμ-help P P i x)
μweakenμ-help P (Q₁ ⊞ Q₂) i (⊞₁ x) = cong ⊞₁ (μweakenμ-help P Q₁ i x)
μweakenμ-help P (Q₁ ⊞ Q₂) i (⊞₂ x) = cong ⊞₂ (μweakenμ-help P Q₂ i x)
μweakenμ-help P (Q₁ ⊠ Q₂) i (x₁ ⊠ x₂) = cong₂ _⊠_ (μweakenμ-help P Q₁ i x₁) (μweakenμ-help P Q₂ i x₂)

weakenμweaken-help : (P Q : Poly ∅) (i : Size) (x : μset ⟦ P ⟧poly ⟦ Q ⟧poly)
  → weakenμ-help P Q i (μweaken-help P Q x i) ≡ x
weakenμweaken-help P (∁ X) i (∁s x) = refl
weakenμweaken-help P I i (I x) = cong I (weakenμweaken-help P P i x)
weakenμweaken-help P (Q₁ ⊞ Q₂) i (⊞₁ x) = cong ⊞₁ (weakenμweaken-help P Q₁ i x)
weakenμweaken-help P (Q₁ ⊞ Q₂) i (⊞₂ x) = cong ⊞₂ (weakenμweaken-help P Q₂ i x)
weakenμweaken-help P (Q₁ ⊠ Q₂) i (x₁ ⊠ x₂) = cong₂ _⊠_ (weakenμweaken-help P Q₁ i x₁) (weakenμweaken-help P Q₂ i x₂)

mutual
  ⟦_⟧tm-eq : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} {t₁ t₂ : Term Γ A} → t₁ ∼ t₂ → def-eq ⟦ Γ ⟧Γ ⟦ A ⟧A ⟦ t₁ ⟧tm ⟦ t₂ ⟧tm
  ⟦_⟧tm-eq {∅} refl∼ x = refl
  ⟦_⟧tm-eq {κ} refl∼ i x = refl
  ⟦_⟧tm-eq {∅} (sym∼ p) x = sym (⟦_⟧tm-eq p x)
  ⟦_⟧tm-eq {κ} (sym∼ p) i x = sym (⟦_⟧tm-eq p i x)
  ⟦_⟧tm-eq {∅} (trans∼ p q) x = trans (⟦_⟧tm-eq p x) (⟦_⟧tm-eq q x)
  ⟦_⟧tm-eq {κ} (trans∼ p q) i x = trans (⟦_⟧tm-eq p i x) (⟦_⟧tm-eq q i x)
  ⟦_⟧tm-eq {∅} (cong-sub {t₂ = t₂} {s₁} p q) x = trans (⟦_⟧tm-eq p (⟦ s₁ ⟧sub x)) (cong ⟦ t₂ ⟧tm (⟦ q ⟧sub-eq x))
  ⟦_⟧tm-eq {κ} (cong-sub {t₂ = t₂} {s₁} p q) i x = trans (⟦_⟧tm-eq p i (nat-map ⟦ s₁ ⟧sub i x)) (cong (nat-map ⟦ t₂ ⟧tm i) (⟦ q ⟧sub-eq i x))
  ⟦ cong-unit-rec p ⟧tm-eq (x , tt) = ⟦ p ⟧tm-eq x
  ⟦_⟧tm-eq {∅} (cong-in₁ B p) x = cong inj₁ (⟦ p ⟧tm-eq x)
  ⟦_⟧tm-eq {κ} (cong-in₁ B p) i x = cong inj₁ (⟦ p ⟧tm-eq i x)
  ⟦_⟧tm-eq {∅} (cong-in₂ A p) x = cong inj₂ (⟦ p ⟧tm-eq x)
  ⟦_⟧tm-eq {κ} (cong-in₂ A p) i x = cong inj₂ (⟦ p ⟧tm-eq i x)
  ⟦_⟧tm-eq {∅} (cong-⊞rec C p q) (x , inj₁ a) = ⟦ p ⟧tm-eq (x , a) 
  ⟦_⟧tm-eq {∅} (cong-⊞rec C p q) (x , inj₂ b) = ⟦ q ⟧tm-eq (x , b) 
  ⟦_⟧tm-eq {κ} (cong-⊞rec C p q) i (x , inj₁ a) = ⟦ p ⟧tm-eq i (x , a)
  ⟦_⟧tm-eq {κ} (cong-⊞rec C p q) i (x , inj₂ b) = ⟦ q ⟧tm-eq i (x , b)
  ⟦_⟧tm-eq {∅} cong-[ p & q ] x = cong₂ _,_ (⟦ p ⟧tm-eq x) (⟦ q ⟧tm-eq x)
  ⟦_⟧tm-eq {κ} cong-[ p & q ] i x = cong₂ _,_ (⟦ p ⟧tm-eq i x) (⟦ q ⟧tm-eq i x)
  ⟦_⟧tm-eq {∅} (cong-π₁ p) x = cong proj₁ (⟦ p ⟧tm-eq x)
  ⟦_⟧tm-eq {κ} (cong-π₁ p) i x = cong proj₁ (⟦ p ⟧tm-eq i x)
  ⟦_⟧tm-eq {∅} (cong-π₂ p) x = cong proj₂ (⟦ p ⟧tm-eq x)
  ⟦_⟧tm-eq {κ} (cong-π₂ p)  i x = cong proj₂ (⟦ p ⟧tm-eq i x)
  ⟦_⟧tm-eq {∅} (cong-lambdaTm p) x = funext (λ a → ⟦ p ⟧tm-eq (x , a))
  ⟦_⟧tm-eq {κ} (cong-lambdaTm {Γ = Γ} p) i x = funeq (λ j a → ⟦ p ⟧tm-eq j (Mor ⟦ Γ ⟧Γ i j x , a))
  ⟦_⟧tm-eq {∅} (cong-appTm p) (x , a) = cong (λ z → z a) (⟦ p ⟧tm-eq x)
  ⟦_⟧tm-eq {κ} (cong-appTm p) i (x , a) = cong (λ z → fun z i a) (⟦ p ⟧tm-eq i x)
  ⟦ cong-⇡ p ⟧tm-eq i x = ⟦ p ⟧tm-eq x
  ⟦ cong-↓ p ⟧tm-eq x = ⟦ p ⟧tm-eq ∞ x
  ⟦ cong-box-q p ⟧tm-eq x = ■eq (λ i → ⟦ p ⟧tm-eq i x)
  ⟦ cong-unbox-q p ⟧tm-eq i x = cong (λ z → ■cone z i) (⟦ p ⟧tm-eq x)
  ⟦_⟧tm-eq (cong-next {Γ = Γ} p) i x = ►eq (λ{ j → ⟦ p ⟧tm-eq j (Mor ⟦ Γ ⟧Γ i j x) })
  ⟦_⟧tm-eq (cong- p ⊛ q) i x = ►eq (λ{ j → cong₂ (λ a b → fun (►cone a [ j ]) j (►cone b [ j ])) (⟦ p ⟧tm-eq i x) (⟦ q ⟧tm-eq i x)})
  ⟦_⟧tm-eq (cong-fix-tm {A = A} p) i x = cong (λ z → fun z i (dfix₁ ⟦ A ⟧A i z)) (⟦ p ⟧tm-eq i x)
  ⟦ cong-force {Γ} {A} {t₁} {t₂} p ⟧tm-eq x = ■eq (λ i → cong (λ z → ►cone (■cone z ∞) [ i ]) (⟦ p ⟧tm-eq x))
  ⟦_⟧tm-eq {∅} (cong-cons p) x = cong (consset' _ _) (⟦ p ⟧tm-eq x)
  ⟦_⟧tm-eq {κ} (cong-cons p) i x = cong (cons₁' _ _ i) (⟦ p ⟧tm-eq i x)
  ⟦_⟧tm-eq {∅} (cong-primrec P {Γ} {A} p) x = funext (λ a → cong (λ z → z (primrec-set' P P A z a)) (⟦ p ⟧tm-eq x))
  ⟦_⟧tm-eq {κ} (cong-primrec P {Γ} {A} p) i x = funeq (λ j y → cong (λ z → fun z j (primrec-psh'₁₁ P P A i z j y)) (⟦ p ⟧tm-eq i x))
  ⟦ λ-β t ⟧tm-eq = sem-λ-β t
  ⟦ λ-η t ⟧tm-eq = sem-λ-η t
  ⟦ ⊠-β₁ t₁ t₂ ⟧tm-eq = sem-⊠-β₁ t₁ t₂
  ⟦ ⊠-β₂ t₁ t₂ ⟧tm-eq = sem-⊠-β₂ t₁ t₂
  ⟦ ⊠-η t ⟧tm-eq = sem-⊠-η t
  ⟦ ⊞-β₁ l r t ⟧tm-eq = sem-⊞-β₁ l r t
  ⟦ ⊞-β₂ l r t ⟧tm-eq = sem-⊞-β₂ l r t
  ⟦ 𝟙-β t ⟧tm-eq = sem-𝟙-β t
  ⟦ 𝟙-η t ⟧tm-eq = sem-𝟙-η t
  ⟦ □-β t ⟧tm-eq = sem-□-β t
  ⟦ □-η t ⟧tm-eq = sem-□-η t
  ⟦ ⇡-β t ⟧tm-eq = sem-⇡-β t
  ⟦ ⇡-η t ⟧tm-eq = sem-⇡-η t
  ⟦ next-id t ⟧tm-eq = sem-next-id t
  ⟦ next-comp g f t ⟧tm-eq = sem-next-comp g f t
  ⟦ next-⊛ f t ⟧tm-eq = sem-next-⊛ f t
  ⟦ next-λ f t ⟧tm-eq = sem-next-λ f t
  ⟦ fix-f f ⟧tm-eq = sem-fix-f f
  ⟦ fix-u f u p ⟧tm-eq = sem-fix-u f u ⟦ p ⟧tm-eq
  ⟦_⟧tm-eq {∅} (primrec-cons P t a) x = cong (⟦ t ⟧tm x) (sem-primrec-set P P _ _ t x (⟦ a ⟧tm x))
  ⟦_⟧tm-eq {κ} (primrec-cons P t a) i x = cong (fun (nat-map ⟦ t ⟧tm i x) i) (sem-primrec-psh P P _ _ t i x i (nat-map ⟦ a ⟧tm i x))
  ⟦_⟧tm-eq {∅} (sub-id t) x = refl
  ⟦_⟧tm-eq {κ} (sub-id t) i x = refl
  ⟦_⟧tm-eq {∅} (sub-sub t s s') x = refl
  ⟦_⟧tm-eq {κ} (sub-sub t s s') i x = refl
  ⟦_⟧tm-eq {∅} (sub-varTm Γ₁ Γ₂ A s) x = refl
  ⟦_⟧tm-eq {κ} (sub-varTm Γ₁ Γ₂ A s) i x = refl
  ⟦_⟧tm-eq {.∅} (sub-unit-rec t s) x = refl
  ⟦_⟧tm-eq {∅} (sub-in₁ B t s) x = refl
  ⟦_⟧tm-eq {κ} (sub-in₁ B t s) i x = refl
  ⟦_⟧tm-eq {∅} (sub-in₂ A t s) x = refl
  ⟦_⟧tm-eq {κ} (sub-in₂ A t s) i x = refl
  ⟦_⟧tm-eq {∅} (sub-[ t₁ & t₂ ] s) x = refl
  ⟦_⟧tm-eq {κ} (sub-[ t₁ & t₂ ] s) i x = refl
  ⟦_⟧tm-eq {∅} (sub-lambdaTm t s) x = refl
  ⟦_⟧tm-eq {κ} (sub-lambdaTm t s) i x = funeq (λ j z → cong (λ y → nat-map ⟦ t ⟧tm j (y , z)) (nat-com ⟦ s ⟧sub i j x))
  ⟦_⟧tm-eq {.κ} (sub-⇡ t s) i x = refl
  ⟦_⟧tm-eq {.∅} (sub-box-q t s) x = ■eq (λ _ → refl)
  ⟦_⟧tm-eq {.κ} (sub-next t s) i x = ►eq (λ { j → cong (nat-map ⟦ t ⟧tm j) (nat-com ⟦ s ⟧sub i j x)})
  ⟦_⟧tm-eq {.κ} (sub-⊛ f t s) i x = ►eq (λ {_ → refl})
  ⟦_⟧tm-eq {.κ} (sub-fix-tm f s) i x = refl
  ⟦ sub-force t s ⟧tm-eq x = refl
  ⟦ sub-□const A s ⟧tm-eq x = refl
  ⟦ sub-□sum A B s ⟧tm-eq x = refl
  ⟦_⟧tm-eq {∅} (sub-cons t s) x = refl
  ⟦_⟧tm-eq {κ} (sub-cons t s) i x = refl
  ⟦_⟧tm-eq {∅} (sub-primrec P t s) x = refl
  ⟦_⟧tm-eq {κ} (sub-primrec P t s) i x = refl
  ⟦ const□const t ⟧tm-eq x = ■eq (λ i → ■com (⟦ t ⟧tm x) ∞ i)
  ⟦ □const□ t ⟧tm-eq x = refl
  ⟦ □sum□ A B t ⟧tm-eq γ with ⟦ t ⟧tm γ
  ... | inj₁ x = cong inj₁ (■eq (■com x ∞))
  ... | inj₂ y = cong inj₂ (■eq (■com y ∞))
  ⟦ sum□sum {Γ} A B t ⟧tm-eq γ with ■cone (⟦ t ⟧tm γ) ∞ | inspect (■cone (⟦ t ⟧tm γ)) ∞
  ... | inj₁ x | [ eq ] = ■eq (λ i → sym (proj₂ (sum-lem₁ ⟦ Γ ⟧Γ ⟦ A ⟧A ⟦ B ⟧A (⟦ t ⟧tm γ) x eq) i))
  ... | inj₂ y | [ eq ] = ■eq (λ i → sym (proj₂ (sum-lem₂ ⟦ Γ ⟧Γ ⟦ A ⟧A ⟦ B ⟧A (⟦ t ⟧tm γ) y eq) i))
  ⟦ force-□next t ⟧tm-eq x = ■eq (λ _ → refl)
  ⟦ □next-force t ⟧tm-eq x = ■eq (λ i → ►eq (λ {j → cong (λ z → ►cone z [ j ]) (■com (⟦ t ⟧tm x) ∞ i)}))
  ⟦ ⟶weaken⟶ A B t ⟧tm-eq i x = funext (λ y → refl)
  ⟦ weaken⟶weaken A B t ⟧tm-eq i x = funeq (λ j z → funcom (nat-map ⟦ t ⟧tm i x) i j z)
  ⟦ μweakenμ P t ⟧tm-eq i x = μweakenμ-help P P i (nat-map ⟦ t ⟧tm i x)
  ⟦ weakenμweaken P t ⟧tm-eq i x = weakenμweaken-help P P i (nat-map ⟦ t ⟧tm i x)
  ⟦ ⇡↓ t ⟧tm-eq i x = nat-com ⟦ t ⟧tm ∞ i x
  ⟦ ↓⇡ t ⟧tm-eq x = refl
  ⟦ ⇡varTm Γ A ⟧tm-eq i x = refl
  ⟦ ↓varTm Γ A ⟧tm-eq x = refl
  ⟦ ⇡sub t s ⟧tm-eq i x = refl
  ⟦ ↓sub t s ⟧tm-eq x = refl
  ⟦ ⇡π₁ t ⟧tm-eq i x = refl
  ⟦ ⇡π₂ t ⟧tm-eq i x = refl
  ⟦ ↓π₁ t ⟧tm-eq x = refl
  ⟦ ↓π₂ t ⟧tm-eq x = refl
  ⟦ ⇡pair t₁ t₂ ⟧tm-eq i x = refl
  ⟦ ↓pair t₁ t₂ ⟧tm-eq x = refl
  ⟦ ⇡in₁ t ⟧tm-eq i x = refl
  ⟦ ⇡in₂ t ⟧tm-eq i x = refl
  ⟦ ↓in₁ t ⟧tm-eq x = refl
  ⟦ ↓in₂ t ⟧tm-eq x = refl
  ⟦ ⇡⊞rec C l r ⟧tm-eq i (x , inj₁ y) = refl
  ⟦ ⇡⊞rec C l r ⟧tm-eq i (x , inj₂ y) = refl
  ⟦ ↓⊞rec C l r ⟧tm-eq (x , inj₁ y) = refl
  ⟦ ↓⊞rec C l r ⟧tm-eq (x , inj₂ y) = refl
  ⟦ ⇡lambda t ⟧tm-eq i x = refl
  ⟦ ↓lambda t ⟧tm-eq x = refl
  ⟦ ⇡app t ⟧tm-eq i x = refl
  ⟦ ↓app t ⟧tm-eq x = refl
  
  ⟦_⟧sub-eq : {Δ : ClockContext} {Γ Γ' : Context Δ} {s₁ s₂ : Subst Γ Γ'} → s₁ ≈ s₂ → subst-eq _ _ ⟦ s₁ ⟧sub ⟦ s₂ ⟧sub
  ⟦_⟧sub-eq {Δ} refl≈ = refl-subst-eq
  ⟦_⟧sub-eq {Δ} (sym≈ p) = sym-subst-eq ⟦ p ⟧sub-eq
  ⟦_⟧sub-eq {Δ} (trans≈ {Γ} {Γ'} p q) = trans-subst-eq ⟦ p ⟧sub-eq ⟦ q ⟧sub-eq
  ⟦_⟧sub-eq {∅} (cong- p ,s t) x = cong₂ (_,_) (⟦ p ⟧sub-eq x) (⟦ t ⟧tm-eq x)
  ⟦_⟧sub-eq {κ} (cong- p ,s t) i x = cong₂ (_,_) (⟦ p ⟧sub-eq i x) (⟦ t ⟧tm-eq i x)
  ⟦_⟧sub-eq {∅} (cong-_o_ {s₁ = s₁} {s₂ = s₂} {σ₁ = σ₁} {σ₂ = σ₂} p q) x = trans (cong (λ z → ⟦ s₁ ⟧sub z) (⟦ q ⟧sub-eq x)) (⟦ p ⟧sub-eq _)
  ⟦_⟧sub-eq {κ} (cong-_o_ {s₁ = s₁} {s₂ = s₂} {σ₁ = σ₁} {σ₂ = σ₂} p q) i x = trans (cong (λ z → nat-map ⟦ s₁ ⟧sub i z) (⟦ q ⟧sub-eq i x)) (⟦ p ⟧sub-eq i _)
  ⟦_⟧sub-eq {∅} (cong-pr p) x = cong proj₁ (⟦ p ⟧sub-eq x)
  ⟦_⟧sub-eq {κ} (cong-pr p) i x = cong proj₁ (⟦ p ⟧sub-eq i x)
  ⟦_⟧sub-eq {Δ} (sub-idl s) = sem-sub-idl s
  ⟦_⟧sub-eq {Δ} (sub-idr s) = sem-sub-idr s
  ⟦_⟧sub-eq {Δ} (sub-assoc s₁ s₂ s₃) = sem-sub-assoc s₁ s₂ s₃
  ⟦_⟧sub-eq {Δ} (sub-π₁β {Γ} {A} {B} {C} {t}  s) = sem-sub-π₁β {Γ} {A} {B} {C} {t} s
  ⟦_⟧sub-eq {Δ} (sub-εη s) = sem-sub-εη s
  ⟦_⟧sub-eq {Δ} (sub-,o {Γ} {A} {B} {C} {D} {t} s₁ s₂) = sem-sub-,o {Γ} {A} {B} {C} {D} {t} s₁ s₂
  ⟦_⟧sub-eq {Δ} (sub-η s) = sem-sub-η s
  ⟦_⟧sub-eq {Δ} (weaken-o s₁ s₂) i x = refl
  ⟦_⟧sub-eq {Δ} (weaken-idsub Γ) i x = refl
  ⟦ weaken-ε Γ ⟧sub-eq i x = refl
  ⟦ weaken-,s s t ⟧sub-eq i x = refl
  ⟦ weaken-pr s ⟧sub-eq i x = refl
  ⟦ weaken-•-id ⟧sub-eq i x = refl
  ⟦ •-weaken-id ⟧sub-eq i x = refl
  ⟦ weaken-,-id Γ A ⟧sub-eq i x = refl
  ⟦ ,-weaken-id Γ A ⟧sub-eq i x = refl
\end{code}
