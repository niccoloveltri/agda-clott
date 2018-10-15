module ClockQuantification where

open import Clocks
open import Types
open import Fun
open import Id
open import LaterModality

-- Constant types

Const : ∀{ℓ} → Set ℓ → Clock → Set ℓ
Const A _ = A

∁ : ∀{ℓ} → Set ℓ → Ty ℓ
∁ A = ty (Const A) (λ _ _ → id) (λ _ _ _ _ → refl) (λ _ _ → refl)

-- Clock quantification

record Box {ℓ} (t : Ty ℓ) : Set ℓ where
  constructor box
  open Ty t
  field
    lim : (κ : Clock) → A κ
    rest : (κ : Clock) (α : Tick= κ) → next κ α (lim κ) ≡ lim α

Box-eq : ∀ {ℓ} {t : Ty ℓ} {x x' : Box t}
  → let open Box x
        open Box x' renaming (lim to lim')
  in lim ≡ lim' → x ≡ x'
Box-eq {x = box l p}{box .l q} refl =
  cong (box l) (funext (λ _ → funext (λ { _ → uip })))

□ : ∀{ℓ} → Ty ℓ → Ty ℓ
□ t = ∁ (Box t)

-- Type isomorphisms

-- -- □ ⊳ A ≅ □ A

□⊳ : ∀{ℓ} (t : Ty ℓ)
  → Tm ℓ (□ t ⇒ □ (⊳ t))
□⊳ (ty A next-A next-ass-A next-id-A) =
  tm (λ κ → fun (λ { α (box x rest-x) → box (λ _ → later (ltr x) rest-x)
                                            (λ _ _ → refl) })
                (λ _ _ _ → refl))
     (λ _ _ → refl)

□⊳-inv : ∀{ℓ} (t : Ty ℓ)
  → Tm ℓ (□ (⊳ t) ⇒ □ t)
□⊳-inv (ty A next-A next-ass-A next-id-A) =
  tm (λ _ → fun (λ { α (box x rest-x) → box (force (Later.L (x κ₀)))
                                            (Later.nextᴸ (x κ₀))})
               (λ {_ _ _ → refl}))
     (λ {_ _ → refl})

□⊳-iso₁ : ∀{ℓ} (t : Ty ℓ) (x : Tm ℓ (□ t))
  → Tm ℓ (app (□⊳-inv t) (app (□⊳ t) x) ≡[ □ t ] x)
□⊳-iso₁ t x = toId {x = app (□⊳-inv t) (app (□⊳ t) x)} (λ _ → refl)

□⊳-iso₂ : ∀{ℓ} (t : Ty ℓ) (x : Tm ℓ (□ (⊳ t)))
  → Tm ℓ (app (□⊳ t) (app (□⊳-inv t) x) ≡[ □ (⊳ t) ] x)
□⊳-iso₂ t (tm x nextᵀᵐ-x) = toId {x = app (□⊳ t) (app (□⊳-inv t) (tm x nextᵀᵐ-x))}
  (λ κ → Box-eq (funext (λ κ' → Later-eq (⊳≡ (ltr-eq
    (λ _ → cong (force ∘ Later.L) (Box.rest (x κ) κ₀ κ')))))))


-- -- □ (∁ A) ≅ ∁ A

□∁ : ∀{ℓ} (A : Set ℓ)
  → Tm ℓ (□ (∁ A) ⇒ ∁ A)
□∁ A =
  tm (λ κ → fun (λ { α (box x _) → x κ₀ })
                (λ _ _ _ → refl))
     (λ _ _ → refl)

□∁-inv : ∀{ℓ} (A : Set ℓ)
  → Tm ℓ (∁ A ⇒ □ (∁ A))
□∁-inv A =
  tm (λ κ → fun (λ α x → box (λ _ → x) (λ { _ _ → refl}))
                (λ _ _ _ → refl))
     (λ _ _ → refl)

□∁-iso₁ : ∀{ℓ} (A : Set ℓ) (x : Tm ℓ (∁ A))
  → Tm ℓ (app (□∁ A) (app (□∁-inv A) x) ≡[ ∁ A ] x)
□∁-iso₁ A x = toId {x = app (□∁ A) (app (□∁-inv A) x)}{x} (λ _ → refl)

□∁-iso₂ : ∀{ℓ} (A : Set ℓ) (x : Tm ℓ (□ (∁ A)))
  → Tm ℓ (app (□∁-inv A) (app (□∁ A) x) ≡[ □ (∁ A) ] x)
□∁-iso₂ A (tm x nx) = toId {x = app (□∁-inv A) (app (□∁ A) (tm x nx))}{tm x nx}
  (λ κ → Box-eq (funext (Box.rest (x κ) κ₀)))

-- -- □ (∁ A ⇒ B) ≅ (∁ A ⇒ □ B)

□⇒ : ∀{ℓ} (A : Set ℓ) (c : Ty ℓ)
  → Tm ℓ (□ (∁ A ⇒ c) ⇒ (∁ A ⇒ □ c))
□⇒ A (ty B next-B _ _) =
  tm (λ _ → fun (λ { _ (box g rest-g) → fun (λ _ x → box (λ κ → Fun.f (g κ) κ x)
                                                         (λ κ α → trans (Fun.nextᶠ (g κ) κ α x)
                                                                        (cong (λ z → Fun.f z α x) (rest-g κ α))))
                                            (λ _ _ _ → refl) })
                (λ _ _ _ → refl))
     (λ _ _ → refl)

□⇒-inv : ∀{ℓ} (A : Set ℓ) (c : Ty ℓ)
  → Tm ℓ ((∁ A ⇒ □ c) ⇒ □ (∁ A ⇒ c))
□⇒-inv A (ty B next-B _ _) =
  tm (λ _ → fun (λ { α (fun g _) → box (λ _ → fun (λ β x → Box.lim (g α x) β)
                                                  (λ β γ x → Box.rest (g α x) β γ))
                                       (λ _ _ → refl) })
                (λ { α β (fun g nextᶠ-g) → Box-eq (funext (λ _ → Fun-eq (funext (λ _ → funext
                  (λ x → cong (λ z → Box.lim z _) (nextᶠ-g α β x)))))) }))
     (λ _ _ → refl)

□⇒-iso₁ : ∀{ℓ} (A : Set ℓ) (c : Ty ℓ) (x : Tm ℓ (∁ A ⇒ □ c))
  → Tm ℓ (app (□⇒ A c) (app (□⇒-inv A c) x) ≡[ ∁ A ⇒ □ c ] x)
□⇒-iso₁ A c g = toId {x = app (□⇒ A c) (app (□⇒-inv A c) g)} {g}
  (λ κ → Fun-eq (funext (λ α → funext (λ x → Box-eq (funext
    (λ _ → cong (λ z → Box.lim z _) (Fun.nextᶠ (Tm.τ g κ) κ _ x))))) ))

□⇒-iso₂ : ∀{ℓ} (A : Set ℓ) (c : Ty ℓ)
  → (g : Tm ℓ (□ (∁ A ⇒ c)))
  → Tm ℓ (app (□⇒-inv A c) (app (□⇒ A c) g) ≡[ □ (∁ A ⇒ c) ] g)
□⇒-iso₂ A c g = toId {x = app (□⇒-inv A c) (app (□⇒ A c) g)} {g}
  (λ κ → Box-eq (funext (λ κ' → Fun-eq (funext
    (λ _ → cong (λ z → Fun.f z _) (sym (Box.rest (Tm.τ g κ) κ' _)))))))

{-




{-
□⇒-iso₁ : ∀{ℓ} (A : Set ℓ) (c : ClTy ℓ)
  → (g : ClTm ℓ (∁ A ⇒ □ c))(x : ClTm ℓ (∁ A))
  → ClTm ℓ (app (app (□⇒ A c) (app (□⇒-inv A c) g)) x ≡[ □ c ] app g x)
□⇒-iso₁ A c g x = 
  toId {x = app (app (□⇒ A c) (app (□⇒-inv A c) g)) x}{app g x}
       (λ _ → Box-eq refl)
-}

□⇒-iso₁ : ∀{ℓ} (A : Set ℓ) (c : ClTy ℓ) (x : ClTm ℓ (∁ A ⇒ □ c))
  → ClTm ℓ (app (□⇒ A c) (app (□⇒-inv A c) x) ≡[ ∁ A ⇒ □ c ] x)
□⇒-iso₁ A c g = toId {x = app (□⇒ A c) (app (□⇒-inv A c) g)} {g}
  (λ κ → Pi-eq (funext (λ α → funext (λ x → {!Pi.nextᶠ (ClTm.τ g κ) κ ? x!})) ))
  
□⇒-iso₂ : ∀{ℓ} (A : Set ℓ) (c : ClTy ℓ)
  → (g : ClTm ℓ (□ (∁ A ⇒ c)))
  → ClTm ℓ (app (□⇒-inv A c) (app (□⇒ A c) g) ≡[ □ (∁ A ⇒ c) ] g)
□⇒-iso₂ A c g = toId {x = app (□⇒-inv A c) (app (□⇒ A c) g)} {g}
  (λ κ → Box-eq (funext (λ κ' → Pi-eq (funext (λ α → {!Box.rest (ClTm.τ g κ) κ'!})))))

{-
□⇒-iso₁ : ∀{ℓ} (A : Set ℓ) (c : ClTy ℓ) (x : ClTm ℓ (∁ A ⇒ □ c))
  → ClTm ℓ (app (□⇒ A c) (app (□⇒-inv A c) x) ≡[ ∁ A ⇒ □ c ] x)
□⇒-iso₁ A (ctx B nB aB) (tm g ng) = toId {x = app (□⇒ A (ctx B nB aB)) (app (□⇒-inv A (ctx B nB aB)) (tm g ng))} {tm g ng}
  (λ κ → Pi-eq (funext (λ α → funext (λ x → Box-eq (funext (λ κ' → h-eq κ _ x κ'))))))
  where
    h : (κ : Clock) (α : Tick= κ) (x : A) (κ' : Clock) → B κ'
    h = curry (curry (Box.lim ∘ uncurry (uncurry (Pi.f ∘ g))))

--    h-eq' : (κ : Clock) (α : Tick κ) → Ctx.next (∁ A ⇒ □ (ctx B nB aB)) κ α (g κ) ≡ g α --g κ ≡ {!!}
--    h-eq' κ α = ng κ α

    h-eq' : (κ : Clock) (α : Tick= κ) → h κ κ ≡ h κ α
    h-eq' κ α = {!!}

    h-eq : (κ : Clock) (α : Tick= κ) (x : A) (κ' : Clock) → h κ κ x κ' ≡ h κ α x κ'
    h-eq κ α x κ' = {!(Pi.nextᶠ ∘ g) κ κ !}

□⇒-iso₂ : ∀{ℓ} (A : Set ℓ) (c : ClTy ℓ) (x : ClTm ℓ (□ (∁ A ⇒ c)))
  → ClTm ℓ (app (□⇒-inv A c) (app (□⇒ A c) x) ≡[ □ (∁ A ⇒ c) ] x)
□⇒-iso₂ A c (tm g ng) = toId {x = app (□⇒-inv A c) (app (□⇒ A c) (tm g ng))} {tm g ng}
  (λ κ' → Box-eq (funext (λ κ → Pi-eq (funext (λ β → {!Box.rest (g κ') κ!}))))) --(trans (funext (λ β → funext (λ x → {!Pi.nextᶠ  (box.lim !})))
                                           --  (cong Pi.f (Box.rest (g κ') (↑ κ) κ)))))) 

-}

{-
-- -- □ (∏ (∁ A) B) ≅ ∏ (∁ A) (□ B)

□∏' : ∀{ℓ} (A : Set ℓ) (t : Ty ℓ (∁ A))
  → ClTm ℓ (□ (∏ (∁ A) t) ⇒ ∏ (∁ A) {!!})
□∏' = {!!}

□∏ : ∀{ℓ} (A : Set ℓ) (t : Ty ℓ (∁ A))
  → ClTm ℓ (□ (∏ (∁ A) t) ⇒ ∏ (□ (∁ A)) (□ᵀʸ (∁ A) t))
□∏ A t =
  tm (λ _ → pi (λ { _ (box g r) → pi (λ { _ (box x q) → box (λ κ → Pi.f (g κ) κ (x κ))
                                                            (λ {κ α → transOver (Pi.nextᶠ (g κ) κ α (x κ))
                                                                                 (cong-appOver (q κ α) (cong (λ z → Pi.f z α) (r κ α))) })})
                                     (λ {_ _ _ → refl }) })
               (λ {_ _ _ → refl }))
     (λ {_ _ → refl})

□∏-inv : ∀{ℓ} (A : Set ℓ) (t : Ty ℓ (∁ A))
  → ClTm ℓ (∏ (□ (∁ A)) (□ᵀʸ (∁ A) t) ⇒ □ (∏ (∁ A) t))
□∏-inv A (ty B nB aB) = 
  tm (λ κ → pi (λ { α (pi g q) → box (λ κ' → pi (λ {β x → Boxᵀʸ.limᵀʸ (g α (box (λ _ → x) (λ {_ _ → refl}))) β})
                                                (λ {β γ x → Boxᵀʸ.restᵀʸ (g α (box (λ _ → x) (λ {_ _ → refl}))) β γ}))
                                     (λ { _ _ → refl})})
               (λ { α β (pi g q) →
                 Box-eq (funext (λ κ' → Pi-eq (funext (λ γ → funext (λ x → cong (λ z → Boxᵀʸ.limᵀʸ z _) (q α β (box (λ _ → x) (λ {_ _ → refl})))))))) }))
     (λ {κ α → Pi-eq refl })


□∏-iso₂ : ∀{ℓ} (A : Set ℓ) (t : Ty ℓ (∁ A)) (x : ClTm ℓ (□ (∏ (∁ A) t)))
  → ClTm ℓ (app (□∏-inv A t) (app (□∏ A t) x) ≡[ □ (∏ (∁ A) t) ] x)
□∏-iso₂ A t (tm g ng) = toId {x = app (□∏-inv A t) (app (□∏ A t) (tm g ng))} {tm g ng}
  (λ κ → Box-eq (funext (λ κ' → Pi-eq (funext (λ α → funext (λ x → {!Box.rest (g κ) κ' !}))))))

□∏-iso₁ : ∀{ℓ} (A : Set ℓ) (t : Ty ℓ (∁ A)) (x : ClTm ℓ (∏ (□ (∁ A)) (□ᵀʸ (∁ A) t)))
  → ClTm ℓ (app (□∏ A t) (app (□∏-inv A t) x) ≡[ ∏ (□ (∁ A)) (□ᵀʸ (∁ A) t) ] x)
□∏-iso₁ A t (tm g ng) = toId {x = app (□∏ A t) (app (□∏-inv A t) (tm g ng))} {tm g ng}
  (λ κ → Pi-eq (funext (λ α → funext (λ { (box l q) → Boxᵀʸ-eq (funext (λ κ' → {!Boxᵀʸ.restᵀʸ (Pi.f (g κ) α (box l q))!}))}))))
-}

-- -- □ ⊳ A ≅ □ A

□⊳ : ∀{ℓ} (c : ClTy ℓ)
  → ClTm ℓ (□ c ⇒ □ (⊳ c))
□⊳ (ctx A nA aA) =
  tm (λ κ → pi (λ { α (box x q) → box (λ κ' → later (ltr x) q)
                                      (λ { κ' β → Later-eq (⊳≡ (ltr-eq (λ { _ → funext (q β) }))) })})
               (λ {_ _ _ → refl}))
     (λ {_ _ → refl})

□⊳-inv : ∀{ℓ} (c : ClTy ℓ)
  → ClTm ℓ (□ (⊳ c) ⇒ □ c)
□⊳-inv (ctx A nA aA) =
  tm (λ _ → pi (λ { α (box x q) → box (force (Later.L (x κ₀)))
                                      (Later.nextᴸ (x κ₀))})
               (λ {_ _ _ → refl}))
     (λ {_ _ → refl})

□⊳-iso₁ : ∀{ℓ} (c : ClTy ℓ) (x : ClTm ℓ (□ c))
  → ClTm ℓ (app (□⊳-inv c) (app (□⊳ c) x) ≡[ □ c ] x)
□⊳-iso₁ c x = toId {x = app (□⊳-inv c) (app (□⊳ c) x)} (λ _ → refl)
  
□⊳-iso₂ : ∀{ℓ} (c : ClTy ℓ) (x : ClTm ℓ (□ (⊳ c)))
  → ClTm ℓ (app (□⊳ c) (app (□⊳-inv c) x) ≡[ □ (⊳ c) ] x)
□⊳-iso₂ c (tm x nx) = toId {x = app (□⊳ c) (app (□⊳-inv c) (tm x nx))}
  (λ κ → Box-eq (funext (λ κ' → Later-eq (⊳≡ (ltr-eq (λ _ →
    trans (funext (λ { _  → sym (Later.nextᴸ (Box.lim (x κ) κ₀) κ' _) }))
          (cong (force ∘ Later.L) (Box.rest (x κ) κ₀ κ'))))))))

{-

--next∁ : ∀{ℓ} → (A : Set ℓ)
--  → (κ : Clock) (α : Tick κ) → Const A κ → Const A α
--next∁ _ _ _ x = x

--next∁-ass : ∀{ℓ} → (A : Set ℓ)
--  → (κ : Clock) (α : Tick κ) (β : Tick α) (ρ : Const A κ)
--  → next∁ A α β (next∁ A κ α ρ) ≡ next∁ A κ β ρ
--next∁-ass _ _ _ _ _ = refl



--□∁-f : ∀{ℓ} (A : Set ℓ)
--  → (κ : Clock) (α : Tick= κ)
--  → (x : Box (∁ A)) → A
--□∁-f A κ α (box x p) = x κ₀

--□∁-nextᶠ : ∀{ℓ} (A : Set ℓ)
--  → (κ : Clock) (α : Tick= κ)

--□∁-τ : ∀{ℓ} (A : Set ℓ)
--  → (κ : Clock) → Fun (□ (∁ A)) (∁ A) κ
--□∁-τ A κ = pi (□∁-f A κ) {!!}



--□∁-inv-f : ∀{ℓ} (A : Set ℓ)
--  → (κ : Clock) (α : Tick= κ)
--  → (x : A) → Box (∁ A)
--□∁-inv-f A κ α x = box (λ _ → x) r
--  where
--    r : ∀ κ' α' → _
--    r _ _ = refl

--□∁-inv-τ : ∀{ℓ} (A : Set ℓ)
--  → (κ : Clock) → Fun (∁ A) (□ (∁ A)) κ
--□∁-inv-τ A κ = pi (□∁-inv-f A κ) {!!}


{-

-- Clock quantification

Box : ∀{ℓ} → (Clock → Set ℓ) → Set ℓ
Box A = (κ : Clock) → A κ

□ : ∀{ℓ} → ClTy ℓ → ClTy ℓ
□ c = ∁ (Box Γ)
  where
    open Ctx c

□ᵀʸ : ∀{ℓ} (c : Ctx ℓ) → Ty ℓ c → Ty ℓ (□ c)
□ᵀʸ (ctx Γ nΓ aΓ) (ty A nA aA) =
  ty (λ _ ρ → (κ : Clock) → A κ (ρ κ)) q r
  where
    q : (i : Clock) (α : Tick i) (ρ : (κ : Clock) → Γ κ)
      → ((κ : Clock) → A κ (ρ κ)) → (κ : Clock) → A κ (ρ κ)
    q _ _ ρ x κ = x κ

    r : (i : Clock) (α : Tick i) (β : Tick α) (ρ : (κ : Clock) → Γ κ)
      → (x : (κ : Clock) → A κ (ρ κ)) → (λ κ → x κ) ≡ (λ κ → x κ)
    r _ _ _ _ _ = refl


BoxConst-f : ∀{ℓ} (A : Set ℓ)
  → (κ : Clock) (α : Tick= κ) (x : Clock → A) → A
BoxConst-f A κ α x = x κ₀

BoxConst-nextᶠ : ∀{ℓ} (A : Set ℓ)
  → (κ : Clock) (α : Tick= κ) (β : Tick (tick α))
  → (x : Clock → A) → x κ₀ ≡ x κ₀
BoxConst-nextᶠ _ _ _ _ _ = refl

BoxConst : ∀{ℓ} (A : Set ℓ)
  → (κ : Clock) → Pi (□ (∁ A)) (Ctx→Ty (∁ A) (□ (∁ A))) κ
BoxConst A κ = pi (BoxConst-f A κ) (BoxConst-nextᶠ A κ) 

BoxConst-nextᵀᵐ : ∀{ℓ} (A : Set ℓ)
  → (κ : Clock) (α : Tick κ)
  → Ctx.next (□ (∁ A) ⇒ ∁ A) κ α (BoxConst A κ) ≡ BoxConst A α
BoxConst-nextᵀᵐ A κ α = Pi-eq (funext (λ _ → funext (λ x → refl)))

□∁ : ∀{ℓ} (A : Set ℓ)
  → ClTm ℓ (□ (∁ A) ⇒ ∁ A)
□∁ A = tm (BoxConst A) (BoxConst-nextᵀᵐ A)

BoxConst-inv-f : ∀{ℓ} (A : Set ℓ)
  → (κ : Clock) (α : Tick= κ) (x : A) (κ' : Clock) → A
BoxConst-inv-f A _ _ x _ = x

BoxConst-inv-nextᶠ : ∀{ℓ} (A : Set ℓ)
  → (κ : Clock) (α : Tick= κ) (β : Tick (tick α)) (x : A)
  → (λ (κ' : Clock) → x) ≡ (λ κ' → x)
BoxConst-inv-nextᶠ _ _ _ _ _ = refl  

BoxConst-inv : ∀{ℓ} (A : Set ℓ)
  → (κ : Clock) → Pi (∁ A) (Ctx→Ty (□ (∁ A)) (∁ A)) κ
BoxConst-inv A κ = pi (BoxConst-inv-f A κ) (BoxConst-inv-nextᶠ A κ)

BoxConst-inv-nextᵀᵐ : ∀{ℓ} (A : Set ℓ)
  → (κ : Clock) (α : Tick κ)
  → Ctx.next (∁ A ⇒ □ (∁ A)) κ α (BoxConst-inv A κ) ≡ BoxConst-inv A α
BoxConst-inv-nextᵀᵐ A κ α = Pi-eq refl

□∁-inv : ∀{ℓ} (A : Set ℓ)
  → ClTm ℓ (∁ A ⇒ □ (∁ A))
□∁-inv A = tm (BoxConst-inv A) (BoxConst-inv-nextᵀᵐ A)

□∁-iso₁ : ∀{ℓ} (A : Set ℓ) (x : ClTm ℓ (∁ A))
  → ClTm ℓ (app (□∁ A) (app (□∁-inv A) x) ≡[ ∁ A ] x)
□∁-iso₁ A x = toId {x = app (□∁ A) (app (□∁-inv A) x)} (λ _ → refl)

□∁-iso₂ : ∀{ℓ} (A : Set ℓ) (x : ClTm ℓ (□ (∁ A)))
  → ClTm ℓ (app (□∁-inv A) (app (□∁ A) x) ≡[ □ (∁ A) ] x)
□∁-iso₂ A (tm x nx) = toId {x = app (□∁-inv A) (app (□∁ A) (tm x nx))}
  {!!} --(λ κ → funext (λ κ' → {!nx κ₀ κ!}))

test : ∀{ℓ} (A : Set ℓ) (x : Box (Const A)) (κ : Clock)
  → x ∞ ≡ x κ
test A x = {!!}

-- □ (∏ (∁ A) B) ≅ ∏ (∁ A) (□ B)

□∏-f : ∀{ℓ} (X : Set ℓ) (t : Ty ℓ (∁ X))
  → (i : Clock) (α : Tick= i) (g : Ctx.Γ (□ (∏ (∁ X) t)) (tick α))
  → Ty.A (Ctx→Ty (∏ (□ (∁ X)) (□ᵀʸ (∁ X) t)) (□ (∏ (∁ X) t))) (tick α) g
□∏-f X (ty A nA aA) _ _ g' = pi (λ _ x κ → g κ (κ , refl≤ˢ) (x κ)) r
  where
    g : (κ : Clock) (α : Tick= κ) (x : X) → A (tick α) x
    g κ = Pi.f (g' κ)

    r : ∀ α β x → _
    r _ _ _ = refl

□∏-nextᶠ : ∀{ℓ} (X : Set ℓ) (t : Ty ℓ (∁ X))
  → (i : Clock) (α : Tick= i) (β : Tick (tick α))
  → (x : Ctx.Γ (□ (∏ (∁ X) t)) (tick α))
  → Ty.nextᵀʸ (Ctx→Ty (∏ (□ (∁ X)) (□ᵀʸ (∁ X) t)) (□ (∏ (∁ X) t))) (tick α) β x (□∏-f X t i α x)
    ≡
    □∏-f X t i (coeˢ α β) (Ctx.next (□ (∏ (∁ X) t)) (tick α) β x)
□∏-nextᶠ X t _ _ _ _ = Pi-eq refl
  
□∏-τ : ∀{ℓ} (X : Set ℓ) (t : Ty ℓ (∁ X))
  → (κ : Clock)
  → Ctx.Γ (□ (∏ (∁ X) t) ⇒ ∏ (□ (∁ X)) (□ᵀʸ (∁ X) t)) κ
□∏-τ X t _ = pi (□∏-f X t _) (□∏-nextᶠ X t _)

□∏-nextᵀᵐ : ∀{ℓ} (X : Set ℓ) (t : Ty ℓ (∁ X))
  → (κ : Clock)(α : Tick κ)
  → Ctx.next (□ (∏ (∁ X) t) ⇒ ∏ (□ (∁ X)) (□ᵀʸ (∁ X) t)) κ α (□∏-τ X t κ)
    ≡
    □∏-τ X t α
□∏-nextᵀᵐ X t _ _ = Pi-eq refl

□∏ : ∀{ℓ} (X : Set ℓ) (t : Ty ℓ (∁ X))
  → ClTm ℓ (□ (∏ (∁ X) t) ⇒ ∏ (□ (∁ X)) (□ᵀʸ (∁ X) t))
□∏ X t = tm (□∏-τ X t) (□∏-nextᵀᵐ X t)

□∏-inv-f : ∀{ℓ} (X : Set ℓ) (t : Ty ℓ (∁ X))
  → (κ : Clock) (α : Tick= κ)
  → (g : Ctx.Γ (∏ (□ (∁ X)) (□ᵀʸ (∁ X) t)) (tick α))
  → Ty.A (Ctx→Ty (□ (∏ (∁ X) t)) (∏ (□ (∁ X)) (□ᵀʸ (∁ X) t))) (tick α) g
□∏-inv-f X (ty A nA aA) _ β (pi g ng) κ =
  pi (λ α x → g ((tick β) , refl≤ˢ) (λ _ → x) (tick α)  ) r
  where
    r : ∀ α γ x → _
    r α γ x = {!ng!}


□∏-inv-τ : ∀{ℓ} (X : Set ℓ) (t : Ty ℓ (∁ X))
  → (κ : Clock)
  → Ctx.Γ (∏ (□ (∁ X)) (□ᵀʸ (∁ X) t) ⇒ □ (∏ (∁ X) t)) κ
□∏-inv-τ X t κ = pi (□∏-inv-f X t κ) {!!}

□∏-inv : ∀{ℓ} (X : Set ℓ) (t : Ty ℓ (∁ X))
  → ClTm ℓ (∏ (□ (∁ X)) (□ᵀʸ (∁ X) t) ⇒ □ (∏ (∁ X) t))
□∏-inv X t = tm {!!} {!!}
-}
-}
-}
