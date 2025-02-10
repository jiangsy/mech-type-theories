
{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

module NonCumulative.Statics.Unascribed.Soundness  (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂)  where

open import Lib

open import NonCumulative.Statics.Ascribed.Presup as A
open import NonCumulative.Statics.Ascribed.CtxEquiv as A
open import NonCumulative.Statics.Ascribed.Refl as A
open import NonCumulative.Statics.Ascribed.Misc as A
open import NonCumulative.Statics.Ascribed.Inversion as A
open import NonCumulative.Statics.Ascribed.Properties.Contexts as A
open import NonCumulative.Statics.Ascribed.Properties as A
open import NonCumulative.Completeness.Consequences fext
open import NonCumulative.Consequences fext
open import NonCumulative.Statics.Ascribed.Full as A renaming (Ctx to lCtx)
open import NonCumulative.Statics.Ascribed.Simpl
open import NonCumulative.Statics.Unascribed.Full as U
open import NonCumulative.Statics.Unascribed.Transfer

U⇒A-vlookup : ∀ {x} →
 A.Γ [↝] U.Γ′ →
 x ∶ U.T′ ∈! U.Γ′ →
 ∃₂ λ i T → (T ↝ U.T′) × (x ∶[ i ] T ∈! A.Γ)
U⇒A-vlookup (↝∷ {Γ′} {Γ} {T′} {T} {i′} Γ↝Γ′ T↝T′) here = _ , _ , (↝sub T↝T′ ↝wk , here) 
U⇒A-vlookup (↝∷ Γ↝Γ′ _) (there x∈Γ') with U⇒A-vlookup Γ↝Γ′ x∈Γ'
... | i , T , T↝T′ , x∈Γ = _ , _ , ↝sub T↝T′ ↝wk , there x∈Γ

unique-lvl : ∀ {i j} →
 A.Γ ⊢ A.t ∶[ i ] A.T →
 A.Γ ⊢ A.t ∶[ j ] A.T′ →
 i ≡ j 
unique-lvl ⊢t ⊢t′ = proj₁ (unique-typ ⊢t ⊢t′)

∷-inv : ∀ {i j} →
 A.⊢ ((A.T ↙ i) ∷ A.Γ) ≈ ((A.S ↙ j) ∷ A.Δ) →
 A.⊢ A.Γ ≈ A.Δ
∷-inv (∷-cong x x₁ x₂ x₃ x₄) = x

∷-inv′ : ∀ {i} →
 A.⊢ ((A.T ↙ i) ∷ A.Γ) ≈ ((A.S ↙ i) ∷ A.Δ) →
 A.⊢ A.Γ ≈ A.Δ
∷-inv′ ⊢s = ∷-inv ⊢s

mutual
  U⇒A-⊢ : U.⊢ U.Γ′ →
          -------
          ∃ λ Γ → (A.⊢ Γ × Γ [↝] U.Γ′ × (∀ {Γ₁} → Γ₁ [↝] U.Γ′ → A.⊢ Γ₁ → A.⊢ Γ ≈ Γ₁))
  U⇒A-⊢ ⊢[] = [] , ⊢[] , ↝[] , λ { ↝[] ⊢[] → []-≈ }
  U⇒A-⊢ (⊢∷ ⊢Γ′ ⊢T′)
    with U⇒A-⊢ ⊢Γ′
      | U⇒A-tm ⊢T′
  ...  | Γ , ⊢Γ , ↝Γ , IHΓ
      | i , Γ′ , T′ , .(Se _) , ↝Γ′ , ↝T , ↝Se , ⊢T , IHT
      with ⊢T:Se-lvl ⊢T
          | presup-tm ⊢T
  ...     | refl
          | ⊢Γ′ , _
          with IHΓ ↝Γ′ ⊢Γ′
  ...        | Γ≈Γ′ = (T′ ↙ _) ∷ Γ , ⊢∷ ⊢Γ (ctxeq-tm (⊢≈-sym Γ≈Γ′) ⊢T) , ↝∷ ↝Γ ↝T , helper
    where  helper : ∀ {Γ₁} → Γ₁ [↝] _ → A.⊢ Γ₁ → A.⊢ _ ≈ Γ₁
           helper (↝∷ ↝Γ₁ T₁↝) (⊢∷ ⊢Γ₁ ⊢T₁)
            with IHΓ ↝Γ₁ ⊢Γ₁
           ...  | Γ≈Γ₁
            with (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₁) Γ≈Γ′) ⊢T₁)
           ... | ⊢T₁′
            with IHT T₁↝ ⊢T₁′
           ...  | T≈T₁
            with unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
           ... | refl = ∷-cong-simp Γ≈Γ₁ (ctxeq-≈ (⊢≈-sym Γ≈Γ′) T≈T₁)

  U⇒A-tm : U.Γ′ U.⊢ U.t′ ∶ U.T′ →
          -------------
          ∃₂ λ i Γ → ∃₂ λ t T →
            (Γ [↝] U.Γ′) ×
            (t ↝ U.t′) ×
            (T ↝ U.T′) ×
            Γ A.⊢ t ∶[ i ] T ×
            (∀ {t₁ i₁ T₁} →
                t₁ ↝ U.t′ →
                Γ ⊢ t₁ ∶[ i₁ ] T₁ →
                Γ A.⊢ t ≈ t₁ ∶[ i₁ ] T₁)
  U⇒A-tm (N-wf ⊢Γ′)
    with U⇒A-⊢ ⊢Γ′
  ...  | Γ , ⊢Γ , Γ↝ , IHΓ = _ , _ , _ , _ , Γ↝ , ↝N , ↝Se , N-wf ⊢Γ , λ { ↝N ⊢N → ≈-refl ⊢N }
  U⇒A-tm (Se-wf i ⊢Γ′)
    with U⇒A-⊢ ⊢Γ′
  ...  | Γ , ⊢Γ , Γ↝ , IHΓ = _ , _ , _ , _ , Γ↝ , ↝Se , ↝Se , Se-wf _ ⊢Γ , λ { ↝Se ⊢Se → ≈-refl ⊢Se }
  U⇒A-tm (Liftt-wf n ⊢T′)
    with U⇒A-tm ⊢T′
  ... | _ , Γ , T , .(Se _) , Γ↝ , T↝ , ↝Se , ⊢T , IHT
    with ⊢T:Se-lvl ⊢T
  ... | refl = _ , _ , _ , _ , Γ↝ , ↝Liftt T↝ , ↝Se , Liftt-wf _ ⊢T , helper
    where helper : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
          helper (↝Liftt t₁↝) ⊢t₁ = {!   !}
  U⇒A-tm (Π-wf {Γ = Γ′} {S = S′} {T = T′} ⊢Γ′ ⊢S′ ⊢T′ k≡maxij)
    with U⇒A-⊢ ⊢Γ′
       | U⇒A-tm ⊢S′
       | U⇒A-tm ⊢T′
  ...  | Γ , ⊢Γ , Γ↝ , IHΓ
       | _ , Γ₁ , S , _ , Γ↝₁ , S↝ , ↝Se , ⊢S , IHS
       | _ , _ , T , .(Se _) , (↝∷ {T = S₁} Γ↝₂ S↝₁) , T↝ , ↝Se , ⊢T , IHT
    with ⊢T:Se-lvl ⊢S
       | ⊢T:Se-lvl ⊢T
  ...  | refl | refl
    with ⊢∷ ⊢Γ₂ ⊢S₂ ← proj₁ (presup-tm ⊢T)
    with IHΓ Γ↝₁ (proj₁ (presup-tm ⊢S))
       | IHΓ Γ↝₂ ⊢Γ₂
  ...  | Γ≈Γ₁ | Γ≈Γ₂
    with Γ₁≈Γ₂ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁
    with IHS S↝₁ (ctxeq-tm Γ₁≈Γ₂ ⊢S₂)
  ...  | S≈S₂
    with unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₂)))
  ...  | refl = _ , _ , _ , _ , Γ↝ , ↝Π S↝ T↝ , ↝Se , Π-wf (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S) (ctxeq-tm (⊢≈-sym S∷Γ≈S₂∷Γ₂) ⊢T) k≡maxij , helper
      where S∷Γ≈S₂∷Γ₂ : A.⊢ (S ↙ _) L.∷ Γ ≈ (S₁ ↙ _) L.∷ _
            S∷Γ≈S₂∷Γ₂ = ∷-cong Γ≈Γ₂ (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S) ⊢S₂ (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) S≈S₂) (ctxeq-≈ (⊢≈-sym Γ₁≈Γ₂) S≈S₂)

            helper : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
            helper (↝Π S₁↝ T₁↝) ⊢Πt₁
              with Π-inv′ ⊢Πt₁
            ... | refl , ≈Se , ⊢S₁ , ⊢T₁
              with IHS S₁↝ (ctxeq-tm Γ≈Γ₁ ⊢S₁)
            ... | S≈S₁
              with unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
            ... | refl
              with S₁≈S₂ ← ≈-trans (≈-sym S≈S₁) S≈S₂
              with IHT T₁↝ (ctxeq-tm (∷-cong Γ≈Γ₂ ⊢S₁ ⊢S₂ (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) S₁≈S₂) (ctxeq-≈ (⊢≈-sym Γ₁≈Γ₂) S₁≈S₂)) ⊢T₁)
            ... | T≈T₁
              with unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
            ... | refl = ≈-conv (Π-cong (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) S≈S₁) (ctxeq-≈ (⊢≈-sym S∷Γ≈S₂∷Γ₂) T≈T₁) refl) (≈-sym ≈Se)

  U⇒A-tm (vlookup ⊢Γ′ x∈Γ')
    with U⇒A-⊢ ⊢Γ′
  ...  | Γ , ⊢Γ , Γ↝ , IHΓ
    with U⇒A-vlookup Γ↝ x∈Γ'
  ...  | _ , _ , T↝ , x∈Γ = _ , _ , _ , _ , Γ↝ , ↝v , T↝ , vlookup ⊢Γ x∈Γ , λ { ↝v ⊢v → ≈-refl ⊢v }
  U⇒A-tm (ze-I ⊢Γ′) with U⇒A-⊢ ⊢Γ′
  ... | Γ , ⊢Γ , Γ↝ , IHΓ = _ , _ , _ , _ , Γ↝ , ↝ze , ↝N , ze-I ⊢Γ , λ { ↝ze ⊢ze → ≈-refl ⊢ze }
  U⇒A-tm (su-I {t = t′} ⊢t′)
    with U⇒A-tm ⊢t′
  ...  | _ , Γ , t , .N , Γ↝ , t↝ , ↝N , ⊢t , IHt
    with  ⊢t∶N-lvl ⊢t
  ...  | refl = _ , _ , _ , _ , Γ↝ , ↝su t↝ , ↝N , (su-I ⊢t) , helper
    where helper : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
          helper (↝su t₁↝) ⊢sut₁
            with su-inv ⊢sut₁
          ...  | refl , T₁≈N , ⊢t₁ = ≈-conv (su-cong (IHt t₁↝ ⊢t₁)) (≈-sym T₁≈N)

  U⇒A-tm (N-E {T = T′} {s = s′} {r = r′} {t = t′} ⊢Γ′ ⊢T′ ⊢s′ ⊢r′ ⊢t′)
    with U⇒A-⊢ ⊢Γ′
       | U⇒A-tm ⊢T′
       | U⇒A-tm ⊢s′
       | U⇒A-tm ⊢r′
       | U⇒A-tm ⊢t′
  ...  | Γ , ⊢Γ , Γ↝ , IHΓ
       | _ , _ , T , _ , (↝∷ Γ₁↝ ↝N) , T↝ , ↝Se , ⊢T , IHT
       | j , Γ₂ , s , _ , Γ₂↝ , s↝ , ↝sub {t = T₁} T↝₁ (↝, {T = T₄} ↝I ↝ze) , ⊢s , IHs
       | k , _ , r , _ , (↝∷ {T = T₃} (↝∷ Γ₃↝ ↝N) T↝₃) , r↝ , ↝sub {t = T₂} T↝₂ (↝, (↝∘ ↝wk ↝wk) (↝su ↝v)) , ⊢r , IHr
       | _ , Γ₄ , t , _ , Γ₄↝ , t↝ , ↝N , ⊢t , IHt
    with (⊢∷ {Γ = Γ₁} ⊢Γ₁ ⊢N₁) ← proj₁ (presup-tm ⊢T)
       | ⊢Γ₂ , ⊢T₁[|ze] ← presup-tm ⊢s
       | (⊢∷ (⊢∷ ⊢Γ₃ ⊢N₂) ⊢T₄) , ⊢T₁[wkwk,ze] ← (presup-tm ⊢r)
    with N≈⇒eq-lvl (≈-refl ⊢N₁)
       | N≈⇒eq-lvl (≈-refl ⊢N₂)
  ...  | refl | refl
    with ⊢T:Se-lvl ⊢T
  ...  | refl
    with IHΓ Γ₁↝ ⊢Γ₁
       | IHΓ Γ₂↝ (proj₁ (presup-tm ⊢s))
       | IHΓ Γ₃↝ ⊢Γ₃
       | IHΓ Γ₄↝ (proj₁ (presup-tm ⊢t))
  ...  | Γ≈Γ₁ | Γ≈Γ₂ | Γ≈Γ₃ | Γ≈Γ₄
    with IHT T↝₃ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁) (≈-refl (N-wf ⊢Γ₃) )) ⊢T₄)
  ...  | T≈T₃
    with unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₃)))
  ...  | refl , _
      = _ , _ , _ , _ , Γ↝ , ↝rec T↝ s↝ r↝ t↝ , ↝sub T↝ (↝, ↝I t↝) ,
          N-E (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (≈-refl (N-wf ⊢Γ₁))) ⊢T) ⊢s_ ⊢r_ ⊢t_ , helper
    where

          ⊢s_ : Γ ⊢ s ∶[ _ ] T [| ze ∶ N₀ ]
          ⊢s_
            with t[σ]-inv ⊢T₁[|ze]
          ... | Γ₂∷N , _ , ⊢[|ze] , ⊢T₁ , _
            with ,-inv ⊢[|ze]
          ... | Γ₅ , ⊢I , ⊢ze , N∷Γ₅≈N∷Δ
            with ∷-cong Γ₅≈Δ _ _ _ _ ← N∷Γ₅≈N∷Δ
            with ze-inv ⊢ze
          ... | refl , ≈N
            with _ , ∷-cong Γ₂≈Δ Γ₂⊢T₄ _ _ _ ← ,-inv′ ⊢[|ze] (s-I ⊢Γ₂)
            with Γ₂≈Γ₅ ← ⊢≈-trans Γ₂≈Δ (⊢≈-sym Γ₅≈Δ)
            with Γ₅≈Γ ← ⊢≈-trans (⊢≈-sym Γ₂≈Γ₅) (⊢≈-sym Γ≈Γ₂)
            with T₄≈N ← [I]-≈ˡ-Se ≈N
            with Γ₁≈Γ₂ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₁) Γ≈Γ₂
            with IHT T↝₁ (ctxeq-tm (⊢≈-trans (⊢≈-sym N∷Γ₅≈N∷Δ) (∷-cong-simp (⊢≈-trans Γ₅≈Γ Γ≈Γ₁) (ctxeq-≈ Γ₂≈Γ₅ T₄≈N)) ) ⊢T₁)
          ... | T≈T₁
            with unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
          ... | refl , Sej≈ = ctxeq-tm (⊢≈-sym Γ≈Γ₂) (conv ⊢s ([]-cong-Se (ctxeq-≈ (∷-cong-simp Γ₁≈Γ₂ (ctxeq-≈ (⊢≈-sym Γ₁≈Γ₂)  (≈-sym T₄≈N))) (≈-conv (≈-sym T≈T₁) (≈-sym Sej≈) )) (s-, (s-I ⊢Γ₂) Γ₂⊢T₄ ⊢ze) (,-cong (s-≈-refl (s-I ⊢Γ₂))  Γ₂⊢T₄ T₄≈N (≈-refl (conv (ze-I ⊢Γ₂) (≈-sym ≈N) )))) )

          ⊢r_ : (T ↙ _) L.∷ N₀ L.∷ Γ ⊢ r ∶[ _ ] sub T ((wk ∘ wk) , su (v 1) ∶ N₀)
          ⊢r_
            with t[σ]-inv  ⊢T₁[wkwk,ze]
          ...  | Γ₃∷N∷T , _ , ⊢wkwk,ze , ⊢T₁ , _
            with ,-inv  ⊢wkwk,ze
          ...  | Γ₆ , ⊢wkwk1 , ⊢su , ∷-cong Γ₆≈Δ ⊢T₅ _ T₅≈T′₁ _
            with ⊢TNΓ₃ ← ⊢wk∘wk-gen (proj₁ (presup-tm ⊢r))
            with Γ₃≈Δ ← ∷-inv′ (proj₂ (,-inv′ ⊢wkwk,ze ⊢TNΓ₃))
            with Γ≈Δ ← ⊢≈-trans Γ≈Γ₃ Γ₃≈Δ
            with Γ≈Γ₆ ← ⊢≈-trans Γ≈Δ (⊢≈-sym Γ₆≈Δ)
            with Γ₁≈Γ₃ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₁) Γ≈Γ₃
            with su-inv ⊢su
          ...  | refl , T₅[wkwk]≈N , _
            with Γ₃⊢T₅ ← ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₆) Γ≈Γ₃) ⊢T₅
            with T[wkwk]≈N-inv Γ₃⊢T₅ T₅[wkwk]≈N
          ...  | T₅≈N
            with IHT T↝₂ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Δ) Γ≈Γ₁) (≈-trans (ctxeq-≈ (⊢≈-trans (⊢≈-sym Γ≈Γ₆) Γ≈Δ) (≈-sym T₅≈T′₁)) (ctxeq-≈ Γ₃≈Δ T₅≈N) ))  ⊢T₁)
          ...  | T≈T₂
            with unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₂)))
          ...  | refl , Sej≈ =  ctxeq-tm (∷-cong-simp (∷-cong-simp (⊢≈-sym Γ≈Γ₃) (≈-refl (N-wf ⊢Γ₃) )) (ctxeq-≈ (∷-cong-simp Γ₁≈Γ₃ (≈-refl (N-wf ⊢Γ₁))) (≈-sym T≈T₃)))
                        (conv ⊢r ([]-cong-Se (≈-sym (ctxeq-≈ (∷-cong-simp Γ₁≈Γ₃ (ctxeq-≈ (⊢≈-sym  Γ₁≈Γ₃) (≈-sym T₅≈N) ))  (≈-conv T≈T₂ (≈-sym Sej≈) ) )) (s-,  ⊢TNΓ₃ Γ₃⊢T₅ ⊢su) (,-cong (s-≈-refl ⊢TNΓ₃) Γ₃⊢T₅ T₅≈N (≈-refl ⊢su))))

          ⊢t_ : Γ ⊢ t ∶[ _ ] N
          ⊢t_
            with ⊢t∶N-lvl ⊢t
          ...  | refl = (ctxeq-tm (⊢≈-sym Γ≈Γ₄) ⊢t)

          helper : ∀ {tᵢ iᵢ Tᵢ} → tᵢ ↝ _ → Γ A.⊢ tᵢ ∶[ iᵢ ] Tᵢ → Γ ⊢ _ ≈ tᵢ ∶[ iᵢ ] Tᵢ
          helper (↝rec ↝Tᵢ ↝sᵢ ↝rᵢ ↝tᵢ) ⊢rectᵢ 
            with rec-inv ⊢rectᵢ
          ...  | refl , ⊢Tᵢ , ⊢sᵢ , ⊢rᵢ , ⊢tᵢ , Tᵢ≈
            with N∷Γ≈N∷Γ₁ ← ∷-cong-simp (⊢≈-sym Γ≈Γ₁)  (≈-refl (N-wf ⊢Γ₁) )
               | N∷Γ≈N∷Γ₃ ← ∷-cong-simp (⊢≈-sym Γ≈Γ₃)  (≈-refl (N-wf ⊢Γ₃) )
            with IHT ↝Tᵢ (ctxeq-tm (⊢≈-sym N∷Γ≈N∷Γ₁) ⊢Tᵢ)
          ...  | T≈Tᵢ
            with unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈Tᵢ)))
          ...  | refl
            with IHs ↝sᵢ (ctxeq-tm Γ≈Γ₂ ⊢sᵢ)
               | IHr ↝rᵢ (ctxeq-tm (∷-cong-simp (⊢≈-sym N∷Γ≈N∷Γ₃) (ctxeq-≈ N∷Γ≈N∷Γ₁ (≈-trans (≈-sym T≈Tᵢ ) T≈T₃)) ) ⊢rᵢ)
               | IHt ↝tᵢ (ctxeq-tm Γ≈Γ₄ ⊢tᵢ)
          ...  | s≈sᵢ | r≈rᵢ | t≈tᵢ = ≈-conv (≈-sym (rec-cong ⊢Tᵢ (ctxeq-≈ N∷Γ≈N∷Γ₁ (≈-sym T≈Tᵢ)) (ctxeq-≈ (⊢≈-sym Γ≈Γ₂) (≈-sym s≈sᵢ)) (ctxeq-≈ (∷-cong-simp N∷Γ≈N∷Γ₃ (ctxeq-≈ (⊢≈-trans N∷Γ≈N∷Γ₁ (⊢≈-sym N∷Γ≈N∷Γ₃)) (≈-trans (≈-sym T≈T₃) T≈Tᵢ) )) (≈-sym r≈rᵢ))  (ctxeq-≈ (⊢≈-sym Γ≈Γ₄) (≈-sym t≈tᵢ)) ) ) (≈-sym Tᵢ≈)

  U⇒A-tm (Λ-I {Γ = Γ′} {S = S′} {T = T′} {i = i′} ⊢Γ′ ⊢S′ ⊢t′)
    with U⇒A-⊢ ⊢Γ′
       | U⇒A-tm ⊢S′
       | U⇒A-tm ⊢t′
  ...  | Γ , ⊢Γ , Γ↝Γ′ , IHΓ
       | _ , Γ₁ , S , _ , Γ↝₁Γ′ , S↝S′ , ↝Se , ⊢S , IHS
       | k , _ , t , T , (↝∷ {T = S₁} Γ↝₂Γ′ S↝₁S′) , t↝t′ , T↝T′ , ⊢t , IHt
    with ⊢∷ ⊢Γ₂ ⊢S₂ ← proj₁ (presup-tm ⊢t)
    with IHΓ Γ↝₁Γ′ (proj₁ (presup-tm ⊢S))
       | IHΓ Γ↝₂Γ′ ⊢Γ₂
  ...  | Γ≈Γ₁ | Γ≈Γ₂
    with Γ₁≈Γ₂ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁
    with IHS S↝₁S′ (ctxeq-tm Γ₁≈Γ₂ ⊢S₂)
  ... | S≈S₂
    with unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₂)))
  ... | refl
    with ⊢T:Se-lvl ⊢S
  ... | refl = _ , _ , _ , _ , Γ↝Γ′ , ↝Λ {i = i′} S↝S′ t↝t′ , ↝Π {i = i′} {j = k} S↝S′ T↝T′ , Λ-I (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S) (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (ctxeq-≈ (⊢≈-sym Γ₁≈Γ₂) (≈-sym S≈S₂) )) ⊢t) refl , helper
    where helper : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
          helper (↝Λ {i = i} S₁↝ t₁↝) ⊢Λt₁
            with Λ-inv′ ⊢Λt₁
          ... | j₁ , T₁ , T₁≈ , i≡maxj₁ , ⊢t₁
            with presup-tm ⊢t₁
          ... | ⊢∷ ⊢Γ ⊢S₁ , _
            with IHS S₁↝ (ctxeq-tm Γ≈Γ₁ ⊢S₁)
          ... | S≈S₁
            with unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
          ... | refl
            with S∷Γ≈S₂∷Γ₂ ← ∷-cong-simp Γ≈Γ₂ (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-trans (≈-sym S≈S₁) S≈S₂))
            with IHt t₁↝ (ctxeq-tm S∷Γ≈S₂∷Γ₂ ⊢t₁)
          ... | t≈t₁ = ≈-conv (≈-sym (Λ-cong ⊢S₁ (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S≈S₁)) (ctxeq-≈ (⊢≈-sym S∷Γ≈S₂∷Γ₂) (≈-sym t≈t₁)) i≡maxj₁)) (≈-sym T₁≈)

  U⇒A-tm (Λ-E {S = S′} {T = T′} {r = r′} {s = s′} ⊢Γ′ ⊢S′ ⊢T′ ⊢r′ ⊢s′)
    with U⇒A-⊢ ⊢Γ′
       | U⇒A-tm ⊢S′
       | U⇒A-tm ⊢T′
       | U⇒A-tm ⊢r′
       | U⇒A-tm ⊢s′
  ...  | Γ , ⊢Γ , Γ↝ , IHΓ
       | _ , Γ₁ , S , _ , Γ↝₁ , S↝S′ , ↝Se , ⊢S , IHS
       | _ , .(S₁ ↙ _) L.∷ Γ₂ , T , .(Se _) , (↝∷ {T = S₁} Γ↝₂ S↝₁S′) , T↝ , ↝Se , ⊢T , IHT
       | k , Γ₃ , r , _ , Γ↝₃ , r↝r′ , ↝Π S↝₂S′ T↝T′ , ⊢r , IHr
       | j , Γ₄ , s , S₂ , Γ↝₄ , s↝s′ , S↝₃S′ , ⊢s , IHs
    with ⊢T:Se-lvl ⊢S
       | ⊢T:Se-lvl ⊢T
  ...  | refl | refl
    with ⊢∷ ⊢Γ₂ ⊢S₁ ← proj₁ (presup-tm ⊢T)
    with IHΓ Γ↝₁ (proj₁ (presup-tm ⊢S))
       | IHΓ Γ↝₂ ⊢Γ₂
       | IHΓ Γ↝₃ (proj₁ (presup-tm ⊢r))
       | IHΓ Γ↝₄ (proj₁ (presup-tm ⊢s))
  ...  | Γ≈Γ₁ | Γ≈Γ₂ | Γ≈Γ₃ | Γ≈Γ₄
    with Γ₁≈Γ₂ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₁) Γ≈Γ₂
       | Γ₁≈Γ₃ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₁) Γ≈Γ₃
    with Π-inv (proj₂ (presup-tm ⊢r))
  ...  | refl , ⊢S₂ , ⊢T₁
    with IHS S↝₁S′ (ctxeq-tm (⊢≈-sym Γ₁≈Γ₂) ⊢S₁)
       | IHS S↝₂S′ (ctxeq-tm (⊢≈-sym Γ₁≈Γ₃) ⊢S₂)
       | IHS S↝₃S′ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₄) Γ≈Γ₁) (proj₂ (presup-tm ⊢s)))
  ...  | S≈S₁ | S≈S₂ | S≈S₃
    with unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
       | unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₂)))
       | unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₃)))
  ...  | refl | refl | refl
    with IHT T↝T′ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₂) (ctxeq-≈ Γ₁≈Γ₃ (≈-trans (≈-sym S≈S₂) S≈S₁) )) ⊢T₁)
  ... | T≈T₁
    with unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
  ... | refl
      = _ , _ , _ , _ , Γ↝ , ↝$ r↝r′ s↝s′ , ↝sub T↝ (↝, ↝I s↝s′) ,
            Λ-E (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S) (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (ctxeq-≈ Γ₁≈Γ₂ (≈-sym S≈S₁) )) ⊢T)
                (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₃) ⊢r) (Π-cong (ctxeq-tm (⊢≈-sym Γ≈Γ₃) ⊢S₂) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S≈S₂)) (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (ctxeq-≈ Γ₁≈Γ₂ (≈-trans (≈-sym S≈S₁) S≈S₂)))  (≈-sym T≈T₁) ) refl))
                (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₄) ⊢s) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S≈S₃) )) refl , helper
    where helper : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
          helper (↝$ r₅↝ s₅↝) ⊢Λrs
            with $-inv ⊢Λrs
          ...  | j , k , S₅ , T₅ , ⊢r₅ , ⊢s₅ , i≡maxjk , ≈T[|s]
            with Π-inv (proj₂ (presup-tm ⊢r₅))
          ...  | _ , ⊢S₅ , ⊢T₅
            with IHr r₅↝ (ctxeq-tm Γ≈Γ₃ ⊢r₅)
               | IHs s₅↝ (ctxeq-tm Γ≈Γ₄ ⊢s₅)
          ...  | r₅≈r | s₅≈s = ≈-conv (≈-sym ($-cong ⊢S₅ ⊢T₅ (ctxeq-≈ (⊢≈-sym Γ≈Γ₃) (≈-sym r₅≈r)) (ctxeq-≈ (⊢≈-sym Γ≈Γ₄) (≈-sym s₅≈s)) i≡maxjk)) (≈-sym ≈T[|s])
  U⇒A-tm (L-I n ⊢t′)
    with U⇒A-tm ⊢t′
  ... | i , Γ , t , T , Γ↝ , t↝ , T↝ , ⊢t , IHt = _ , _ , _ , _ , Γ↝ , ↝liftt t↝ , ↝Liftt T↝ , L-I _ ⊢t , helper 
      where helper : ∀ {tᵢ iᵢ Tᵢ} → tᵢ ↝ _ → Γ A.⊢ tᵢ ∶[ iᵢ ] Tᵢ → Γ ⊢ _ ≈ tᵢ ∶[ iᵢ ] Tᵢ
            helper (↝liftt tᵢ↝) ⊢lifttᵢ 
              with liftt-inv ⊢lifttᵢ  
            ... | jᵢ , Sᵢ , refl , ⊢tᵢ , Tᵢ≈ = ≈-conv (liftt-cong _ (IHt tᵢ↝ ⊢tᵢ))  (≈-sym Tᵢ≈)
  U⇒A-tm (L-E {t = t′} n ⊢Γ′ ⊢T′ ⊢t′) 
    with U⇒A-⊢ ⊢Γ′
        | U⇒A-tm ⊢T′
        | U⇒A-tm ⊢t′
  ... | Γ , ⊢Γ , Γ↝ , IHΓ
      | i , Γ₁ , T , _ , Γ₁↝ , T↝ , ↝Se , ⊢T , IHT
      | j , Γ₂ , t , _ , Γ₂↝ , t↝ , ↝Liftt T₁↝ , ⊢t , IHt
    with ⊢Γ₂ , ⊢LifttT₁ ← presup-tm ⊢t
    with refl , ⊢T₁ ← Liftt-inv ⊢LifttT₁
    with IHΓ Γ₁↝ (proj₁ (presup-tm ⊢T))
       | IHΓ Γ₂↝ ⊢Γ₂
  ...  | Γ≈Γ₁ | Γ≈Γ₂
    with ⊢T:Se-lvl ⊢T
  ...  | refl 
    with Γ₁≈Γ₂ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁
    with IHT T₁↝ (ctxeq-tm Γ₁≈Γ₂ ⊢T₁)
  ...  | T≈T₁
    with unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
  ...  | refl = _ , _ , _ , _ , Γ↝ , ↝unlift t↝ , T↝ , 
                L-E _ (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢T) (ctxeq-tm (⊢≈-sym Γ≈Γ₂) (conv ⊢t (Liftt-cong _ (ctxeq-≈ (⊢≈-sym Γ₁≈Γ₂) (≈-sym T≈T₁)))) ) , helper
      where helper : ∀ {tᵢ iᵢ Tᵢ} → tᵢ ↝ _ → Γ A.⊢ tᵢ ∶[ iᵢ ] Tᵢ → Γ ⊢ _ ≈ tᵢ ∶[ iᵢ ] Tᵢ
            helper (↝unlift tᵢ↝) ⊢unlifttᵢ
              with unlift-inv ⊢unlifttᵢ
            ... | jᵢ , nᵢ , Sᵢ , refl , ⊢tᵢ , Tᵢ≈ 
              with _ , ⊢Tᵢ ← Liftt-inv (proj₂ (presup-tm ⊢tᵢ))
              with IHt tᵢ↝ (ctxeq-tm Γ≈Γ₂ ⊢tᵢ) 
            ... | t≈tᵢ = ≈-conv (unlift-cong _ ⊢Tᵢ (ctxeq-≈ (⊢≈-sym Γ≈Γ₂) t≈tᵢ))  (≈-sym Tᵢ≈)
  U⇒A-tm (t[σ] {Δ = Δ′} {σ = σ′} ⊢Δ′ ⊢t′ ⊢σ′)
    with U⇒A-⊢ ⊢Δ′
       | U⇒A-tm ⊢t′
       | U⇒A-s-⊢ ⊢σ′
  ...  | Δ , ⊢Δ , Δ↝ , IHΔ
       | i , Δ₁ , t , T , Δ↝₁ , t↝ , T↝ , ⊢t , IHt
       | Γ , Δ₂ , σ , Γ↝ , Δ↝₂ , σ↝ , ⊢σ , IHσ
    with IHΔ Δ↝₁ (proj₁ (presup-tm ⊢t))
       | IHΔ Δ↝₂ (proj₂ (presup-s ⊢σ))
  ...  | Δ≈Δ₁ | Δ≈Δ₂
    with Δ₂≈Δ₁ ← ⊢≈-trans (⊢≈-sym Δ≈Δ₂) Δ≈Δ₁
    = _ , _ , _ , _ , Γ↝ , ↝sub t↝ σ↝ , ↝sub T↝ σ↝ , t[σ] ⊢t (s-conv ⊢σ Δ₂≈Δ₁) , helper
    where helper : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
          helper (↝sub t₁↝ σ₁↝) ⊢t₁[σ]
            with t[σ]-inv ⊢t₁[σ]
          ... | Δ₃ , S , ⊢σ₁ , ⊢t₁ , ≈S[σ₁]
            with IHσ σ₁↝ ⊢σ₁
          ... | σ≈σ₁
            with unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σ₁)))
          ... | Δ₂≈Δ₃
            with Δ₃≈Δ₁ ← ⊢≈-trans (⊢≈-sym Δ₂≈Δ₃) Δ₂≈Δ₁ = ≈-conv (≈-sym ([]-cong (≈-sym (IHt t₁↝ (ctxeq-tm Δ₃≈Δ₁ ⊢t₁))) (s-≈-sym (IHσ σ₁↝ (s-conv ⊢σ₁ Δ₃≈Δ₁)) ))) (≈-sym ≈S[σ₁])
  U⇒A-tm (conv {S = S′} ⊢Γ′ ⊢t′ ⊢S′ S′≈T′)
    with U⇒A-⊢ ⊢Γ′
       | U⇒A-tm ⊢t′
       | U⇒A-tm ⊢S′
       | U⇒A-≈ S′≈T′
  ...  | Γ , ⊢Γ , Γ↝ , IHΓ
       | i , Γ₁ , t , S , Γ↝₁ , t↝ , S↝ , ⊢t , IHt
       | j , Γ₂ , S₁ , _ , Γ↝₂ , S↝₁ , ↝Se , ⊢S , IHS
       | _ , Γ₃ , S₂ , T , _ , Γ↝₃ , S↝₂ , T↝ , ↝Se , T≈S
    with IHΓ Γ↝₁ (proj₁ (presup-tm ⊢t))
       | IHΓ Γ↝₂ (proj₁ (presup-tm ⊢S))
       | IHΓ Γ↝₃ (proj₁ (presup-≈ T≈S))
  ...  | Γ≈Γ₁ | Γ≈Γ₂ | Γ≈Γ₃
    with Γ₁≈Γ₂ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₁) Γ≈Γ₂
       | Γ₁≈Γ₃ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₁) Γ≈Γ₃
       | Γ₃≈Γ₂ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₂
    with ⊢T:Se-lvl (proj₁ (proj₂ (presup-≈ T≈S)))
  ...  | refl
    with IHS S↝₂ (proj₁ (proj₂ (presup-≈ (ctxeq-≈ Γ₃≈Γ₂ T≈S) )))
       | IHS S↝ (proj₂ (presup-tm (ctxeq-tm Γ₁≈Γ₂ ⊢t) ))
  ...  | S₁≈S₂ | S₁≈S
    with unique-lvl (proj₁ (proj₂ (presup-≈ S₁≈S₂)))  (proj₁ (proj₂ (presup-≈ S₁≈S)))
  ...  | refl
       = _ , _ , _ , _ , Γ↝₁ , t↝ , T↝ , conv ⊢t (≈-trans (ctxeq-≈ (⊢≈-sym Γ₁≈Γ₂) (≈-trans (≈-sym S₁≈S) S₁≈S₂)) (ctxeq-≈ (⊢≈-sym Γ₁≈Γ₃) T≈S) ), IHt

  U⇒A-s-⊢ : U.Γ′ U.⊢s U.σ′ ∶ U.Δ′ →
          ------------------
          ∃₂ λ Γ Δ → ∃ λ σ → (Γ [↝] U.Γ′) × (Δ [↝] U.Δ′) × (σ ↝s U.σ′) × Γ A.⊢s σ ∶ Δ ×
            (∀ {σ₁ Δ₁} →
                σ₁ ↝s U.σ′ →
                Γ A.⊢s σ₁ ∶ Δ₁ →
                Γ A.⊢s σ ≈ σ₁ ∶ Δ₁)
  U⇒A-s-⊢ (s-I ⊢Γ′)
    with U⇒A-⊢ ⊢Γ′
  ... | Γ , ⊢Γ , Γ↝ , IHΓ = _ , _ , _ , Γ↝ , Γ↝ , ↝I , s-I ⊢Γ , λ { ↝I ⊢σ₁ → s-≈-refl ⊢σ₁ }
  U⇒A-s-⊢ (s-wk ⊢T∷Γ′)
    with U⇒A-⊢ ⊢T∷Γ′
  ... | .((_ ↙ _) L.∷ _) , ⊢∷ ⊢Γ ⊢T , ↝∷ Γ↝ T↝ , IHΓ = _ , _ , _ , ↝∷ Γ↝ T↝ , Γ↝ , ↝wk , s-wk (⊢∷ ⊢Γ ⊢T) , λ { ↝wk ⊢σ₁ → s-≈-refl ⊢σ₁ }
  U⇒A-s-⊢ (s-∘ ⊢σ′ ⊢σ′₁) = {!   !}
  U⇒A-s-⊢ (s-, {Γ = Γ′} {Δ = Δ′} {T = T′} {t = t′} ⊢σ′ ⊢T′ ⊢t′)
    with U⇒A-s-⊢ ⊢σ′
       | U⇒A-tm ⊢T′
       | U⇒A-tm ⊢t′
  ...  | Γ , Δ , σ , Γ↝ , Δ↝ , σ↝ , ⊢σ , IHσ
       | 1+i , Δ₁ , T , _ , Δ₁↝ , T↝ , ↝Se , ⊢T , IHT
       | i , Γ₁ , t , _ , Γ₁↝ , t↝ , (↝sub {T₁} T↝₁ σ↝₁) , ⊢t , IHt =
        {!   !} , {!   !} , {!   !} , Γ↝ , {!   !} , ↝, {!   !} t↝ , s-, {!   !} {!   !} {!   !} , {!   !}
  U⇒A-s-⊢ (s-conv ⊢σ′ x) = {!   !}

  U⇒A-≈ : U.Γ′ U.⊢ U.t′ ≈ U.s′ ∶ U.T′ →
          ------------------
          ∃₂ λ i Γ → ∃₂ λ t s → ∃ λ T → (Γ [↝] U.Γ′) × (t ↝ U.t′) × (s ↝ U.s′) × (T ↝ U.T′) × Γ A.⊢ t ≈ s ∶[ i ] T
  U⇒A-≈ (N-[] ⊢σ′) with U⇒A-s-⊢ ⊢σ′
  ... | Γ , Δ , σ , Γ↝ , Δ↝ , σ↝ , ⊢σ , IHσ = _ , _ , _ , _ , _ , Γ↝ , ↝sub ↝N σ↝ , ↝N , ↝Se , N-[] ⊢σ
  U⇒A-≈ (Se-[] i ⊢σ′) with U⇒A-s-⊢ ⊢σ′
  ... | Γ , Δ , σ , Γ↝ , Δ↝ , σ↝ , ⊢σ , IHσ = _ , _ , _ , _ , _ , Γ↝ , ↝sub ↝Se σ↝ , ↝Se , ↝Se , Se-[] _ ⊢σ
  U⇒A-≈ (Liftt-[] n x x₁) = {!   !}
  U⇒A-≈ (Π-[] x x₁ x₂ x₃) = {!   !}
  U⇒A-≈ (Π-cong x t≈s t≈s₁ x₁) = {!   !}
  U⇒A-≈ (Liftt-cong n t≈s) = {!   !}
  U⇒A-≈ (v-≈ x x₁) = {!   !}
  U⇒A-≈ (ze-≈ x) = {!   !}
  U⇒A-≈ (su-cong t′≈s′) with U⇒A-≈ t′≈s′
  ... | i , Γ , t , s , T , Γ↝ , t↝ , s↝ , ↝N , t≈s = _ , _ , _ , _ , _ , Γ↝ , ↝su t↝ , ↝su s↝ , ↝N , su-cong {!   !}
  U⇒A-≈ (rec-cong x t≈s t≈s₁ t≈s₂ t≈s₃) = {!   !}
  U⇒A-≈ (Λ-cong ⊢Γ′ x t≈s t≈s₁) = {!   !}
  U⇒A-≈ ($-cong x x₁ t≈s t≈s₁) = {!   !}
  U⇒A-≈ (liftt-cong n t≈s) = {!   !}
  U⇒A-≈ (unlift-cong n x t≈s) = {!   !}
  U⇒A-≈ ([]-cong t≈s x) = {!   !}
  U⇒A-≈ (ze-[] x) = {!   !}
  U⇒A-≈ (su-[] x x₁) = {!   !}
  U⇒A-≈ (rec-[] x x₁ x₂ x₃ x₄) = {!   !}
  U⇒A-≈ (Λ-[] x x₁ x₂) = {!   !}
  U⇒A-≈ ($-[] x x₁ x₂ x₃ x₄) = {!   !}
  U⇒A-≈ (liftt-[] n x x₁ x₂) = {!   !}
  U⇒A-≈ (unlift-[] n x x₁ x₂) = {!   !}
  U⇒A-≈ (rec-β-ze x x₁ x₂) = {!   !}
  U⇒A-≈ (rec-β-su x x₁ x₂ x₃) = {!   !}
  U⇒A-≈ (Λ-β x x₁ x₂ x₃) = {!   !}
  U⇒A-≈ (Λ-η x x₁ x₂) = {!   !}
  U⇒A-≈ (L-β n x) = {!   !}
  U⇒A-≈ (L-η n x x₁) = {!   !}
  U⇒A-≈ ([I] ⊢s′) = {!   !}
  U⇒A-≈ ([wk] x x₁) = {!   !}
  U⇒A-≈ ([∘] x x₁ x₂) = {!   !}
  U⇒A-≈ ([,]-v-ze x x₁ x₂) = {!   !}
  U⇒A-≈ ([,]-v-su x x₁ x₂ x₃) = {!   !}
  U⇒A-≈ (≈-conv t≈s t≈s₁) = {!   !}
  U⇒A-≈ (≈-sym t≈s) = {!   !}
  U⇒A-≈ (≈-trans t≈s t≈s₁) = {!   !}

  U⇒A-s-≈ : U.Γ′ U.⊢s U.σ′ ≈ U.τ′ ∶ U.Δ′ →
          ------------------
          ∃₂ λ Γ Δ → ∃₂ λ σ τ → (Γ [↝] U.Γ′) × (Δ [↝] U.Δ′) × (σ ↝s U.σ′) × (τ ↝s U.τ′) × Γ A.⊢s σ ≈ τ ∶ Δ
  U⇒A-s-≈ σ′≈τ′ = {!   !}

  U⇒A-⊢≈ : U.⊢ U.Γ′ ≈ U.Δ′ →
          ------------------
          ∃₂ λ Γ Δ → (Γ [↝] U.Γ′) × (Δ [↝] U.Δ′) × A.⊢ Γ ≈ Δ
  U⇒A-⊢≈ []-≈ = {!   !}
  U⇒A-⊢≈ (∷-cong Γ′≈Δ′ x x₁ x₂ x₃) = {!   !}    