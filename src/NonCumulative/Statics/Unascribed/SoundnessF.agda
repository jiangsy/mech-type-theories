
{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

module NonCumulative.Statics.Unascribed.SoundnessF  (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂)  where

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
  U⇒A-⊢ (⊢∷ ⊢Γ′ ⊢T′) = {!   !} -- done

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
  U⇒A-tm (N-wf ⊢Γ′) = {!   !} -- done
  U⇒A-tm (Se-wf i ⊢Γ′) = {!   !} -- done
  U⇒A-tm (Liftt-wf n ⊢T′)
    with U⇒A-tm ⊢T′
  ... | _ , Γ , T , .(Se _) , Γ↝ , T↝ , ↝Se , ⊢T , IHT
    with ⊢T:Se-lvl ⊢T
  ... | refl = _ , _ , _ , _ , Γ↝ , ↝Liftt T↝ , ↝Se , Liftt-wf _ ⊢T , helper
    where helper : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
          helper (↝Liftt t₁↝) ⊢Liftt₁ 
            with Liftt-inv′ ⊢Liftt₁ 
          ... | refl , ⊢Tᵢ , ≈Se 
            with IHT t₁↝ ⊢Tᵢ
          ... | T≈Tᵢ 
            with unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈Tᵢ)))
          ... | refl = ≈-conv (Liftt-cong _ T≈Tᵢ) (≈-sym ≈Se)
  U⇒A-tm (Π-wf {Γ = Γ′} {S = S′} {T = T′} ⊢Γ′ ⊢S′ ⊢T′ k≡maxij) = {!   !} -- done
  U⇒A-tm (vlookup ⊢Γ′ x∈Γ') = {!   !} -- done
  U⇒A-tm (ze-I ⊢Γ′) = {!   !} -- done
  U⇒A-tm (su-I {t = t′} ⊢t′) = {!   !} -- done
  U⇒A-tm (N-E {T = T′} {s = s′} {r = r′} {t = t′} ⊢Γ′ ⊢T′ ⊢s′ ⊢r′ ⊢t′) = {!   !} -- done 
  U⇒A-tm (Λ-I {Γ = Γ′} {S = S′} {T = T′} {i = i′} ⊢Γ′ ⊢S′ ⊢t′) = {!   !} -- done
  U⇒A-tm (Λ-E {S = S′} {T = T′} {r = r′} {s = s′} ⊢Γ′ ⊢S′ ⊢T′ ⊢r′ ⊢s′) = {!   !} -- done
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
  ... | Γ≈Γ₁ | Γ≈Γ₂
    with ⊢T:Se-lvl ⊢T
  ... | refl 
    with Γ₁≈Γ₂ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁
    with IHT T₁↝ (ctxeq-tm Γ₁≈Γ₂ ⊢T₁)
  ... | T≈T₁
    with unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
  ... | refl = _ , _ , _ , _ , Γ↝ , ↝unlift t↝ , T↝ , 
               L-E _ (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢T) (ctxeq-tm (⊢≈-sym Γ≈Γ₂) (conv ⊢t (Liftt-cong _ (ctxeq-≈ (⊢≈-sym Γ₁≈Γ₂) (≈-sym T≈T₁)))) ) , helper
     where helper : ∀ {tᵢ iᵢ Tᵢ} → tᵢ ↝ _ → Γ A.⊢ tᵢ ∶[ iᵢ ] Tᵢ → Γ ⊢ _ ≈ tᵢ ∶[ iᵢ ] Tᵢ
           helper (↝unlift tᵢ↝) ⊢unlifttᵢ
            with unlift-inv ⊢unlifttᵢ
           ... | jᵢ , nᵢ , Sᵢ , refl , ⊢tᵢ , Tᵢ≈ 
            with _ , ⊢Tᵢ ← Liftt-inv (proj₂ (presup-tm ⊢tᵢ))
            with IHt tᵢ↝ (ctxeq-tm Γ≈Γ₂ ⊢tᵢ) 
           ... | t≈tᵢ = ≈-conv (unlift-cong _ ⊢Tᵢ (ctxeq-≈ (⊢≈-sym Γ≈Γ₂) t≈tᵢ))  (≈-sym Tᵢ≈)
  U⇒A-tm (t[σ] {Δ = Δ′} {σ = σ′} ⊢Δ′ ⊢t′ ⊢σ′) = {!   !} -- done
  U⇒A-tm (conv {S = S′} ⊢Γ′ ⊢t′ ⊢S′ S′≈T′) = {!   !} -- done

  U⇒A-s-⊢ : U.Γ′ U.⊢s U.σ′ ∶ U.Δ′ →
           ------------------
           ∃₂ λ Γ Δ → ∃ λ σ → (Γ [↝] U.Γ′) × (Δ [↝] U.Δ′) × (σ ↝s U.σ′) × Γ A.⊢s σ ∶ Δ ×
            (∀ {σ₁ Δ₁} →
                σ₁ ↝s U.σ′ →
                Γ A.⊢s σ₁ ∶ Δ₁ →
                Γ A.⊢s σ ≈ σ₁ ∶ Δ₁)
  U⇒A-s-⊢ (s-I ⊢Γ′) = {!   !} -- done
  U⇒A-s-⊢ (s-wk ⊢T∷Γ′) = {!   !} -- done
  U⇒A-s-⊢ (s-∘ ⊢σ′ ⊢σ′₁) = {!   !}
  U⇒A-s-⊢ (s-, {Γ = Γ′} {Δ = Δ′} {T = T′} {t = t′} ⊢σ′ ⊢T′ ⊢t′)
    with U⇒A-s-⊢ ⊢σ′
       | U⇒A-tm ⊢T′
       | U⇒A-tm ⊢t′
  ... | Γ , Δ , σ , Γ↝ , Δ↝ , σ↝ , ⊢σ , IHσ
      | 1+i , Δ₁ , T , _ , Δ₁↝ , T↝ , ↝Se , ⊢T , IHT
      | i , Γ₁ , t , _ , Γ₁↝ , t↝ , (↝sub {T₁} T↝₁ σ↝₁) , ⊢t , IHt =
        {!   !} , {!   !} , {!   !} , Γ↝ , {!   !} , ↝, {!   !} t↝ , s-, {!   !} {!   !} {!   !} , {!   !}
  U⇒A-s-⊢ (s-conv ⊢σ′ x) = {!   !}

  U⇒A-≈ : U.Γ′ U.⊢ U.t′ ≈ U.s′ ∶ U.T′ →
          ------------------
          ∃₂ λ i Γ → ∃₂ λ t s → ∃ λ T → (Γ [↝] U.Γ′) × (t ↝ U.t′) × (s ↝ U.s′) × (T ↝ U.T′) × Γ A.⊢ t ≈ s ∶[ i ] T
  U⇒A-≈ (N-[] ⊢σ′) = {!   !} -- done
  U⇒A-≈ (Se-[] i ⊢σ′) = {!   !} -- done
  U⇒A-≈ (Liftt-[] n x x₁) = {!   !}
  U⇒A-≈ (Π-[] x x₁ x₂ x₃) = {!   !}
  U⇒A-≈ (Π-cong x t≈s t≈s₁ x₁) = {!   !}
  U⇒A-≈ (Liftt-cong n t≈s) = {!   !}
  U⇒A-≈ (v-≈ x x₁) = {!   !}
  U⇒A-≈ (ze-≈ x) = {!   !}
  U⇒A-≈ (su-cong t′≈s′) with U⇒A-≈ t′≈s′
  ... | i , Γ , t , s , T , Γ↝ , t↝ , s↝ , ↝N , t≈s = _ , _ , _ , _ , _ , Γ↝ , ↝su t↝ , ↝su s↝ , ↝N , su-cong {!   !} 
  U⇒A-≈ (rec-cong x t≈s t≈s₁ t≈s₂ t≈s₃) = {!   !}
  U⇒A-≈ (Λ-cong {S = S′} {S′ = T′} ⊢Γ′ ⊢S′ S′≈T′ t≈t′) 
    with U⇒A-tm ⊢S′
       | U⇒A-≈ S′≈T′
       | U⇒A-≈ t≈t′
  ... | 1+i , Γ , _ , S , Γ↝ , _ , S↝ , ⊢S , IHS
      | i+i₁ , Γ₁ , S₁ , T , _ , Γ₁↝ , S↝₁ , T↝ , ↝Se , T≈S 
      | i , Γ₂ , s , t , _ , ↝∷ Γ₂↝ S↝₂ , s↝ , t↝ , T↝₁ , t≈s = {!   !} , {!   !} , {!   !} , {!   !} , {!   !} , {!   !} , ↝Λ S↝₁ s↝ , ↝Λ T↝ t↝ , ↝Π {!   !} {!   !} , (Λ-cong {!   !} {!   !} {!   !} {!   !})
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