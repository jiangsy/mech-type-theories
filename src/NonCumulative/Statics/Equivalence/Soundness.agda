
{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

module NonCumulative.Statics.Equivalence.Soundness (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂)  where

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
open import NonCumulative.Statics.Equivalence.Transfer

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

infix 4 ⫢_ ⫢_≈_ _⫢_∶_ _⫢s_∶_ _⫢_≈_∶_ _⫢s_≈_∶_

⫢_ : U.Ctx → Set
⫢ Γ′ = ∃ λ Γ → (A.⊢ Γ × Γ [↝] Γ′ × (∀ {Γᵢ} → Γᵢ [↝] Γ′ → A.⊢ Γᵢ → A.⊢ Γ ≈ Γᵢ))

_⫢_∶_ : U.Ctx → U.Exp → U.Typ → Set
Γ′ ⫢ t′ ∶ T′ =  ∃₂ λ i Γ → ∃₂ λ t T →
                  (Γ [↝] Γ′) ×
                  (t ↝ t′) ×
                  (T ↝ T′) ×
                  Γ A.⊢ t ∶[ i ] T ×
                  (∀ {Γᵢ} → Γᵢ [↝] Γ′ → A.⊢ Γᵢ → A.⊢ Γ ≈ Γᵢ) ×
                  (∀ {tᵢ iᵢ Tᵢ} →
                      tᵢ ↝ t′ →
                      Γ ⊢ tᵢ ∶[ iᵢ ] Tᵢ →
                      Γ A.⊢ t ≈ tᵢ ∶[ iᵢ ] Tᵢ)

_⫢s_∶_ : U.Ctx → U.Subst → U.Ctx → Set
Γ′ ⫢s σ′ ∶ Δ′ = 
  ∃₂ λ Γ Δ → ∃ λ σ → (Γ [↝] Γ′) × (Δ [↝] Δ′) × (σ ↝s σ′) × Γ A.⊢s σ ∶ Δ ×
     (∀ {Γᵢ} → Γᵢ [↝] Γ′ → A.⊢ Γᵢ → A.⊢ Γ ≈ Γᵢ) ×
     (∀ {σᵢ Δᵢ} → σᵢ ↝s σ′ → Γ A.⊢s σᵢ ∶ Δᵢ → Γ A.⊢s σ ≈ σᵢ ∶ Δᵢ)

⫢_≈_ : U.Ctx → U.Ctx → Set
⫢ Γ′ ≈ Δ′ = ∃₂ λ Γ Δ → (Γ [↝] Γ′) × (Δ [↝] Δ′) × A.⊢ Γ ≈ Δ × 
               (∀ {Γᵢ} → Γᵢ [↝] Γ′ → A.⊢ Γᵢ → A.⊢ Γ ≈ Γᵢ) × 
               (∀ {Δᵢ} → Δᵢ [↝] Δ′ → A.⊢ Δᵢ → A.⊢ Δ ≈ Δᵢ)

_⫢_≈_∶_ : U.Ctx → U.Exp → U.Exp → U.Typ → Set
Γ′ ⫢ t′ ≈ s′ ∶ T′ = 
  ∃₂ λ i Γ → ∃₂ λ t s → ∃ λ T → (Γ [↝] Γ′) × (t ↝ t′) × (s ↝ s′) × (T ↝ T′) × Γ A.⊢ t ≈ s ∶[ i ] T × 
     (∀ {Γᵢ} → Γᵢ [↝] Γ′ → A.⊢ Γᵢ → A.⊢ Γ ≈ Γᵢ) × 
     (∀ {tᵢ iᵢ Tᵢ} →
      tᵢ ↝ t′ →
      Γ ⊢ tᵢ ∶[ iᵢ ] Tᵢ →
      Γ A.⊢ t ≈ tᵢ ∶[ iᵢ ] Tᵢ) × 
     (∀ {sᵢ iᵢ Tᵢ} →
      sᵢ ↝ s′ →
      Γ ⊢ sᵢ ∶[ iᵢ ] Tᵢ →
      Γ A.⊢ s ≈ sᵢ ∶[ iᵢ ] Tᵢ)

_⫢s_≈_∶_ : U.Ctx → U.Subst → U.Subst → U.Ctx → Set
Γ′ ⫢s σ′ ≈ τ′ ∶ Δ′ = ∃₂ λ Γ Δ → ∃₂ λ σ τ → (Γ [↝] Γ′) × (Δ [↝] Δ′) × (σ ↝s σ′) × (τ ↝s τ′) × Γ A.⊢s σ ≈ τ ∶ Δ × 
  (∀ {Γᵢ} → Γᵢ [↝] Γ′ → A.⊢ Γᵢ → A.⊢ Γ ≈ Γᵢ) × 
  (∀ {σᵢ Δᵢ} → σᵢ ↝s σ′ → Γ A.⊢s σᵢ ∶ Δᵢ → Γ A.⊢s σ ≈ σᵢ ∶ Δᵢ) × 
  (∀ {τᵢ Δᵢ} → τᵢ ↝s τ′ → Γ A.⊢s τᵢ ∶ Δᵢ → Γ A.⊢s τ ≈ τᵢ ∶ Δᵢ)

⫢⊢[] : ⫢ []
⫢⊢[] = _ , ⊢[] , ↝[] , λ { ↝[] ⊢[] → []-≈ }

⫢[]-≈ : ⫢ [] ≈ []
⫢[]-≈ = _ , _ , ↝[] , ↝[] , []-≈ , (λ { ↝[] ⊢[] → []-≈ }) , (λ { ↝[] ⊢[] → []-≈ })

⫢⊢∷ : ∀ {i} →
      ⫢ U.Γ′ →
      U.Γ′ ⫢ U.T′ ∶ Se i →
      --------------------
      ⫢ U.T′ ∷ U.Γ′
⫢⊢∷  {Γ′} ⫢Γ′ ⫢T′
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
     | i , Γ₁ , T , .(Se _) , Γ₁↝ , T↝ , ↝Se , ⊢T , _ , IHT ← ⫢T′
  with refl ← ⊢T:Se-lvl ⊢T
  with Γ≈Γ₁  ← IHΓ Γ₁↝ (proj₁ (presup-tm ⊢T)) = _ , ⊢∷ ⊢Γ (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢T) , ↝∷ Γ↝ T↝ , helper
    where
      helper : ∀ { Γᵢ } → Γᵢ [↝] _ → A.⊢ Γᵢ → A.⊢ _ ≈ Γᵢ
      helper (↝∷ {T = Tᵢ} ↝Γᵢ ↝Tᵢ) (⊢∷ ⊢Γᵢ ⊢Tᵢ)
        with Γ≈Γᵢ ← IHΓ ↝Γᵢ ⊢Γᵢ
        with T≈Tᵢ ← IHT ↝Tᵢ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γᵢ) Γ≈Γ₁) ⊢Tᵢ)
        with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈Tᵢ))) = ∷-cong-simp Γ≈Γᵢ (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) T≈Tᵢ)

⫢∷-cong : ∀ {i} →
          ⫢ U.Γ′ ≈ U.Δ′ →
          U.Γ′ ⫢ U.T′ ∶ Se i →
          U.Δ′ ⫢ U.S′ ∶ Se i →
          U.Γ′ ⫢ U.T′ ≈ U.S′ ∶ Se i →
          U.Δ′ ⫢ U.T′ ≈ U.S′ ∶ Se i →
          --------------------
          ⫢ U.T′ ∷ U.Γ′ ≈ U.S′ ∷ U.Δ′
⫢∷-cong Γ′≈Δ′ ⫢T′ ⫢S′ Γ⫢T≈S′ Δ⫢T≈S′
  with Γ , Δ , Γ↝ , Δ↝ , Γ≈Δ , IHΓ , IHΔ ← Γ′≈Δ′
     | _ , Γ₁ , T , _ , Γ₁↝ , T↝ , ↝Se , ⊢T , _ , IHT ← ⫢T′
     | _ , Δ₁ , S , _ , Δ₁↝ , S↝ , ↝Se , ⊢S , _ , IHS ← ⫢S′
     | _ , Γ₂ , T₁ , S₁ , _ , Γ₂↝ , T↝₁ , S↝₁ , ↝Se , T₁≈S₁ , _ ← Γ⫢T≈S′ 
  with refl ← ⊢T:Se-lvl ⊢T
  with refl ← ⊢T:Se-lvl ⊢S
  with ⊢Γ₂ , ⊢T₁ , ⊢S₁ , _  ← presup-≈ T₁≈S₁
  with ⊢Γ , ⊢Δ ← presup-⊢≈ Γ≈Δ 
  with refl ← ⊢T:Se-lvl ⊢T₁ 
  with Γ≈Γ₁ ← IHΓ Γ₁↝ (proj₁ (presup-tm ⊢T))
     | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
     | Δ≈Δ₁ ← IHΔ Δ₁↝ (proj₁ (presup-tm ⊢S)) 
  with T≈T₁ ← IHT T↝₁ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₂)  Γ≈Γ₁) ⊢T₁)
     | S≈S₁ ← IHS S↝₁ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₂) (⊢≈-trans Γ≈Δ Δ≈Δ₁)) ⊢S₁) 
  = _ , _ , ↝∷ Γ↝ T↝ , ↝∷ Δ↝ S↝ , ∷-cong-simp Γ≈Δ ((≈-trans (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) T≈T₁) (≈-trans (ctxeq-≈ (⊢≈-sym Γ≈Γ₂) T₁≈S₁) (ctxeq-≈ (⊢≈-trans (⊢≈-sym Δ≈Δ₁) (⊢≈-sym Γ≈Δ)) (≈-sym S≈S₁))))) , IHT∷Γ , IHS∷Δ
  where 
    IHT∷Γ : ∀ { Γᵢ } → Γᵢ [↝] _ → A.⊢ Γᵢ → A.⊢ _ ≈ Γᵢ
    IHT∷Γ (↝∷ {T = Tᵢ} ↝Γᵢ ↝Tᵢ) (⊢∷ ⊢Γᵢ ⊢Tᵢ)
      with Γ≈Γᵢ ← IHΓ ↝Γᵢ ⊢Γᵢ
      with T≈Tᵢ ← IHT ↝Tᵢ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γᵢ) Γ≈Γ₁) ⊢Tᵢ) 
      with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈Tᵢ))) = ∷-cong-simp Γ≈Γᵢ (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) T≈Tᵢ)

    IHS∷Δ : ∀ { Δᵢ } → Δᵢ [↝] _ → A.⊢ Δᵢ → A.⊢ _ ≈ Δᵢ
    IHS∷Δ (↝∷ {T = Sᵢ} ↝Δᵢ ↝Sᵢ) (⊢∷ ⊢Δᵢ ⊢Sᵢ) 
      with Δ≈Δᵢ ← IHΔ ↝Δᵢ ⊢Δᵢ 
      with S≈Sᵢ ← IHS ↝Sᵢ (ctxeq-tm (⊢≈-trans (⊢≈-sym Δ≈Δᵢ) Δ≈Δ₁) ⊢Sᵢ) 
      with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈Sᵢ))) = ∷-cong-simp Δ≈Δᵢ (ctxeq-≈ (⊢≈-sym Δ≈Δ₁) S≈Sᵢ)

-- ⫢N-wf : ⫢ U.Γ′ →
--         U.Γ′ ⫢ N ∶ Se 0
-- ⫢N-wf ⫢Γ′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′ = _ , _ , _ , _ , Γ↝ , ↝N , ↝Se , N-wf ⊢Γ , IHΓ , λ { ↝N ⊢N → ≈-refl ⊢N }

-- ⫢Se-wf : ∀ {i} →
--          ⫢ U.Γ′ →
--          U.Γ′ ⫢ Se i ∶ Se (1 + i)
-- ⫢Se-wf ⫢Γ′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′ = _ , _ , _ , _ , Γ↝ , ↝Se , ↝Se , Se-wf _ ⊢Γ , IHΓ , λ { ↝Se ⊢Se → ≈-refl ⊢Se }

-- ⫢Liftt-wf : ∀ {i n} →
--             U.Γ′ ⫢ U.T′ ∶ Se i →
--             U.Γ′ ⫢ Liftt n U.T′ ∶ Se (n + i)
-- ⫢Liftt-wf ⫢T′
--   with _ , Γ , T , .(Se _) , Γ↝ , T↝ , ↝Se , ⊢T , IHΓ , IHT ← ⫢T′
--   with refl ← ⊢T:Se-lvl ⊢T = _ , _ , _ , _ , Γ↝ , ↝Liftt T↝ , ↝Se , Liftt-wf _ ⊢T , IHΓ , IHLiftT
--     where
--       IHLiftT : ∀ {tᵢ iᵢ Tᵢ} → tᵢ ↝ _ → Γ A.⊢ tᵢ ∶[ iᵢ ] Tᵢ → Γ ⊢ _ ≈ tᵢ ∶[ iᵢ ] Tᵢ
--       IHLiftT (↝Liftt tᵢ↝) ⊢Lifttᵢ
--         with Liftt-inv′ ⊢Lifttᵢ
--       ... | refl , ⊢Tᵢ , ≈Se
--         with IHT tᵢ↝ ⊢Tᵢ
--       ... | T≈Tᵢ
--         with unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈Tᵢ)))
--       ... | refl = ≈-conv (Liftt-cong _ T≈Tᵢ) (≈-sym ≈Se)

-- ⫢Π-wf : ∀ {i j k} →
--         U.Γ′ ⫢ U.S′ ∶ Se i →
--         (U.S′ ∷ U.Γ′) ⫢ U.T′ ∶ Se j →
--         k ≡ max i j →
--         --------------------
--         U.Γ′ ⫢ Π U.S′ U.T′ ∶ Se k
-- ⫢Π-wf ⫢S′ ⫢T′ k≡maxij
--   with _ , Γ , S , _ , Γ↝ , S↝ , ↝Se , ⊢S , IHΓ , IHS ← ⫢S′
--      | _ , _ , T , .(Se _) , (↝∷ {T = S₁} Γ↝₁ S↝₁) , T↝ , ↝Se , ⊢T , _ , IHT ← ⫢T′ 
--   with refl ← ⊢T:Se-lvl ⊢S
--      | refl ← ⊢T:Se-lvl ⊢T 
--   with ⊢∷ ⊢Γ₁ ⊢S₁ ← proj₁ (presup-tm ⊢T) 
--   with Γ≈Γ₁ ← IHΓ Γ↝₁ ⊢Γ₁
--   with S≈S₁ ← IHS S↝₁ (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S₁)
--   with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁))) 
--   = _ , _ , _ , _ , Γ↝ , ↝Π S↝ T↝ , ↝Se , Π-wf ⊢S (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (ctxeq-≈ Γ≈Γ₁ (≈-sym S≈S₁))) ⊢T) k≡maxij , IHΓ , IHΠST
--   where
--     IHΠST : ∀ {tᵢ iᵢ Tᵢ} → tᵢ ↝ _ → Γ A.⊢ tᵢ ∶[ iᵢ ] Tᵢ → Γ ⊢ _ ≈ tᵢ ∶[ iᵢ ] Tᵢ
--     IHΠST (↝Π Sᵢ↝ Tᵢ↝) ⊢Πtᵢ
--       with refl , ≈Se , ⊢Sᵢ , ⊢Tᵢ ← Π-inv′ ⊢Πtᵢ
--       with S≈Sᵢ ← IHS Sᵢ↝ ⊢Sᵢ 
--       with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈Sᵢ))) 
--       with Sᵢ≈S₁ ← ≈-trans (≈-sym S≈Sᵢ) S≈S₁ 
--       with T≈Tᵢ ← IHT Tᵢ↝ (ctxeq-tm (∷-cong-simp Γ≈Γ₁ Sᵢ≈S₁) ⊢Tᵢ) 
--       with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈Tᵢ))) = ≈-conv (Π-cong ⊢S S≈Sᵢ (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (ctxeq-≈ Γ≈Γ₁ (≈-sym S≈S₁))) T≈Tᵢ) refl) (≈-sym ≈Se)

-- ⫢vlookup : ∀ {x} →
--            ⫢ U.Γ′ →
--            x ∶ U.T′ ∈! U.Γ′ →
--            ------------
--            U.Γ′ ⫢ v x ∶ U.T′
-- ⫢vlookup ⫢Γ′ x∈Γ′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--   with  _ , _ , T↝ , x∈Γ ← U⇒A-vlookup Γ↝ x∈Γ′ = _ , _ , _ , _ , Γ↝ , ↝v , T↝ , vlookup ⊢Γ x∈Γ , IHΓ , λ { ↝v ⊢v → ≈-refl ⊢v }

-- ⫢ze-I : ⫢ U.Γ′ →
--         ------------------
--         U.Γ′ ⫢ ze ∶ N
-- ⫢ze-I ⫢Γ′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′ = _ , _ , _ , _ , Γ↝ , ↝ze , ↝N , ze-I ⊢Γ , IHΓ , λ { ↝ze ⊢ze → ≈-refl ⊢ze }

-- ⫢su-I : U.Γ′ ⫢ U.t′ ∶ N →
--         U.Γ′ ⫢ su U.t′ ∶ N
-- ⫢su-I ⫢t′
--   with _ , Γ , t , .N , Γ↝ , t↝ , ↝N , ⊢t , IHΓ , IHt ← ⫢t′
--   with  ⊢t∶N-lvl ⊢t
-- ...  | refl = _ , _ , _ , _ , Γ↝ , ↝su t↝ , ↝N , (su-I ⊢t) , IHΓ , IHsu
--   where
--     IHsu : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
--     IHsu (↝su t₁↝) ⊢sut₁
--       with su-inv ⊢sut₁
--     ...  | refl , T₁≈N , ⊢t₁ = ≈-conv (su-cong (IHt t₁↝ ⊢t₁)) (≈-sym T₁≈N)

T[I,ze]-inv : ∀ {i j} →
              A.Γ A.⊢ sub A.T (I , ze ∶ N ↙ j) ∶[ 1 + i ] Se i →
              ∃ λ S → j ≡ 0 × N₀ ∷ A.Γ ⊢ A.T ∶[ 1 + i ] S
T[I,ze]-inv ⊢T[|ze]
  with t[σ]-inv ⊢T[|ze]
... | Δ , S , ⊢[|ze] , ⊢T , ≈Sei
  with ⊢ze , ≈Δ ← ,-inv′ ⊢[|ze] (s-I (proj₁ (presup-tm ⊢T[|ze])))
  with refl , ≈N ← ze-inv ⊢ze = _ , refl , ctxeq-tm (⊢≈-sym ≈Δ) ⊢T

T[wkwk,suv1]-inv : ∀ {i j} →
                   A.lS ∷ A.lT ∷ A.Γ A.⊢ sub A.T ((wk ∘ wk) , su (v 1) ∶ N ↙ j) ∶[ 1 + i ] Se i →
                   ∃ λ S → j ≡ 0 × N₀ ∷ A.Γ ⊢ A.T ∶[ 1 + i ] S
T[wkwk,suv1]-inv ⊢T[wkwk,suv1]
  with t[σ]-inv ⊢T[wkwk,suv1]
... | Δ , S , ⊢[wkwk,suv1] , ⊢T , ≈Sei
  with ⊢suv1 , ≈Δ ← ,-inv′ ⊢[wkwk,suv1] (⊢wk∘wk-gen (proj₁ (presup-tm ⊢T[wkwk,suv1])))
  with refl , _ ← su-inv ⊢suv1 = _ , refl , ctxeq-tm (⊢≈-sym ≈Δ) ⊢T

-- ⫢N-E : ∀ {i} →
--        (N ∷ U.Γ′) ⫢ U.T′ ∶ Se i →
--        U.Γ′ ⫢ U.s′ ∶ U.T′ U.[| ze ∶ N ] →
--        (U.T′ ∷ N ∷ U.Γ′) ⫢ U.r′ ∶ U.T′ U.[ (wk ∘ wk) , su (v 1) ∶ N ] →
--        U.Γ′ ⫢ U.t′ ∶ N →
--        --------------------------
--        U.Γ′ ⫢ rec U.T′ U.s′ U.r′ U.t′ ∶ U.T′ U.[| U.t′ ∶ N ]
-- ⫢N-E  ⫢T′ ⫢s′ ⫢r′ ⫢t′
--   with _ , _ , T , _ , (↝∷ Γ₁↝ ↝N) , T↝ , ↝Se , ⊢T , _ , IHT ← ⫢T′
--      | j , Γ , s , _ , Γ↝ , s↝ , ↝sub {t = T₁} T↝₁ (↝, ↝I ↝ze ↝N) , ⊢s , IHΓ , IHs ← ⫢s′
--      | k , _ , r , _ , (↝∷ {T = T₃} (↝∷ Γ₂↝ ↝N) T↝₃) , r↝ , ↝sub {t = T₂} T↝₂ (↝, (↝∘ ↝wk ↝wk) (↝su ↝v) ↝N) , ⊢r , _ , IHr ← ⫢r′
--      | _ , Γ₃ , t , _ , Γ₃↝ , t↝ , ↝N , ⊢t , _ , IHt ← ⫢t′ 
--   with (⊢∷ {Γ = Γ₁} ⊢Γ₁ ⊢N₁) ← proj₁ (presup-tm ⊢T)
--      | ⊢Γ , ⊢T₁[|ze] ← presup-tm ⊢s
--      | (⊢∷ (⊢∷ ⊢Γ₂ ⊢N₂) ⊢T₃) , ⊢T₂[wkwk,ze] ← (presup-tm ⊢r) 
--   with refl ← N≈⇒eq-lvl (≈-refl ⊢N₁)
--      | refl ← N≈⇒eq-lvl (≈-refl ⊢N₂) 
--   with refl ← ⊢T:Se-lvl ⊢T
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--      | Γ≈Γ₃ ← IHΓ Γ₃↝ (proj₁ (presup-tm ⊢t)) 
--   with T≈T₃ ← IHT T↝₃ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) (≈-refl ⊢N₂)) ⊢T₃) 
--   with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₃))) 
--   = _ , _ , _ , _ , Γ↝ , ↝rec T↝ s↝ r↝ t↝ , ↝sub T↝ (↝, ↝I t↝ ↝N) , N-E (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (≈-refl ⊢N₁)) ⊢T) ⊢s_ ⊢r_ ⊢t_ , IHΓ , IHrec
--   where
--     N∷Γ₁≈N∷Γ = ∷-cong-simp (⊢≈-sym Γ≈Γ₁) (≈-refl ⊢N₁)
--     Γ₁≈Γ₂ = ⊢≈-trans (⊢≈-sym Γ≈Γ₁) Γ≈Γ₂
--     N∷Γ₁≈N∷Γ₂ = ∷-cong-simp Γ₁≈Γ₂ (≈-refl ⊢N₁)

--     ⊢s_ : Γ ⊢ s ∶[ _ ] T A.[| ze ∶ N₀ ]
--     ⊢s_ 
--       with SeS , refl , ⊢T₁ ← T[I,ze]-inv ⊢T₁[|ze] 
--       with T≈T₁ ← IHT T↝₁ (ctxeq-tm (∷-cong-simp Γ≈Γ₁ (≈-refl (N-wf ⊢Γ))) ⊢T₁)
--       with refl , Sej≈ ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
--       = conv ⊢s ([]-cong-Se′ (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (≈-refl ⊢N₁)) (≈-conv (≈-sym T≈T₁) (≈-sym Sej≈))) (⊢I,ze ⊢Γ))

--     ⊢r_ : (T ↙ _) L.∷ N₀ L.∷ Γ ⊢ r ∶[ _ ] sub T ((wk ∘ wk) , su (v 1) ∶ N₀) 
--     ⊢r_ 
--       with SeS , refl , ⊢T₂ ← T[wkwk,suv1]-inv ⊢T₂[wkwk,ze]
--       with T≈T₂ ← IHT T↝₂ (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ₁≈Γ₂) (≈-refl ⊢N₂)) ⊢T₂)
--       with refl , Sej≈SeS ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₂)))
--       = conv (ctxeq-tm (∷-cong-simp (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (≈-refl ⊢N₂)) (ctxeq-≈ N∷Γ₁≈N∷Γ₂ (≈-sym T≈T₃))) ⊢r) ([]-cong-Se′ (ctxeq-≈ N∷Γ₁≈N∷Γ (≈-conv (≈-sym T≈T₂) (≈-sym Sej≈SeS))) (⊢[wk∘wk],su[v1] (⊢∷ (⊢∷ ⊢Γ (N-wf ⊢Γ)) (ctxeq-tm N∷Γ₁≈N∷Γ ⊢T))))
        
--     ⊢t_ : Γ ⊢ t ∶[ _ ] N
--     ⊢t_
--       with refl ← ⊢t∶N-lvl ⊢t = (ctxeq-tm (⊢≈-sym Γ≈Γ₃) ⊢t)
      
--     IHrec : ∀ {tᵢ iᵢ Tᵢ} → tᵢ ↝ _ → Γ A.⊢ tᵢ ∶[ iᵢ ] Tᵢ → Γ ⊢ _ ≈ tᵢ ∶[ iᵢ ] Tᵢ
--     IHrec (↝rec ↝Tᵢ ↝sᵢ ↝rᵢ ↝tᵢ) ⊢rectᵢ 
--       with rec-inv ⊢rectᵢ
--     ...  | refl , ⊢Tᵢ , ⊢sᵢ , ⊢rᵢ , ⊢tᵢ , Tᵢ≈ 
--       with T≈Tᵢ ← IHT ↝Tᵢ (ctxeq-tm (⊢≈-sym N∷Γ₁≈N∷Γ) ⊢Tᵢ) 
--       with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈Tᵢ)))
--       with T₃∷N∷Γ₂≈Tᵢ∷N∷Γ ← ∷-cong-simp (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (≈-refl ⊢N₂)) (ctxeq-≈ N∷Γ₁≈N∷Γ₂ (≈-trans (≈-sym T≈T₃) T≈Tᵢ))
--       with s≈sᵢ ← IHs ↝sᵢ ⊢sᵢ
--          | r≈rᵢ ← IHr ↝rᵢ (ctxeq-tm (⊢≈-sym T₃∷N∷Γ₂≈Tᵢ∷N∷Γ) ⊢rᵢ)
--          | t≈tᵢ ← IHt ↝tᵢ (ctxeq-tm Γ≈Γ₃ ⊢tᵢ)
--       = ≈-conv (≈-sym (rec-cong ⊢Tᵢ (ctxeq-≈ N∷Γ₁≈N∷Γ (≈-sym T≈Tᵢ)) (≈-sym s≈sᵢ) (ctxeq-≈ T₃∷N∷Γ₂≈Tᵢ∷N∷Γ (≈-sym r≈rᵢ)) (ctxeq-≈ (⊢≈-sym Γ≈Γ₃) (≈-sym t≈tᵢ)))) 
--         (≈-sym Tᵢ≈)

-- ⫢Λ-I : ∀ {i} →
--        U.Γ′ ⫢ U.S′ ∶ Se i →
--        (U.S′ ∷ U.Γ′) ⫢ U.t′ ∶ U.T′ →
--        --------------------
--        U.Γ′ ⫢ Λ U.S′ U.t′ ∶ Π U.S′ U.T′
-- ⫢Λ-I {i = i} ⫢S′ ⫢t′
--   with  _ , Γ , S , _ , Γ↝ , S↝ , ↝Se , ⊢S , IHΓ , IHS ← ⫢S′
--      | k , _ , t , T , (↝∷ {T = S₁} Γ↝₁ S↝₁) , t↝ , T↝ , ⊢t , _ , IHt ← ⫢t′
--   with ⊢∷ ⊢Γ₁ ⊢S₁ ← proj₁ (presup-tm ⊢t)
--   with Γ≈Γ₁ ← IHΓ Γ↝₁ ⊢Γ₁
--   with S≈S₁ ← IHS S↝₁ (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S₁)
--   with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
--   with refl ← ⊢T:Se-lvl ⊢S
--   = _ , _ , _ , _ , Γ↝ , ↝Λ S↝ t↝ , ↝Π {i = i} {j = k} S↝ T↝ , Λ-I ⊢S (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (ctxeq-≈ Γ≈Γ₁ (≈-sym S≈S₁))) ⊢t) refl , IHΓ , IHΛ
--   where
--     IHΛ : ∀ {tᵢ iᵢ Tᵢ} → tᵢ ↝ _ → Γ A.⊢ tᵢ ∶[ iᵢ ] Tᵢ → Γ ⊢ _ ≈ tᵢ ∶[ iᵢ ] Tᵢ
--     IHΛ (↝Λ {i = i} Sᵢ↝ tᵢ↝) ⊢Λtᵢ
--       with jᵢ , Tᵢ , Tᵢ≈ , i≡maxjᵢ , ⊢tᵢ ← Λ-inv′ ⊢Λtᵢ 
--       with ⊢∷ ⊢Γ ⊢Sᵢ , _ ← presup-tm ⊢tᵢ
--       with S≈Sᵢ ← IHS Sᵢ↝ ⊢Sᵢ
--       with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈Sᵢ)))
--       with S₁≈S₂ ← ctxeq-≈ Γ≈Γ₁ (≈-trans (≈-sym S≈S₁) S≈Sᵢ)
--       with Sᵢ∷Γ≈S₁∷Γ₁ ← ∷-cong-simp (⊢≈-sym Γ≈Γ₁)  S₁≈S₂
--       with t≈tᵢ ← IHt tᵢ↝ (ctxeq-tm (⊢≈-sym Sᵢ∷Γ≈S₁∷Γ₁) ⊢tᵢ)
--       = ≈-conv (≈-sym (Λ-cong ⊢Sᵢ (≈-sym S≈Sᵢ) (ctxeq-≈ Sᵢ∷Γ≈S₁∷Γ₁ (≈-sym t≈tᵢ)) i≡maxjᵢ)) (≈-sym Tᵢ≈)

-- ⫢Λ-E : ∀ {i j} →
--        U.Γ′ ⫢ U.S′ ∶ Se i →
--        U.S′ ∷ U.Γ′ ⫢ U.T′ ∶ Se j →
--        U.Γ′ ⫢ U.r′ ∶ Π U.S′ U.T′ →
--        U.Γ′ ⫢ U.s′ ∶ U.S′ →
--        --------------------
--        U.Γ′ ⫢ U.r′ $ U.s′ ∶ U.T′ U.[| U.s′ ∶ U.S′ ]
-- ⫢Λ-E ⫢S′ ⫢T′ ⫢r′ ⫢s′
--   with  _ , Γ , S , _ , Γ↝ , S↝S′ , ↝Se , ⊢S , IHΓ , IHS ← ⫢S′
--      | _ , .(S₁ ↙ _) L.∷ Γ₁ , T , .(Se _) , (↝∷ {T = S₁} Γ↝₁ S↝₁S′) , T↝ , ↝Se , ⊢T , _ , IHT ← ⫢T′
--      | k , Γ₂ , r , _ , Γ↝₂ , r↝r′ , ↝Π S↝₂S′ T↝T′ , ⊢r , _ , IHr ← ⫢r′
--      | j , Γ₃ , s , S₃ , Γ↝₃ , s↝s′ , S↝₃S′ , ⊢s , _ , IHs ← ⫢s′ 
--   with refl ← ⊢T:Se-lvl ⊢S
--      | refl ← ⊢T:Se-lvl ⊢T 
--   with ⊢∷ ⊢Γ₁ ⊢S₁ ← proj₁ (presup-tm ⊢T)
--      | ⊢Γ₂ , ⊢ΠS₂T₁ ← presup-tm ⊢r
--      | ⊢Γ₃ , ⊢S₃ ← presup-tm ⊢s
--   with IHΓ Γ↝₁ ⊢Γ₁
--      | IHΓ Γ↝₂ ⊢Γ₂
--      | IHΓ Γ↝₃ ⊢Γ₃
-- ...  | Γ≈Γ₁ | Γ≈Γ₂ | Γ≈Γ₃ 
--   with refl , ⊢S₂ , ⊢T₁ ← Π-inv ⊢ΠS₂T₁
--   with S≈S₁ ← IHS S↝₁S′ (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S₁)
--      | S≈S₂ ← IHS S↝₂S′ (ctxeq-tm (⊢≈-sym Γ≈Γ₂) ⊢S₂)
--      | S≈S₃ ← IHS S↝₃S′ (ctxeq-tm (⊢≈-sym Γ≈Γ₃) ⊢S₃) 
--   with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
--      | refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₂)))
--      | refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₃))) 
--   with T≈T₁ ← IHT T↝T′ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) (ctxeq-≈ Γ≈Γ₂ (≈-trans (≈-sym S≈S₂) S≈S₁))) ⊢T₁) 
--   with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
--   = _ , _ , _ , _ , Γ↝ , ↝$ r↝r′ s↝s′ , ↝sub T↝ (↝, ↝I s↝s′ S↝S′) , 
--     Λ-E ⊢S 
--         (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (ctxeq-≈ Γ≈Γ₁ (≈-sym S≈S₁))) ⊢T) 
--         (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₂) ⊢r) 
--               (Π-cong (ctxeq-tm (⊢≈-sym Γ≈Γ₂) ⊢S₂) (≈-sym S≈S₂) (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (ctxeq-≈ Γ≈Γ₁ (≈-trans (≈-sym S≈S₁) S≈S₂))) (≈-sym T≈T₁)) refl)) (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₃) ⊢s) (≈-sym S≈S₃)) 
--         refl , 
--     IHΓ , IHrs
--   where
--     IHrs : ∀ {tᵢ iᵢ Tᵢ} → tᵢ ↝ _ → Γ A.⊢ tᵢ ∶[ iᵢ ] Tᵢ → Γ ⊢ _ ≈ tᵢ ∶[ iᵢ ] Tᵢ
--     IHrs (↝$ rᵢ↝ sᵢ↝) ⊢Λrs
--       with j , k , Sᵢ , Tᵢ , ⊢rᵢ , ⊢sᵢ , i≡maxjk , ≈T[|s] ← $-inv ⊢Λrs
--       with _ , ⊢Sᵢ , ⊢Tᵢ ← Π-inv (proj₂ (presup-tm ⊢rᵢ)) 
--       with rᵢ≈r ← IHr rᵢ↝ (ctxeq-tm Γ≈Γ₂ ⊢rᵢ)
--          | sᵢ≈s ← IHs sᵢ↝ (ctxeq-tm Γ≈Γ₃ ⊢sᵢ) = ≈-conv (≈-sym ($-cong ⊢Sᵢ ⊢Tᵢ (ctxeq-≈ (⊢≈-sym Γ≈Γ₂) (≈-sym rᵢ≈r)) (ctxeq-≈ (⊢≈-sym Γ≈Γ₃) (≈-sym sᵢ≈s)) i≡maxjk)) (≈-sym ≈T[|s])

-- ⫢L-I : ∀ {j} →
--        U.Γ′ ⫢ U.t′ ∶ U.T′ →
--        --------------------
--        U.Γ′ ⫢ liftt j U.t′ ∶ Liftt j U.T′
-- ⫢L-I ⫢t′
--   with i , Γ , t , T , Γ↝ , t↝ , T↝ , ⊢t , IHΓ , IHt ← ⫢t′
--     = _ , _ , _ , _ , Γ↝ , ↝liftt t↝ , ↝Liftt T↝ , L-I _ ⊢t , IHΓ , IHlift
--   where
--     IHlift : ∀ {tᵢ iᵢ Tᵢ} → tᵢ ↝ _ → Γ A.⊢ tᵢ ∶[ iᵢ ] Tᵢ → Γ ⊢ _ ≈ tᵢ ∶[ iᵢ ] Tᵢ
--     IHlift (↝liftt tᵢ↝) ⊢lifttᵢ
--       with liftt-inv ⊢lifttᵢ
--     ... | jᵢ , Sᵢ , refl , ⊢tᵢ , Tᵢ≈ = ≈-conv (liftt-cong _ (IHt tᵢ↝ ⊢tᵢ))  (≈-sym Tᵢ≈)

-- ⫢L-E : ∀ {i j} →
--        U.Γ′ ⫢ U.T′ ∶ Se i →
--        U.Γ′ ⫢ U.t′ ∶ Liftt j U.T′ →
--        --------------------
--        U.Γ′ ⫢ unlift U.t′ ∶ U.T′
-- ⫢L-E ⫢T′ ⫢t′
--   with i , Γ , T , _ , Γ↝ , T↝ , ↝Se , ⊢T , IHΓ , IHT ← ⫢T′
--      | j , Γ₁ , t , _ , Γ₁↝ , t↝ , ↝Liftt T₁↝ , ⊢t , _ , IHt ← ⫢t′ 
--   with ⊢Γ₁ , ⊢LifttT₁ ← presup-tm ⊢t
--   with refl , ⊢T₁ ← Liftt-inv ⊢LifttT₁
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--   with refl ← ⊢T:Se-lvl ⊢T
--   with T≈T₁ ← IHT T₁↝ (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢T₁)
--   with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁))) 
--   = _ , _ , _ , _ , Γ↝ , ↝unlift t↝ , T↝ , 
--     L-E _ ⊢T (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢t) (Liftt-cong _ (≈-sym T≈T₁))) , 
--     IHΓ , IHlift

--   where
--     IHlift : ∀ {tᵢ iᵢ Tᵢ} → tᵢ ↝ _ → Γ A.⊢ tᵢ ∶[ iᵢ ] Tᵢ → Γ ⊢ _ ≈ tᵢ ∶[ iᵢ ] Tᵢ
--     IHlift (↝unlift tᵢ↝) ⊢unlifttᵢ
--       with jᵢ , nᵢ , Sᵢ , refl , ⊢tᵢ , Tᵢ≈ ← unlift-inv ⊢unlifttᵢ
--       with _ , ⊢Tᵢ ← Liftt-inv (proj₂ (presup-tm ⊢tᵢ))
--       with t≈tᵢ ← IHt tᵢ↝ (ctxeq-tm Γ≈Γ₁ ⊢tᵢ) 
--       = ≈-conv (unlift-cong _ ⊢Tᵢ (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) t≈tᵢ))  (≈-sym Tᵢ≈)

-- ⫢t[σ] : U.Δ′ ⫢ U.t′ ∶ U.T′ →
--         U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--         --------------------
--         U.Γ′ ⫢ U.t′ U.[ U.σ′ ] ∶ U.T′ U.[ U.σ′ ]
-- ⫢t[σ] ⫢t′ ⫢σ′
--   with i , Δ , t , T , Δ↝ , t↝ , T↝ , ⊢t , IHΔ , IHt ← ⫢t′
--      | Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHΓ , IHσ ← ⫢σ′
--   with Δ≈Δ₁ ← IHΔ Δ₁↝ (proj₂ (presup-s ⊢σ)) 
--   = _ , _ , _ , _ , Γ↝ , ↝sub t↝ σ↝ , ↝sub T↝ σ↝ , t[σ] ⊢t (s-conv ⊢σ (⊢≈-sym Δ≈Δ₁)) , IHΓ , IHt[σ] 
--   where 
--     IHt[σ] : ∀ {tᵢ iᵢ Tᵢ} → tᵢ ↝ _ → Γ A.⊢ tᵢ ∶[ iᵢ ] Tᵢ → Γ ⊢ _ ≈ tᵢ ∶[ iᵢ ] Tᵢ
--     IHt[σ] (↝sub tᵢ↝ σᵢ↝) ⊢tᵢ[σ]
--       with Δᵢ , S , ⊢σᵢ , ⊢tᵢ , ≈S[σᵢ] ← t[σ]-inv ⊢tᵢ[σ]
--       with σ≈σᵢ ← IHσ σᵢ↝ ⊢σᵢ 
--       with Δ₁≈Δᵢ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σᵢ))) 
--       with Δᵢ≈Δ ← ⊢≈-trans (⊢≈-sym Δ₁≈Δᵢ) (⊢≈-sym Δ≈Δ₁)
--       = ≈-conv (≈-sym ([]-cong (≈-sym (IHt tᵢ↝ (ctxeq-tm Δᵢ≈Δ ⊢tᵢ))) (s-≈-sym (IHσ σᵢ↝ (s-conv ⊢σᵢ Δᵢ≈Δ))))) (≈-sym ≈S[σᵢ])

-- ⫢conv : ∀ {i} →
--         U.Γ′ ⫢ U.t′ ∶ U.S′ →
--         U.Γ′ ⫢ U.S′ ≈ U.T′ ∶ Se i →
--         --------------------
--         U.Γ′ ⫢ U.t′ ∶ U.T′
-- ⫢conv ⫢t′ S′≈T′
--   with i , Γ , t , S₁ , Γ↝ , t↝ , S₁↝ , ⊢t , IHΓ , IHt ← ⫢t′
--      | _ , Γ₁ , S , T , _ , Γ₁↝ , S↝ , T↝ , ↝Se , S≈T , _ , IHS , _ ← S′≈T′ 
--   with ⊢Γ₁ , ⊢S , _ , _ ← presup-≈ S≈T
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--   with refl ← ⊢T:Se-lvl ⊢S 
--   with S≈S₁ ← IHS S₁↝ (ctxeq-tm Γ≈Γ₁ (proj₂ (presup-tm ⊢t))) 
--   with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
--   = _ , _ , _ , _ , Γ↝ , t↝ , T↝ , conv ⊢t (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-trans (≈-sym S≈S₁) S≈T)) , IHΓ , IHt

-- ⫢s-I : ⫢ U.Γ′ →
--        --------------------
--        U.Γ′ ⫢s I ∶ U.Γ′
-- ⫢s-I ⫢Γ′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′ = _ , _ , _ , Γ↝ , Γ↝ , ↝I , s-I ⊢Γ , IHΓ , λ { ↝I ⊢σᵢ → s-≈-refl ⊢σᵢ }

-- ⫢s-wk : ⫢ U.T′ ∷ U.Γ′ →
--         --------------------
--         U.T′ ∷ U.Γ′ ⫢s wk ∶ U.Γ′
-- ⫢s-wk ⫢T∷Γ′
--   with .((_ ↙ _) L.∷ _) , ⊢∷ ⊢Γ ⊢T , ↝∷ Γ↝ T↝ , IHΓ ← ⫢T∷Γ′ = _ , _ , _ , ↝∷ Γ↝ T↝ , Γ↝ , ↝wk , s-wk (⊢∷ ⊢Γ ⊢T) , IHΓ , λ { ↝wk ⊢σᵢ → s-≈-refl ⊢σᵢ }

-- ⫢s-∘ :  U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--         U.Δ′ ⫢s U.τ′ ∶ U.Ψ′ →
--         --------------------
--         U.Γ′ ⫢s U.τ′ ∘ U.σ′ ∶ U.Ψ′
-- ⫢s-∘ ⫢σ′ ⫢τ′
--   with Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHΓ , IHτ ← ⫢σ′
--      | Δ , Ψ , τ , Δ↝ , Ψ↝ , τ↝ , ⊢τ , IHΔ , IHσ ← ⫢τ′ 
--   with Δ≈Δ₁ ← IHΔ Δ₁↝ (proj₂ (presup-s ⊢σ)) 
--   = _ , _ , _ , Γ↝ , Ψ↝ , ↝∘ τ↝ σ↝ , s-∘ ⊢σ  (ctxeq-s Δ≈Δ₁ ⊢τ) , IHΓ , IHτ∘σ
--   where 
--     IHτ∘σ : (∀ {σᵢ Δᵢ} → σᵢ ↝s _ → Γ A.⊢s σᵢ ∶ Δᵢ → Γ A.⊢s _ ≈ σᵢ ∶ Δᵢ)
--     IHτ∘σ (↝∘ {σ = τᵢ} {τ = σᵢ} τᵢ↝ σᵢ↝) ⊢σᵢ∘τᵢ 
--       with ∘-inv ⊢σᵢ∘τᵢ
--     ...  | Ψᵢ , ⊢σᵢ , ⊢τᵢ
--       with σ≈σᵢ ← (IHτ σᵢ↝ ⊢σᵢ)  
--       with Δ₁≈Ψᵢ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σᵢ))) 
--       with Δ≈Ψᵢ ← ⊢≈-trans Δ≈Δ₁ Δ₁≈Ψᵢ
--       with τ≈τᵢ ← IHσ τᵢ↝ (ctxeq-s (⊢≈-sym Δ≈Ψᵢ) ⊢τᵢ)  = ∘-cong σ≈σᵢ (ctxeq-s-≈ Δ≈Ψᵢ τ≈τᵢ) 

-- ⫢s-, : ∀ {i} →
--        U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--        U.Δ′ ⫢ U.T′ ∶ Se i →
--        U.Γ′ ⫢ U.t′ ∶ U.T′ U.[ U.σ′ ] →
--        -------------------------
--        U.Γ′ ⫢s U.σ′ , U.t′ ∶ U.T′ ∶ U.T′ ∷ U.Δ′
-- ⫢s-, ⫢σ′ ⫢T′ ⫢t′
--   with Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHΓ , IHσ ← ⫢σ′
--      | _ , Δ , T , _ , Δ↝ , T↝ , ↝Se , ⊢T , IHΔ , IHT ← ⫢T′
--      | i , Γ₁ , t , _ , Γ₁↝ , t↝ , (↝sub {T₁} T↝₁ σ↝₁) , ⊢t , _ , IHt ← ⫢t′
--   with refl ← ⊢T:Se-lvl ⊢T 
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ (proj₁ (presup-tm ⊢t))
--      | Δ≈Δ₁ ← IHΔ Δ₁↝ (proj₂ (presup-s ⊢σ))
--   = _ , _ , _ , Γ↝ , ↝∷ Δ↝ T↝ , (↝, σ↝ t↝ T↝) , 
--     s-, (s-conv ⊢σ (⊢≈-sym Δ≈Δ₁)) ⊢T ⊢t_ , IHΓ , IHσ,t
--       --  _ , _ , _ , Γ↝ , ↝∷ Δ↝ T↝ , (↝, σ↝ t↝ T↝) , s-, (s-conv (ctxeq-s (⊢≈-sym Γ≈Γ₁) ⊢σ) (⊢≈-sym Δ≈Δ₁)) (ctxeq-tm (⊢≈-sym Δ≈Δ₂) ⊢T) ⊢t_ , IHσ,t
--   where
--     ⊢t_ : Γ ⊢ t ∶[ _ ] sub T σ
--     ⊢t_
--       with ⊢T₁[σ] ← proj₂ (presup-tm ⊢t)
--       with Δ₂ , S , ⊢σ₁ , ⊢T₁ , _ ← t[σ]-inv ⊢T₁[σ]
--       with σ≈σ₁ ← IHσ σ↝₁ (ctxeq-s (⊢≈-sym Γ≈Γ₁) ⊢σ₁) 
--       with Δ₁≈Δ₂ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σ₁))) 
--       with Δ₂≈Δ ← ⊢≈-trans (⊢≈-sym Δ₁≈Δ₂) (⊢≈-sym Δ≈Δ₁)
--       with T≈T₁ ← IHT T↝₁ (ctxeq-tm Δ₂≈Δ ⊢T₁) 
--       with refl , ≈Se ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁))) 
--       = conv (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢t) ([]-cong-Se-simp (ctxeq-≈ (⊢≈-sym Δ₂≈Δ) (≈-conv (≈-sym T≈T₁) (≈-sym ≈Se))) (s-≈-sym σ≈σ₁))

--     IHσ,t : (∀ {σᵢ Δᵢ} → σᵢ ↝s _ → Γ A.⊢s σᵢ ∶ Δᵢ → Γ A.⊢s _ ≈ σᵢ ∶ Δᵢ)
--     IHσ,t  (↝, {σ = σᵢ} {t = tᵢ} {T = Tᵢ} σᵢ↝ tᵢ↝ Tᵢ↝) ⊢σᵢ,
--       with ,-inv ⊢σᵢ,
--     ...  | Δᵢ , ⊢σᵢ , ⊢tᵢ , ≈T∷Δᵢ
--       with ⊢Tᵢ[σᵢ] ← proj₂ (presup-tm ⊢tᵢ)
--       with S , ⊢Tᵢ , Seᵢ≈S[σᵢ] ← t[σ]-inv′ ⊢Tᵢ[σᵢ] ⊢σᵢ
--       with σ≈σᵢ ← IHσ σᵢ↝ ⊢σᵢ 
--       with Δ₁≈Δᵢ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σᵢ))) 
--       with Δ≈Δᵢ ← ⊢≈-trans Δ≈Δ₁ Δ₁≈Δᵢ
--       with T≈Tᵢ ← IHT Tᵢ↝ (ctxeq-tm (⊢≈-sym Δ≈Δᵢ) ⊢Tᵢ)
--       with t≈tᵢ ← IHt tᵢ↝ (ctxeq-tm Γ≈Γ₁ ⊢tᵢ) 
--       with refl , Sei≈ ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈Tᵢ))) 
--       = s-≈-conv (,-cong σ≈σᵢ 
--                          (ctxeq-tm Δ≈Δᵢ ⊢T) 
--                          (ctxeq-≈ Δ≈Δᵢ (≈-conv T≈Tᵢ (≈-sym Sei≈))) 
--                          (≈-conv (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) t≈tᵢ) ([]-cong-Se-simp (≈-conv (≈-sym T≈Tᵢ) (≈-sym Sei≈)) (s-≈-conv (s-≈-sym σ≈σᵢ) (⊢≈-sym Δ≈Δᵢ))))) 
--                  (⊢≈-trans (∷-cong″ (ctxeq-≈ Δ≈Δᵢ (≈-conv T≈Tᵢ (≈-sym Sei≈)))) ≈T∷Δᵢ) 

-- ⫢s-conv : U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--           ⫢ U.Δ′ ≈ U.Ψ′ →
--           -------------------------
--           U.Γ′ ⫢s U.σ′ ∶ U.Ψ′
-- ⫢s-conv ⫢σ′ Δ′≈Ψ′
--   with Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHΓ , IHσ ← ⫢σ′
--      | Δ , Ψ , Δ↝ , Ψ↝ , Δ≈Ψ , IHΔ , _ ← Δ′≈Ψ′ 
--   with Δ≈Δ₁ ← IHΔ Δ₁↝ (proj₂ (presup-s ⊢σ)) 
--      = _ , _ , _ , Γ↝ , Ψ↝ , σ↝ , s-conv ⊢σ (⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Ψ) , IHΓ , IHσ

-- ⫢N-[] : U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--         --------------------
--         U.Γ′ ⫢ N U.[ U.σ′ ] ≈ N ∶ Se 0
-- ⫢N-[] ⫢σ′
--   with Γ , Δ , σ , Γ↝ , Δ↝ , σ↝ , ⊢σ , IHΓ , IHσ ← ⫢σ′ = _ , _ , _ , _ , _ , Γ↝ , ↝sub ↝N σ↝ , ↝N , ↝Se , N-[] ⊢σ , IHΓ , IHN[σ] , λ { ↝N ⊢N → ≈-refl ⊢N }
--   where 
--     IHN[σ] : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
--     IHN[σ] (↝sub ↝N σ₁↝) ⊢N[σᵢ] 
--       with Δᵢ , SeS , ⊢σᵢ , ⊢N , T≈ ← t[σ]-inv ⊢N[σᵢ] 
--       with refl , T≈Se ← N:T-inv′ ⊢N
--       with σᵢ≈σ ← IHσ σ₁↝ ⊢σᵢ
--       = ≈-conv (≈-sym ([]-cong (≈-refl ⊢N) (s-≈-sym σᵢ≈σ))) (≈-sym T≈)

-- ⫢Se-[] : ∀ {i} →
--           U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--           --------------------
--           U.Γ′ ⫢ Se i U.[ U.σ′ ] ≈ Se i ∶ Se (1 + i)
-- ⫢Se-[] ⫢σ′
--   with Γ , Δ , σ , Γ↝ , Δ↝ , σ↝ , ⊢σ , IHΓ , IHσ ← ⫢σ′
--   = _ , _ , _ , _ , _ , Γ↝ , ↝sub ↝Se σ↝ , ↝Se , ↝Se , Se-[] _ ⊢σ , IHΓ , IHSe[σ] , λ { ↝Se ⊢Se → ≈-refl ⊢Se }
--   where 
--     IHSe[σ] : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
--     IHSe[σ] (↝sub ↝Se σ₁↝) ⊢Se[σᵢ] 
--       with Δᵢ , SeS , ⊢σᵢ , ⊢Se , T≈ ← t[σ]-inv ⊢Se[σᵢ] 
--       with σᵢ≈σ ← IHσ σ₁↝ ⊢σᵢ
--       = ≈-conv (≈-sym ([]-cong (≈-refl ⊢Se) (s-≈-sym σᵢ≈σ))) (≈-sym T≈)

-- ⫢Liftt-[] : ∀ {i j} →
--             U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--             U.Δ′ ⫢ U.T′ ∶ Se i →
--             --------------------
--             U.Γ′ ⫢ Liftt j U.T′ U.[ U.σ′ ] ≈ Liftt j (U.T′ U.[ U.σ′ ]) ∶ Se (j + i)
-- ⫢Liftt-[] ⫢σ′ ⫢T′
--   with Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHΓ , IHσ ← ⫢σ′
--      | _ , Δ , T , _ , Δ↝ , T↝ , ↝Se , ⊢T , IHΔ , IHT ← ⫢T′ 
--   with refl ← ⊢T:Se-lvl ⊢T
--   with Δ≈Δ₁ ← IHΔ Δ₁↝ (proj₂ (presup-s ⊢σ)) 
--   = _ , _ , _ , _ , _ , Γ↝ , ↝sub (↝Liftt T↝) σ↝ , ↝Liftt (↝sub T↝ σ↝) , ↝Se , Liftt-[] _ ⊢σ (ctxeq-tm Δ≈Δ₁ ⊢T) , IHΓ , IHLiftT[σ] , IHLift,T[σ]
--   where
--     IHLiftT[σ] : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
--     IHLiftT[σ] (↝sub (↝Liftt Tᵢ↝) σᵢ↝) ⊢Lift[σᵢ] 
--       with Δᵢ , SeS , ⊢σᵢ , ⊢LiftTᵢ , S≈ ← t[σ]-inv ⊢Lift[σᵢ]
--       with refl , ⊢Tᵢ , Se≈ ← Liftt-inv′ ⊢LiftTᵢ
--       with σ≈σᵢ ← IHσ σᵢ↝ ⊢σᵢ 
--       with Δ₁≈Δᵢ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σᵢ))) 
--       with Δ≈Δᵢ ← ⊢≈-trans Δ≈Δ₁ Δ₁≈Δᵢ
--       with T≈Tᵢ ← IHT Tᵢ↝ (ctxeq-tm (⊢≈-sym Δ≈Δᵢ) ⊢Tᵢ)
--       with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈Tᵢ)))
--       = ≈-conv (≈-sym ([]-cong (≈-conv (Liftt-cong _ (ctxeq-≈ Δ≈Δᵢ (≈-sym T≈Tᵢ))) (≈-sym Se≈)) (s-≈-sym σ≈σᵢ))) (≈-sym S≈)
    
--     IHLift,T[σ] : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
--     IHLift,T[σ] (↝Liftt (↝sub Tᵢ↝ σᵢ↝) ) ⊢Lift,T[σᵢ] 
--       with refl , ⊢Tᵢ[σ] , Se≈ ← Liftt-inv′ ⊢Lift,T[σᵢ] 
--       with Δᵢ , SeS , ⊢σᵢ , ⊢Tᵢ , S≈ ← t[σ]-inv ⊢Tᵢ[σ] 
--       with σ≈σᵢ ← IHσ σᵢ↝ ⊢σᵢ 
--       with Δ₁≈Δᵢ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σᵢ))) 
--       with Δ≈Δᵢ ← ⊢≈-trans Δ≈Δ₁ Δ₁≈Δᵢ
--       with T≈Tᵢ ← IHT Tᵢ↝ (ctxeq-tm (⊢≈-sym Δ≈Δᵢ) ⊢Tᵢ)
--       with refl , S≈Se ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈Tᵢ)))
--       = ≈-conv (Liftt-cong _ ([]-cong-Se-simp (ctxeq-≈ Δ≈Δᵢ (≈-conv T≈Tᵢ (≈-sym S≈Se)))  σ≈σᵢ)) (≈-sym Se≈)

qσ-inv : ∀ {i j} →
           (A.T ↙ j) ∷ A.Γ A.⊢s A.q (A.S ↙ i) A.σ ∶ A.Δ →
           ∃ λ Ψ → A.⊢ A.Δ ≈ (A.S ↙ i) ∷ Ψ × A.Γ A.⊢s A.σ ∶ Ψ
qσ-inv ⊢qσ
  with Ψ , ⊢σwk , ⊢v0 , (∷-cong Γ≈Δ _ _ _ S≈S′) ← ,-inv ⊢qσ 
  with Θ , ⊢wk , ⊢σ ← ∘-inv ⊢σwk 
  with Γ≈θ ← wk-inv ⊢wk = Ψ , ∷-cong-simp (⊢≈-sym Γ≈Δ) (≈-sym S≈S′) , ctxeq-s (⊢≈-sym Γ≈θ) ⊢σ

qqσ-inv : ∀ {i₁ i₂ j₁ j₂ T₁ T₂ S₁ S₂} →
           (T₂ ↙ j₂) ∷ (T₁ ↙ j₁) ∷ A.Γ A.⊢s A.q (S₂ ↙ i₂) (A.q (S₁ ↙ i₁) A.σ) ∶ A.Δ →
           ∃ λ Ψ → A.Γ A.⊢s A.σ ∶ Ψ × A.⊢ A.Δ ≈ (S₂ ↙ i₂) ∷ (S₁ ↙ i₁) ∷ Ψ
qqσ-inv ⊢qqσ 
  with Ψ , Ψ≈ , ⊢qσ ← qσ-inv ⊢qqσ
  with _ , ⊢∷ ⊢Ψ ⊢S₂ ← presup-⊢≈ Ψ≈
  with θ , θ≈ , ⊢σ ← qσ-inv ⊢qσ = _ , ⊢σ , ⊢≈-trans Ψ≈ (∷-cong-simp θ≈ (≈-refl ⊢S₂))

IH-transform : ∀ {Γ t′ t t₁ i i₁ T T₁} →  
               (∀ {t₁ i₁ T₁} → t₁ ↝ t′ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ t ≈ t₁ ∶[ i₁ ] T₁) →
               t₁ ↝ t′ →
               Γ ⊢ t₁ ∶[ i₁ ] T₁ → 
               Γ ⊢ t ∶[ i ] T →
               i ≡ i₁ × Γ ⊢ t₁ ≈ t ∶[ i ] T
IH-transform IH t₁↝ ⊢t₁ ⊢t 
  with t≈t₁ ← IH t₁↝ ⊢t₁ 
  with refl , T≈T₁ ← unique-typ ⊢t (proj₁ (proj₂ (presup-≈ t≈t₁)))
  = refl , ≈-conv (≈-sym t≈t₁) (≈-sym T≈T₁)

t[σ]-inv-IH : ∀ {σ₁ i} →
              (∀ {σᵢ Δᵢ} → σᵢ ↝s U.σ′ → A.Γ A.⊢s σᵢ ∶ Δᵢ → A.Γ A.⊢s A.σ ≈ σᵢ ∶ Δᵢ) → 
              A.Γ ⊢ A.t A.[ σ₁ ] ∶[ i ] A.T →
              σ₁ ↝s U.σ′ →
              A.Γ A.⊢s A.σ ∶ A.Δ →
              ∃ λ S → A.Γ A.⊢s σ₁ ≈ A.σ ∶ A.Δ × A.Γ A.⊢s σ₁ ∶ A.Δ × A.Δ ⊢ A.t ∶[ i ] S × A.Γ ⊢ A.T ≈ S A.[ σ₁ ] ∶[ 1 + i ] Se i
t[σ]-inv-IH IHσ ⊢t[σ₁] σ₁↝ ⊢σ 
  with Δ₁ , S , ⊢σ₁ , ⊢t , T≈ ← t[σ]-inv ⊢t[σ₁] 
  with σ≈σ₁ ← IHσ σ₁↝ ⊢σ₁
  with Δ≈Δ₁ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σ₁)))
  = _ , s-≈-conv (s-≈-sym σ≈σ₁) (⊢≈-sym Δ≈Δ₁) , s-conv ⊢σ₁ (⊢≈-sym Δ≈Δ₁) , ctxeq-tm (⊢≈-sym Δ≈Δ₁) ⊢t , T≈

,-inv-IH : ∀ {σ₁ i Ψ} →
          (∀ {σᵢ Δᵢ} → σᵢ ↝s U.σ′ → A.Γ A.⊢s σᵢ ∶ Δᵢ → A.Γ A.⊢s A.σ ≈ σᵢ ∶ Δᵢ) →
          A.Γ A.⊢s (σ₁ , A.t ∶ A.T ↙ i) ∶ Ψ →
          σ₁ ↝s U.σ′ →
          A.Γ A.⊢s A.σ ∶ A.Δ →
          A.Γ A.⊢s σ₁ ≈ A.σ ∶ A.Δ × A.Γ A.⊢s σ₁ ∶ A.Δ × A.Γ ⊢ A.t ∶[ i ] sub A.T A.σ × A.⊢ (A.T ↙ i) ∷ A.Δ ≈ Ψ 
,-inv-IH IHσ ⊢σ₁,t σ₁↝ ⊢σ 
  with Ψ , ⊢σ₁ , ⊢t , S≈ ← ,-inv ⊢σ₁,t 
  with ⊢∷ ⊢Ψ ⊢T , _ ← presup-⊢≈ S≈
  with σ≈σ₁ ← IHσ σ₁↝ ⊢σ₁ 
  with Δ≈Ψ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σ₁)))
  = s-≈-conv (s-≈-sym σ≈σ₁) (⊢≈-sym Δ≈Ψ) , s-conv ⊢σ₁ (⊢≈-sym Δ≈Ψ) , conv ⊢t ([]-cong-Se‴ ⊢T (s-≈-sym σ≈σ₁)) , ⊢≈-trans (∷-cong-simp Δ≈Ψ (≈-refl (ctxeq-tm (⊢≈-sym Δ≈Ψ) ⊢T))) S≈
  
qσ-inv-IH : ∀ {i j σ₁ Ψ} →
           (∀ {σᵢ Δᵢ} → σᵢ ↝s U.σ′ → A.Γ A.⊢s σᵢ ∶ Δᵢ → A.Γ A.⊢s A.σ ≈ σᵢ ∶ Δᵢ) →
           (A.T ↙ j) ∷ A.Γ A.⊢s A.q (A.S ↙ i) σ₁ ∶ Ψ →
           σ₁ ↝s U.σ′ →
           A.Γ A.⊢s A.σ ∶ A.Δ →
           A.Γ A.⊢s σ₁ ≈ A.σ ∶ A.Δ × A.Γ A.⊢s σ₁ ∶ A.Δ × A.⊢ Ψ ≈ (A.S ↙ i) ∷ A.Δ × A.Δ A.⊢ A.S ∶[ 1 + i ] Se i
qσ-inv-IH IHσ ⊢qσ₁ σ₁↝ ⊢σ 
  with θ , Ψ≈ , ⊢σ₁ ← qσ-inv ⊢qσ₁
  with _ , ⊢∷ _ ⊢S ← presup-⊢≈ Ψ≈
  with σ≈σ₁ ← IHσ σ₁↝ ⊢σ₁ 
  with Δ≈Θ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σ₁))) 
  = s-≈-conv (s-≈-sym σ≈σ₁) (⊢≈-sym Δ≈Θ) , s-conv ⊢σ₁ (⊢≈-sym Δ≈Θ) , ⊢≈-trans Ψ≈ (∷-cong-simp (⊢≈-sym Δ≈Θ) (≈-refl ⊢S)) , ctxeq-tm (⊢≈-sym Δ≈Θ) ⊢S

qqσ-inv-IH : ∀ {i₁ i₂ j₁ j₂ σ₁ T₁ T₂ S₁ S₂ Ψ} →
            (∀ {σᵢ Δᵢ} → σᵢ ↝s U.σ′ → A.Γ A.⊢s σᵢ ∶ Δᵢ → A.Γ A.⊢s A.σ ≈ σᵢ ∶ Δᵢ) →
            (T₂ ↙ j₂) ∷ (T₁ ↙ j₁) ∷ A.Γ A.⊢s A.q (S₂ ↙ i₂) (A.q (S₁ ↙ i₁) σ₁) ∶ Ψ →
            σ₁ ↝s U.σ′ →
            A.Γ A.⊢s A.σ ∶ A.Δ →
            A.Γ A.⊢s σ₁ ≈ A.σ ∶ A.Δ × A.Γ A.⊢s σ₁ ∶ A.Δ × A.⊢ Ψ ≈ (S₂ ↙ i₂) ∷ (S₁ ↙ i₁) ∷ A.Δ
qqσ-inv-IH IHσ ⊢qqσ₁ σ₁↝ ⊢σ
  with Ψ , ⊢σ₁ , Ψ≈ ← qqσ-inv ⊢qqσ₁
  with _ , ⊢∷ (⊢∷ _ ⊢S₁) ⊢S₂ ← presup-⊢≈ Ψ≈
  with σ≈σ₁ ← IHσ σ₁↝ ⊢σ₁
  with Δ≈Ψ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σ₁)))
  = s-≈-conv (s-≈-sym σ≈σ₁) (⊢≈-sym Δ≈Ψ) , s-conv ⊢σ₁ (⊢≈-sym Δ≈Ψ) , ⊢≈-trans Ψ≈ (∷-cong-simp (∷-cong-simp (⊢≈-sym Δ≈Ψ) (≈-refl ⊢S₁)) (≈-refl ⊢S₂))
  
-- ⫢Π-[] : ∀ {i j k} →
--          U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--          U.Δ′ ⫢ U.S′ ∶ Se i →
--          (U.S′ ∷ U.Δ′) ⫢ U.T′ ∶ Se j →
--          k ≡ max i j →
--          --------------------
--          U.Γ′ ⫢ Π U.S′ U.T′ U.[ U.σ′ ] ≈ Π (U.S′ U.[ U.σ′ ]) (U.T′ U.[ U.q U.S′ U.σ′ ]) ∶ Se k
-- ⫢Π-[] ⫢σ′ ⫢S′ ⫢T′ k≡maxij
--   with Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHΓ , IHσ ← ⫢σ′
--      | _ , Δ , S , _ , Δ↝ , S↝ , ↝Se , ⊢S , IHΔ , IHS ← ⫢S′
--      | _ , _ , T , _ , (↝∷ {Γ = Δ₂} {T = S₁} Δ₂↝ S₁↝) , T↝ , ↝Se , ⊢T , _ , IHT ← ⫢T′
--   with refl ← ⊢T:Se-lvl ⊢S
--      | refl ← ⊢T:Se-lvl ⊢T
--   with ⊢Γ , ⊢Δ₁ ← presup-s ⊢σ
--      | ⊢∷ ⊢Δ₂ ⊢S₁ ← proj₁ (presup-tm ⊢T)
--   with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
--      | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂ 
--   with S≈S₁ ← IHS S₁↝ (ctxeq-tm (⊢≈-sym Δ≈Δ₂) ⊢S₁) 
--   with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁))) 
--   = _ , _ , _ , _ , _ , Γ↝ , ↝sub (↝Π S↝ T↝) σ↝ , ↝Π (↝sub S↝ σ↝) (↝sub T↝ (↝, (↝∘ σ↝ ↝wk) ↝v S↝)) , ↝Se 
--     , Π-[] (s-conv ⊢σ (⊢≈-sym Δ≈Δ₁)) ⊢S (ctxeq-tm (∷-cong-simp (⊢≈-sym Δ≈Δ₂) (ctxeq-≈ Δ≈Δ₂ (≈-sym S≈S₁))) ⊢T) k≡maxij , IHΓ , IHΠST[σ] , IHΠS[σ]T[qσ]
--   where
--     ⊢S[σ]∷Γ : A.⊢ (sub S σ ↙ _) ∷ Γ
--     ⊢S[σ]∷Γ = ⊢∷ ⊢Γ (t[σ]-Se ⊢S (s-conv ⊢σ (⊢≈-sym Δ≈Δ₁)))

--     IHΠST[σ] : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
--     IHΠST[σ] (↝sub (↝Π Sᵢ↝ Tᵢ↝) σᵢ↝) ⊢ΠST[σ] 
--       with _ , σ≈σᵢ , ⊢σᵢ , ⊢ΠST , x  ← t[σ]-inv-IH IHσ ⊢ΠST[σ] σᵢ↝ ⊢σ 
--       with refl , ≈Se , ⊢Sᵢ , ⊢Tᵢ ← Π-inv′ ⊢ΠST
--       with refl , Sᵢ≈S ← IH-transform IHS Sᵢ↝ (ctxeq-tm (⊢≈-sym  Δ≈Δ₁) ⊢Sᵢ) ⊢S
--       with S₁≈Sᵢ ← ≈-trans (≈-sym S≈S₁) (≈-sym Sᵢ≈S)
--       with refl , Tᵢ≈T ← IH-transform IHT Tᵢ↝ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₂) (ctxeq-≈ Δ≈Δ₁ (≈-sym  S₁≈Sᵢ))) ⊢Tᵢ) ⊢T
--       = ≈-conv (≈-sym ([]-cong (≈-conv (Π-cong-simp (ctxeq-≈ Δ≈Δ₁ Sᵢ≈S) (ctxeq-≈ (∷-cong-simp (⊢≈-trans (⊢≈-sym Δ≈Δ₂) Δ≈Δ₁) (ctxeq-≈ Δ≈Δ₂ S₁≈Sᵢ)) Tᵢ≈T) refl) (≈-sym ≈Se)) σ≈σᵢ)) (≈-sym x)
        
--     IHΠS[σ]T[qσ] : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
--     IHΠS[σ]T[qσ] (↝Π (↝sub {t = S₁₁} {σ = σᵢ₁} Sᵢ₁↝ σᵢ₁↝) (↝sub {t = Tᵢ} Tᵢ↝ (↝, {T = Sᵢ₂} (↝∘ σᵢ₂↝ ↝wk) ↝v Sᵢ₂↝))) ⊢ΠS[σ]T[qσ] 
--       with refl , ≈Se , ⊢Sᵢ₁[σᵢ₁] , ⊢Tᵢ[qσᵢ₂] ← Π-inv′ ⊢ΠS[σ]T[qσ] 
--       with Δᵢ₁ , _ , ⊢σᵢ₁ , ⊢Sᵢ₁ , [σ]≈Se ← t[σ]-inv ⊢Sᵢ₁[σᵢ₁]
--       with σ≈σᵢ₁ ← IHσ σᵢ₁↝ ⊢σᵢ₁
--       with Δ₁≈Δᵢ₁ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σᵢ₁)))
--       with Δ≈Δᵢ₁ ← ⊢≈-trans Δ≈Δ₁ Δ₁≈Δᵢ₁
--       with S≈Sᵢ₁ ← IHS Sᵢ₁↝ (ctxeq-tm (⊢≈-sym Δ≈Δᵢ₁) ⊢Sᵢ₁)
--       with refl , ≈Sei ← unique-typ ⊢S (proj₁ (proj₂ (presup-≈ S≈Sᵢ₁)))
--       with Sᵢ₂∷Δᵢ₂ , _ , ⊢qσᵢ₂ , ⊢Tᵢ , e ← t[σ]-inv ⊢Tᵢ[qσᵢ₂]
--       with Δᵢ₂ , ≈Sᵢ₂∷Δᵢ₂ , ⊢σᵢ₂ ← qσ-inv ⊢qσᵢ₂
--       with σ≈σᵢ₂ ← IHσ σᵢ₂↝ ⊢σᵢ₂
--       with Δ₁≈Δᵢ₂ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σᵢ₂)))
--       with Δ≈Δᵢ₂ ← ⊢≈-trans Δ≈Δ₁ Δ₁≈Δᵢ₂
--       with (⊢∷ ⊢Δᵢ₂ ⊢Sᵢ₂) ← proj₂ (presup-⊢≈ ≈Sᵢ₂∷Δᵢ₂)
--       with S≈Sᵢ₂ ← IHS Sᵢ₂↝ (ctxeq-tm (⊢≈-sym Δ≈Δᵢ₂) ⊢Sᵢ₂)
--       with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈Sᵢ₂)))
--       with T≈Tᵢ ← IHT Tᵢ↝ (ctxeq-tm (⊢≈-trans ≈Sᵢ₂∷Δᵢ₂ (∷-cong-simp (⊢≈-trans (⊢≈-sym Δ≈Δᵢ₂) Δ≈Δ₂) (ctxeq-≈ Δ≈Δᵢ₂ (≈-trans (≈-sym S≈Sᵢ₂) S≈S₁) ))) ⊢Tᵢ)
--       with refl , ≈Sej ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈Tᵢ)))
--       = ≈-conv (Π-cong (t[σ]-Se (ctxeq-tm Δ≈Δ₁ ⊢S) ⊢σ) ([]-cong-Se-simp (ctxeq-≈ Δ≈Δᵢ₁ (≈-conv S≈Sᵢ₁ (≈-sym ≈Sei))) σ≈σᵢ₁) 
--                        ([]-cong-Se-simp (ctxeq-≈ (∷-cong-simp (⊢≈-trans (⊢≈-sym Δ≈Δ₂) Δ≈Δ₁) (ctxeq-≈ Δ≈Δ₂ (≈-sym S≈S₁))) (≈-conv T≈Tᵢ (≈-sym ≈Sej) ))
--                                         (,-cong (∘-cong (wk-≈ ⊢S[σ]∷Γ) (s-≈-conv σ≈σᵢ₂ (⊢≈-trans (⊢≈-sym Δ≈Δᵢ₂) Δ≈Δ₁))) (ctxeq-tm Δ≈Δ₁ ⊢S) (ctxeq-≈ Δ≈Δ₁ S≈Sᵢ₂) (≈-refl (conv (vlookup ⊢S[σ]∷Γ here) ([∘]-Se ⊢S (s-conv ⊢σ (⊢≈-sym Δ≈Δ₁)) (s-wk ⊢S[σ]∷Γ)))))) refl) 
--                (≈-sym ≈Se)

-- ⫢Π-cong : ∀ {i j k S₁′ S₂′ T₁′ T₂′} →
--            U.Γ′ ⫢ S₁′ ∶ Se i →
--            U.Γ′ ⫢ S₁′ ≈ S₂′ ∶ Se i →
--            S₁′ ∷ U.Γ′ ⫢ T₁′ ≈ T₂′ ∶ Se j →
--            k ≡ max i j →
--            --------------------
--            U.Γ′ ⫢ Π S₁′ T₁′ ≈ Π S₂′ T₂′ ∶ Se k
-- ⫢Π-cong ⫢S₁′ S₁′≈S₂′ T₁′≈T₂′ k≡maxij
--   with _ , Γ , S₁₁ , _ , Γ↝ , S₁₁↝ , ↝Se , ⊢S₁ , IHΓ , IHS₁ ← ⫢S₁′
--      | _ , Γ₁ , S₁₂ , S₂₁ , _ , Γ₁↝ , S₁₂↝ , S₂₁↝ , ↝Se , S₁₂≈S₂₁ , _ , _ , IHS₂ ← S₁′≈S₂′
--      | _ , S∷Γ₂ , T₁₁ , T₂₁ , _ , (↝∷ {T = S₁₃} Γ₂↝ S₁₃↝) , T₁₁↝ , T₂₁↝ , ↝Se , T₁₁≈T₂₁ , _ , IHT₁ , IHT₂ ← T₁′≈T₂′ 
--   with ⊢Γ₁ , ⊢S₁₂ , ⊢S₂₁ , _ ← presup-≈ S₁₂≈S₂₁
--      | ⊢∷ ⊢Γ₂ ⊢S₁₃ , ⊢T₁₁ , ⊢T₂₁ , _ ← presup-≈ T₁₁≈T₂₁
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--   with refl ← ⊢T:Se-lvl ⊢S₁
--      | refl ← ⊢T≈S:Se-lvl S₁₂≈S₂₁
--      | refl ← ⊢T≈S:Se-lvl T₁₁≈T₂₁ 
--   with S₁≈S₁₂ ← IHS₁ S₁₂↝ (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S₁₂)
--      | S₁≈S₁₃ ← IHS₁ S₁₃↝ (ctxeq-tm (⊢≈-sym Γ≈Γ₂) ⊢S₁₃) 
--   with refl ← unique-lvl ⊢S₁ (proj₁ (proj₂ (presup-≈ S₁≈S₁₃)))
--   = _ , _ , _ , _ , _ , Γ↝ , ↝Π S₁₁↝ T₁₁↝ , ↝Π S₂₁↝ T₂₁↝ , ↝Se , 
--     Π-cong ⊢S₁ (≈-trans S₁≈S₁₂ (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) S₁₂≈S₂₁)) (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (ctxeq-≈ Γ≈Γ₂ (≈-sym S₁≈S₁₃))) T₁₁≈T₂₁) k≡maxij , IHΓ , IHΠS₁T₁ , IHΠS₂T₂
--   where
--     IHΠS₁T₁ : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
--     IHΠS₁T₁ (↝Π {S = Sᵢ} {T = Rᵢ} Sᵢ↝ Rᵢ↝) ⊢ΠSᵢRᵢ 
--       with refl , Tᵢ≈ , ⊢Sᵢ , ⊢Rᵢ ← Π-inv′ ⊢ΠSᵢRᵢ
--       with S₁≈Sᵢ ← IHS₁ Sᵢ↝ ⊢Sᵢ
--       with refl ← unique-lvl ⊢S₁ (proj₁ (proj₂ (presup-≈ S₁≈Sᵢ)))
--       with T₁≈Rᵢ ← IHT₁ Rᵢ↝ (ctxeq-tm (∷-cong-simp Γ≈Γ₂ (≈-trans (≈-sym S₁≈Sᵢ) S₁≈S₁₃)) ⊢Rᵢ)
--       with refl ← unique-lvl ⊢T₁₁ (proj₁ (proj₂ (presup-≈ T₁≈Rᵢ)))
--       = ≈-conv (Π-cong ⊢S₁ S₁≈Sᵢ (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (ctxeq-≈ Γ≈Γ₂ (≈-sym S₁≈S₁₃))) T₁≈Rᵢ) refl) (≈-sym Tᵢ≈)

--     IHΠS₂T₂ : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
--     IHΠS₂T₂ (↝Π {S = Sᵢ} {T = Rᵢ} Sᵢ↝ Rᵢ↝) ⊢ΠSᵢRᵢ 
--       with refl , Tᵢ≈ , ⊢Sᵢ , ⊢Rᵢ ← Π-inv′ ⊢ΠSᵢRᵢ 
--       with S₂≈Sᵢ ← IHS₂ Sᵢ↝ (ctxeq-tm Γ≈Γ₁ ⊢Sᵢ)
--       with refl ← unique-lvl ⊢S₂₁ (proj₁ (proj₂ (presup-≈ S₂≈Sᵢ)))
--       with T₂≈Rᵢ ← IHT₂ Rᵢ↝ (ctxeq-tm (∷-cong-simp Γ≈Γ₂ (≈-trans (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S₂≈Sᵢ)) (≈-trans (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S₁₂≈S₂₁)) (≈-trans (≈-sym S₁≈S₁₂) S₁≈S₁₃)))) ⊢Rᵢ)
--       with refl ← unique-lvl ⊢T₂₁ (proj₁ (proj₂ (presup-≈ T₂≈Rᵢ)))
--       = ≈-conv (Π-cong (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S₂₁) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) S₂≈Sᵢ) (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (ctxeq-≈ Γ≈Γ₂ (≈-trans (≈-sym S₁≈S₁₃) (≈-trans S₁≈S₁₂ (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) S₁₂≈S₂₁))))) T₂≈Rᵢ) refl) (≈-sym Tᵢ≈)

-- ⫢Liftt-cong : ∀ {i j} →
--               U.Γ′ ⫢ U.S′ ≈ U.T′ ∶ Se i →
--               --------------------
--               U.Γ′ ⫢ Liftt j U.S′ ≈ Liftt j U.T′ ∶ Se (j + i)
-- ⫢Liftt-cong S′≈T′
--   with _ , Γ , S , T , _ , Γ↝ , S↝ , T↝ , ↝Se , S≈T , IHΓ , IHS , IHT ← S′≈T′
--   with ⊢Γ , ⊢S , ⊢T , _ ← presup-≈ S≈T
--   with refl ← ⊢T≈S:Se-lvl S≈T = _ , _ , _ , _ , _ , Γ↝ , ↝Liftt S↝ , ↝Liftt T↝ , ↝Se , Liftt-cong _ S≈T , IHΓ , IHLifttS , IHLifttT 

--   where 
--     IHLifttS : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
--     IHLifttS (↝Liftt Sᵢ↝) ⊢Liftt 
--       with refl , ⊢Sᵢ , ≈Se ← Liftt-inv′ ⊢Liftt
--       with refl , Sᵢ≈S ← IH-transform IHS Sᵢ↝ ⊢Sᵢ ⊢S
--       = ≈-conv (Liftt-cong _ (≈-sym Sᵢ≈S)) (≈-sym ≈Se) 

--     IHLifttT : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
--     IHLifttT (↝Liftt Tᵢ↝) ⊢Liftt        
--       with refl , ⊢Tᵢ , ≈Se ← Liftt-inv′ ⊢Liftt
--       with refl , Tᵢ≈T ← IH-transform IHT Tᵢ↝ ⊢Tᵢ ⊢T
--       = ≈-conv (Liftt-cong _ (≈-sym Tᵢ≈T)) (≈-sym ≈Se) 

-- ⫢v-≈ : ∀ {x} →
--        ⫢ U.Γ′ →
--        x ∶ U.T′ ∈! U.Γ′ →
--        --------------------
--        U.Γ′ ⫢ v x ≈ v x ∶ U.T′
-- ⫢v-≈ ⫢Γ′ x∈Γ′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--   with i , T , T↝ , x∈Γ ← U⇒A-vlookup Γ↝ x∈Γ′ = _ , _ , _ , _ , _ , Γ↝ , ↝v , ↝v , T↝ , v-≈ ⊢Γ x∈Γ , IHΓ , (λ {↝v ⊢v → ≈-refl ⊢v }) , (λ {↝v ⊢v → ≈-refl ⊢v })

-- ⫢ze-≈ : ⫢ U.Γ′ →
--         --------------------
--         U.Γ′ ⫢ ze ≈ ze ∶ N
-- ⫢ze-≈ ⫢Γ′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--     = _ , _ , _ , _ , _ , Γ↝ , ↝ze , ↝ze , ↝N , ze-≈ ⊢Γ , IHΓ , (λ {↝ze ⊢ze → ≈-refl ⊢ze }) , (λ {↝ze ⊢ze → ≈-refl ⊢ze })

-- ⫢su-cong : U.Γ′ ⫢ U.s′ ≈ U.t′ ∶ N →
--            --------------------
--            U.Γ′ ⫢ su U.s′ ≈ su U.t′ ∶ N
-- ⫢su-cong s′≈t′
--   with _ , Γ , s , t , _ , Γ↝ , s↝ , t↝ , ↝N , s≈t , IHΓ , IHs , IHt ← s′≈t′
--   with ⊢Γ , ⊢s , ⊢t , _ ← presup-≈ s≈t
--   with refl ← ⊢t≈s∶N-lvl s≈t
--     = _ , _ , _ , _ , _ , Γ↝ , ↝su s↝ , ↝su t↝ , ↝N , su-cong s≈t , IHΓ , IHsus , IHsut
  
--   where
--     IHsus : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
--     IHsus (↝su sᵢ↝) ⊢susᵢ 
--       with refl , ≈N , ⊢sᵢ ← su-inv ⊢susᵢ
--       with _ , sᵢ≈s ← IH-transform IHs sᵢ↝ ⊢sᵢ ⊢s
--       = ≈-conv (su-cong (≈-sym sᵢ≈s)) (≈-sym ≈N)

--     IHsut : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
--     IHsut (↝su tᵢ↝) ⊢sutᵢ
--       with refl , ≈N , ⊢tᵢ ← su-inv ⊢sutᵢ
--       with _ , tᵢ≈t ← IH-transform IHt tᵢ↝ ⊢tᵢ ⊢t
--       = ≈-conv (su-cong (≈-sym tᵢ≈t)) (≈-sym ≈N)

-- ⫢rec-cong : ∀ {i T₁′ T₂′ s₁′ s₂′ r₁′ r₂′ t₁′ t₂′} →
--             N ∷ U.Γ′ ⫢ T₁′ ∶ Se i →
--             N ∷ U.Γ′ ⫢ T₁′ ≈ T₂′ ∶ Se i →
--             U.Γ′ ⫢ s₁′ ≈ s₂′ ∶ T₁′ U.[| ze ∶ N ] →
--             T₁′ ∷ N ∷ U.Γ′ ⫢ r₁′ ≈ r₂′ ∶ T₁′ U.[ (wk ∘ wk) , su (v 1) ∶ N ] →
--             U.Γ′ ⫢ t₁′ ≈ t₂′ ∶ N →
--             --------------------
--             U.Γ′ ⫢ rec T₁′ s₁′ r₁′ t₁′ ≈ rec T₂′ s₂′ r₂′ t₂′ ∶ T₁′ U.[| t₁′ ∶ N ]
-- ⫢rec-cong _ T₁′≈T₂′ s₁′≈s₂′ r₁≈r₂′ t₁≈t₂′
--   with _ , N∷Γ₁ , T₁₁ , T₂₁ , _ , (↝∷ Γ₁↝ ↝N) , T₁₁↝ , T₂₁↝ , ↝Se , T₁₁≈T₂₁ , _ , IHT₁ , IHT₂ ← T₁′≈T₂′
--      | _ , Γ , s₁ , s₂ , _ , Γ↝ , s₁↝ , s₂↝ , ↝sub {t = T₁₂} T₁₂↝ (↝, ↝I ↝ze ↝N) , s₁≈s₂ , IHΓ , IHs₁ , IHs₂ ← s₁′≈s₂′
--      | _ , T₁∷N∷Γ₂ , r₁ , r₂ , _ , ↝∷ {T = T₁₄} (↝∷ Γ₂↝ ↝N) T₁₄↝ , r₁↝ , r₂↝ , ↝sub {t = T₁₃} T₁₃↝ (↝, (↝∘ ↝wk ↝wk) (↝su ↝v) ↝N) , r₁≈r₂ , _ , IHr₁ , IHr₂ ← r₁≈r₂′
--      | _ , Γ₃ , t₁ , t₂ , N , Γ₃↝ , t₁↝ , t₂↝ , ↝N , t₁≈t₂ , _ , IHt₁ , IHt₂ ← t₁≈t₂′ 
--   with refl ← ⊢T≈S:Se-lvl T₁₁≈T₂₁
--   with _ , refl , ⊢T₁₂ ← T[I,ze]-inv (proj₂ (proj₂ (proj₂ (presup-≈ s₁≈s₂))))
--      | _ , refl , ⊢T₁₃ ← T[wkwk,suv1]-inv (proj₂ (proj₂ (proj₂ (presup-≈ r₁≈r₂)))) 
--   with (⊢∷ ⊢Γ₁ ⊢N₁) , ⊢T₁₁ , ⊢T₂₁ , _ ← presup-≈ T₁₁≈T₂₁
--      | ⊢Γ , ⊢s₁ , ⊢s₂ , _ ← presup-≈ s₁≈s₂
--      | ⊢∷ (⊢∷ ⊢Γ₂ ⊢N₂) ⊢T₁₄ , ⊢r₁ , ⊢r₂ , _ ← presup-≈ r₁≈r₂
--      | ⊢Γ₃ , ⊢t₁ , ⊢t₂ , _ ← presup-≈ t₁≈t₂
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--      | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃ 
--   with refl ← N≈⇒eq-lvl (≈-refl ⊢N₁)
--      | refl ← N≈⇒eq-lvl (≈-refl ⊢N₂)
--      | refl ← ⊢t≈s∶N-lvl t₁≈t₂ 
--   with N∷Γ₂≈N∷Γ₁ ← ∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) (≈-refl ⊢N₂)
--      | N∷Γ≈N∷Γ₁ ← ∷-cong-simp Γ≈Γ₁ (≈-refl (N-wf ⊢Γ))
--      | N∷Γ≈N∷Γ₂ ← ∷-cong-simp Γ≈Γ₂ (≈-refl (N-wf ⊢Γ))
--   with refl , T₁₁≈T₁₂ ← IH-transform IHT₁ T₁₂↝ (ctxeq-tm N∷Γ≈N∷Γ₁ ⊢T₁₂) ⊢T₁₁
--      | refl , T₁₁≈T₁₃ ← IH-transform IHT₁ T₁₃↝ (ctxeq-tm N∷Γ₂≈N∷Γ₁ ⊢T₁₃) ⊢T₁₁
--      | refl , T₁₁≈T₁₄ ← IH-transform IHT₁ T₁₄↝ (ctxeq-tm  N∷Γ₂≈N∷Γ₁ ⊢T₁₄) ⊢T₁₁
--     = _ , _ , _ , _ , _ , Γ↝ , ↝rec T₁₁↝ s₁↝ r₁↝ t₁↝ , ↝rec T₂₁↝ s₂↝ r₂↝ t₂↝ , ↝sub T₁₁↝ (↝, ↝I t₁↝ ↝N) , 
--       rec-cong-simp (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (≈-refl ⊢N₁)) T₁₁≈T₂₁) 
--                     (≈-conv s₁≈s₂ ([]-cong-Se′ (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (≈-refl ⊢N₁)) T₁₁≈T₁₂) (⊢I,ze ⊢Γ))) 
--                     (≈-conv (ctxeq-≈ (∷-cong-simp (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (≈-refl ⊢N₂)) (ctxeq-≈ (⊢≈-sym N∷Γ₂≈N∷Γ₁) T₁₁≈T₁₄)) r₁≈r₂) ([]-cong-Se′ (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (≈-refl ⊢N₁)) T₁₁≈T₁₃) (⊢[wk∘wk],su[v1] (⊢∷ (⊢∷ ⊢Γ (N-wf ⊢Γ)) (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (≈-refl ⊢N₁)) ⊢T₁₁))))) 
--                     (ctxeq-≈ (⊢≈-sym Γ≈Γ₃) t₁≈t₂) , 
--       IHΓ , IHrec₁ , IHrec₂
--     where
--       IHrec₁ : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
--       IHrec₁ (↝rec Tᵢ↝ sᵢ↝ rᵢ↝ tᵢ↝) ⊢recᵢ 
--         with refl , ⊢Tᵢ , ⊢sᵢ , ⊢rᵢ , ⊢tᵢ , ≈Tᵢ[|tᵢ] ← rec-inv ⊢recᵢ 
--         with refl , Tᵢ≈T₁₁ ← IH-transform IHT₁ Tᵢ↝ (ctxeq-tm N∷Γ≈N∷Γ₁ ⊢Tᵢ) ⊢T₁₁
--         with _ , sᵢ≈s₁ ← IH-transform IHs₁ sᵢ↝  ⊢sᵢ ⊢s₁
--         with _ , rᵢ≈r₁ ← IH-transform IHr₁ rᵢ↝ (ctxeq-tm (∷-cong-simp N∷Γ≈N∷Γ₂ (ctxeq-≈ (⊢≈-sym N∷Γ≈N∷Γ₁) (≈-trans Tᵢ≈T₁₁ (≈-sym T₁₁≈T₁₄)))) ⊢rᵢ) ⊢r₁
--         with refl , tᵢ≈t₁ ← IH-transform IHt₁ tᵢ↝ (ctxeq-tm Γ≈Γ₃ ⊢tᵢ) ⊢t₁
--         = ≈-conv (≈-sym (rec-cong-simp (ctxeq-≈ (⊢≈-sym N∷Γ≈N∷Γ₁) Tᵢ≈T₁₁) 
--                         (≈-conv sᵢ≈s₁ ([]-cong-Se′ (ctxeq-≈ (⊢≈-sym N∷Γ≈N∷Γ₁) (≈-trans T₁₁≈T₁₂ (≈-sym Tᵢ≈T₁₁))) (⊢I,ze ⊢Γ) )) 
--                         (≈-conv (ctxeq-≈ (∷-cong-simp (⊢≈-sym N∷Γ≈N∷Γ₂) (ctxeq-≈ (⊢≈-sym N∷Γ₂≈N∷Γ₁) (≈-trans T₁₁≈T₁₄ (≈-sym Tᵢ≈T₁₁)))) rᵢ≈r₁) ([]-cong-Se′ (ctxeq-≈ (⊢≈-sym N∷Γ≈N∷Γ₁) (≈-trans T₁₁≈T₁₃ (≈-sym Tᵢ≈T₁₁))) (⊢[wk∘wk],su[v1] (⊢∷ (⊢∷ ⊢Γ (N-wf ⊢Γ)) ⊢Tᵢ)))) 
--                         (ctxeq-≈ (⊢≈-sym Γ≈Γ₃) tᵢ≈t₁))) (≈-sym ≈Tᵢ[|tᵢ])

--       IHrec₂ : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
--       IHrec₂ (↝rec Tᵢ↝ sᵢ↝ rᵢ↝ tᵢ↝) ⊢recᵢ 
--         with refl , ⊢Tᵢ , ⊢sᵢ , ⊢rᵢ , ⊢tᵢ , ≈Tᵢ[|tᵢ] ← rec-inv ⊢recᵢ 
--         with refl , Tᵢ≈T₂₁ ← IH-transform IHT₂ Tᵢ↝ (ctxeq-tm N∷Γ≈N∷Γ₁ ⊢Tᵢ) ⊢T₂₁
--         with _ , sᵢ≈s₁ ← IH-transform IHs₂ sᵢ↝  ⊢sᵢ ⊢s₂
--         with _ , rᵢ≈r₁ ← IH-transform IHr₂ rᵢ↝ (ctxeq-tm (∷-cong-simp N∷Γ≈N∷Γ₂ (ctxeq-≈ (⊢≈-sym N∷Γ≈N∷Γ₁) (≈-trans Tᵢ≈T₂₁ (≈-trans (≈-sym T₁₁≈T₂₁) (≈-sym T₁₁≈T₁₄))))) ⊢rᵢ) ⊢r₂
--         with refl , tᵢ≈t₁ ← H-transform IHt₂ tᵢ↝ (ctxeq-tm Γ≈Γ₃ ⊢tᵢ) ⊢t₂
--         = ≈-conv (≈-sym (rec-cong-simp (ctxeq-≈ (⊢≈-sym N∷Γ≈N∷Γ₁) Tᵢ≈T₂₁) 
--                         (≈-conv sᵢ≈s₁ ([]-cong-Se′ (ctxeq-≈ (⊢≈-sym N∷Γ≈N∷Γ₁) (≈-trans T₁₁≈T₁₂ (≈-trans T₁₁≈T₂₁ (≈-sym Tᵢ≈T₂₁)))) (⊢I,ze ⊢Γ) )) 
--                         (≈-conv (ctxeq-≈ (∷-cong-simp (⊢≈-sym N∷Γ≈N∷Γ₂) (ctxeq-≈ (⊢≈-sym N∷Γ₂≈N∷Γ₁) (≈-trans T₁₁≈T₁₄ (≈-trans T₁₁≈T₂₁ (≈-sym Tᵢ≈T₂₁))))) rᵢ≈r₁) ([]-cong-Se′ (ctxeq-≈ (⊢≈-sym N∷Γ≈N∷Γ₁) (≈-trans T₁₁≈T₁₃ (≈-trans T₁₁≈T₂₁ (≈-sym Tᵢ≈T₂₁)))) (⊢[wk∘wk],su[v1] (⊢∷ (⊢∷ ⊢Γ (N-wf ⊢Γ)) ⊢Tᵢ)))) 
--                         (ctxeq-≈ (⊢≈-sym Γ≈Γ₃) tᵢ≈t₁))) (≈-sym ≈Tᵢ[|tᵢ])

-- ⫢Λ-cong : ∀ {i S₁′ S₂′ t₁′ t₂′} →
--            U.Γ′ ⫢ S₁′ ∶ Se i →
--            U.Γ′ ⫢ S₁′ ≈ S₂′ ∶ Se i →
--            (S₁′ ∷ U.Γ′) ⫢ t₁′ ≈ t₂′ ∶ U.T′ →
--            --------------------
--            U.Γ′ ⫢ Λ S₁′ t₁′ ≈ Λ S₂′ t₂′ ∶ Π S₁′ U.T′
-- ⫢Λ-cong _ S₁′≈S₂′ t₁′≈t₂′
--   with _ , Γ , S₁₁ , S₂₁ , _ , Γ↝ , S₁₁↝ , S₂₁↝ , ↝Se , S₁₁≈S₂₁ , IHΓ , IHS₁ , IHS₂ ← S₁′≈S₂′
--      | _ , S∷Γ₁ , t₁ , t₂ , T , ↝∷ {T = S₁₂} Γ₁↝ S₁₂↝ , t₁↝ , t₂↝ , T↝ , t₁≈t₂ , _ , IHt₁ , IHt₂ ← t₁′≈t₂′ 
--   with refl ← ⊢T≈S:Se-lvl S₁₁≈S₂₁
--   with ⊢∷ ⊢Γ₁ ⊢S₁₂ , ⊢t₁ , ⊢t₂ , _ ← presup-≈ t₁≈t₂
--      | ⊢Γ , ⊢S₁₁ , ⊢S₂₁ , _ ← presup-≈ S₁₁≈S₂₁
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--   with refl , S₁₁≈S₁₂ ← IH-transform IHS₁ S₁₂↝ (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S₁₂) ⊢S₁₁ 
--     = _ , _ , _ , _ , _ , Γ↝ , ↝Λ S₁₁↝ t₁↝ , ↝Λ S₂₁↝ t₂↝ , ↝Π S₁₁↝ T↝ ,
--       Λ-cong-simp S₁₁≈S₂₁ (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (ctxeq-≈ Γ≈Γ₁ S₁₁≈S₁₂)) t₁≈t₂) refl , 
--       IHΓ , IHΛ₁ , IHΛ₂
--   where
--     IHΛ₁ : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
--     IHΛ₁ (↝Λ Sᵢ↝ tᵢ↝) ⊢Λ 
--       with _ , _ , ≈Π , refl , ⊢tᵢ ← Λ-inv′ ⊢Λ
--       with ⊢∷ ⊢Γᵢ ⊢Sᵢ , _ ← presup-tm ⊢tᵢ
--       with refl , Sᵢ≈S ← IH-transform IHS₁ Sᵢ↝  ⊢Sᵢ ⊢S₁₁
--       with t≈tᵢ ← IHt₁ tᵢ↝ (ctxeq-tm (∷-cong-simp Γ≈Γ₁ (≈-trans Sᵢ≈S (≈-sym S₁₁≈S₁₂))) ⊢tᵢ)
--       with refl , T≈ ← unique-typ ⊢t₁ (proj₁ (proj₂ (presup-≈ t≈tᵢ)))
--       = ≈-conv (≈-sym (Λ-cong-simp Sᵢ≈S (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (ctxeq-≈ Γ≈Γ₁ (≈-sym ( ≈-trans Sᵢ≈S (≈-sym S₁₁≈S₁₂) )) )) (≈-sym t≈tᵢ)) refl)) (≈-sym ≈Π)

--     IHΛ₂ : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
--     IHΛ₂ (↝Λ Sᵢ↝ tᵢ↝) ⊢Λ 
--       with _ , _ , ≈Π , refl , ⊢tᵢ ← Λ-inv′ ⊢Λ
--       with ⊢∷ ⊢Γᵢ ⊢Sᵢ , _ ← presup-tm ⊢tᵢ
--       with refl , Sᵢ≈S ← IH-transform IHS₂ Sᵢ↝ ⊢Sᵢ ⊢S₂₁
--       with t≈tᵢ ← IHt₂ tᵢ↝ (ctxeq-tm (∷-cong-simp Γ≈Γ₁ (≈-trans Sᵢ≈S (≈-trans (≈-sym S₁₁≈S₂₁) (≈-sym S₁₁≈S₁₂))) ) ⊢tᵢ)
--       with refl , T≈ ← unique-typ ⊢t₂ (proj₁ (proj₂ (presup-≈ t≈tᵢ)))
--       = ≈-conv (≈-sym (Λ-cong-simp Sᵢ≈S (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (ctxeq-≈ Γ≈Γ₁ (≈-sym (≈-trans Sᵢ≈S (≈-trans (≈-sym S₁₁≈S₂₁) (≈-sym S₁₁≈S₁₂)))) )) (≈-sym t≈tᵢ)) refl)) (≈-sym ≈Π)


-- ⫢$-cong : ∀ {i j s₁′ s₂′ r₁′ r₂′} →
--            U.Γ′ ⫢ U.S′ ∶ Se i →
--            (U.S′ ∷ U.Γ′) ⫢ U.T′ ∶ Se j →
--            U.Γ′ ⫢ r₁′ ≈ r₂′ ∶ Π U.S′ U.T′ →
--            U.Γ′ ⫢ s₁′ ≈ s₂′ ∶ U.S′ →
--            --------------------
--            U.Γ′ ⫢ r₁′ $ s₁′ ≈ r₂′ $ s₂′ ∶ U.T′ U.[| s₁′ ∶ U.S′ ]
-- ⫢$-cong ⫢S′ ⫢T′ ⫢r₁′≈r₂′ ⫢s₁′≈s₂′
--   with _ , Γ , S , _ , Γ↝ , S↝ , ↝Se , ⊢S , IHΓ , IHS ← ⫢S′
--      | _ , S₄∷Γ₁ , T , _ , ↝∷ {T = S₁} {i = i} Γ₁↝ S₁↝ , T↝ , ↝Se , ⊢T , _ , IHT ← ⫢T′
--      | _ , Γ₂ , r₁ , r₂ , _ , Γ₂↝ , r₁↝ , r₂↝ , ↝Π S₂↝ T₁↝ , r₁≈r₂ , _ , IHr₁ , IHr₂ ← ⫢r₁′≈r₂′
--      | _ , Γ₃ , s₁ , s₂ , S₃ , Γ₃↝ , s₁↝ , s₂↝ , S₃↝ , s₁≈s₂ , _ , IHs₁ , IHs₂ ← ⫢s₁′≈s₂′ 
--   with refl ← ⊢T:Se-lvl ⊢S
--      | refl ← ⊢T:Se-lvl ⊢T
--   with ⊢Γ ← proj₁ (presup-tm ⊢S)
--      | ⊢∷ ⊢Γ₁ ⊢S₁ , _ ← presup-tm ⊢T
--      | ⊢Γ₂ , ⊢r₁ , ⊢r₂ , ⊢ΠS₂T₁ ← presup-≈ r₁≈r₂
--      | ⊢Γ₃ , ⊢s₁ , ⊢s₂ , ⊢S₃ ← presup-≈ s₁≈s₂
--   with refl , ⊢S₂ , ⊢T₁ ← Π-inv ⊢ΠS₂T₁
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--      | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃ 
--   with refl , S≈S₁ ← IH-transform IHS S₁↝ (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S₁) ⊢S
--      | refl , S≈S₂ ← IH-transform IHS S₂↝ (ctxeq-tm (⊢≈-sym Γ≈Γ₂) ⊢S₂) ⊢S
--      | refl , S≈S₃ ← IH-transform IHS S₃↝ (ctxeq-tm (⊢≈-sym Γ≈Γ₃) ⊢S₃) ⊢S
--   with S₁≈S₂ ← ≈-trans S≈S₁ (≈-sym S≈S₂)
--   with refl , T≈T₁ ← IH-transform IHT T₁↝ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) (ctxeq-≈ Γ≈Γ₂ (≈-sym S₁≈S₂))) ⊢T₁) ⊢T 
--   = _ , _ , _ , _ , _ , Γ↝ , ↝$ r₁↝ s₁↝ , ↝$ r₂↝ s₂↝ , ↝sub T↝ (↝, ↝I s₁↝ S↝) , 
--     $-cong ⊢S 
--            (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (ctxeq-≈ Γ≈Γ₁ S≈S₁)) ⊢T) 
--            (≈-conv (ctxeq-≈ (⊢≈-sym Γ≈Γ₂) r₁≈r₂) (Π-cong-simp S≈S₂ (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (ctxeq-≈ Γ≈Γ₁ S₁≈S₂)) T≈T₁) refl)) 
--            (≈-conv (ctxeq-≈ (⊢≈-sym Γ≈Γ₃) s₁≈s₂) S≈S₃) 
--            refl , 
--     IHΓ , IHr$s₁ , IHr$s₂
--   where 
--     IHr$s₁ : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
--     IHr$s₁ (↝$ rᵢ↝ sᵢ↝) ⊢r$s
--       with i , k , Sᵢ , Tᵢ , ⊢rᵢ , ⊢sᵢ , refl , ≈Tᵢ[s] ← $-inv ⊢r$s 
--       with ⊢ΠSᵢTᵢ ← proj₂ (presup-tm ⊢rᵢ)
--       with _ , ⊢Sᵢ , ⊢Tᵢ ← Π-inv ⊢ΠSᵢTᵢ
--       with r≈rᵢ ← IHr₁ rᵢ↝ (ctxeq-tm Γ≈Γ₂ ⊢rᵢ)
--       with s≈sᵢ ← IHs₁ sᵢ↝ (ctxeq-tm Γ≈Γ₃ ⊢sᵢ)
--       = ≈-conv (≈-sym ($-cong ⊢Sᵢ ⊢Tᵢ (ctxeq-≈ (⊢≈-sym Γ≈Γ₂) (≈-sym r≈rᵢ)) (ctxeq-≈ (⊢≈-sym Γ≈Γ₃) (≈-sym s≈sᵢ)) refl)) (≈-sym ≈Tᵢ[s])

--     IHr$s₂ : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
--     IHr$s₂ (↝$ rᵢ↝ sᵢ↝) ⊢r$s
--       with i , k , Sᵢ , Tᵢ , ⊢rᵢ , ⊢sᵢ , refl , ≈Tᵢ[s] ← $-inv ⊢r$s 
--       with ⊢ΠSᵢTᵢ ← proj₂ (presup-tm ⊢rᵢ)
--       with _ , ⊢Sᵢ , ⊢Tᵢ ← Π-inv ⊢ΠSᵢTᵢ
--       with r≈rᵢ ← IHr₂ rᵢ↝ (ctxeq-tm Γ≈Γ₂ ⊢rᵢ)
--       with s≈sᵢ ← IHs₂ sᵢ↝ (ctxeq-tm Γ≈Γ₃ ⊢sᵢ)
--       = ≈-conv (≈-sym ($-cong ⊢Sᵢ ⊢Tᵢ (ctxeq-≈ (⊢≈-sym Γ≈Γ₂) (≈-sym r≈rᵢ)) (ctxeq-≈ (⊢≈-sym Γ≈Γ₃) (≈-sym s≈sᵢ)) refl)) (≈-sym ≈Tᵢ[s])

-- ⫢liftt-cong : ∀ {j} →
--               U.Γ′ ⫢ U.s′ ≈ U.t′ ∶ U.T′ →
--               --------------------
--               U.Γ′ ⫢ liftt j U.s′ ≈ liftt j U.t′ ∶ Liftt j U.T′
-- ⫢liftt-cong s′≈t′
--   with _ , Γ , s , t , T , Γ↝ , s↝ , t↝ , ↝T , s≈t , IHΓ , IHs , IHt ← s′≈t′ 
--   = _ , _ , _ , _ , _ , Γ↝ , ↝liftt s↝ , ↝liftt t↝ , ↝Liftt ↝T , liftt-cong _ s≈t , IHΓ , IHlifts , IHliftt

--   where
--     IHlifts : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
--     IHlifts (↝liftt sᵢ↝) ⊢liftsᵢ
--       with i , _ , refl , ⊢sᵢ , ≈Liftt ← liftt-inv ⊢liftsᵢ
--       with s≈sᵢ ← IHs sᵢ↝ ⊢sᵢ
--       = ≈-conv (liftt-cong _ s≈sᵢ) (≈-sym ≈Liftt)
    
--     IHliftt : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
--     IHliftt (↝liftt tᵢ↝) ⊢lifttᵢ 
--       with i , _ , refl , ⊢tᵢ , ≈Liftt ← liftt-inv ⊢lifttᵢ
--       with t≈tᵢ ← IHt tᵢ↝ ⊢tᵢ
--       = ≈-conv (liftt-cong _ t≈tᵢ) (≈-sym ≈Liftt)

-- ⫢unliftt-cong : ∀ {i j} →
--                 U.Γ′ ⫢ U.T′ ∶ Se i →
--                 U.Γ′ ⫢ U.s′ ≈ U.t′ ∶ Liftt j U.T′ →
--                 --------------------
--                 U.Γ′ ⫢ unlift U.s′ ≈ unlift U.t′ ∶ U.T′
-- ⫢unliftt-cong _ ⫢s′≈t′
--   with _ , Γ , s , t , _ , Γ↝ , s↝ , t↝ , ↝Liftt ↝T , s≈t , IHΓ , IHs , IHt ← ⫢s′≈t′
--   with ⊢Γ , ⊢s , ⊢t , ⊢LifttT ← presup-≈ s≈t
--   with refl , ⊢T ← Liftt-inv ⊢LifttT
--     = _ , _ , _ , _ , _ , Γ↝ , ↝unlift s↝ , ↝unlift t↝ , ↝T , unlift-cong _ ⊢T s≈t , IHΓ , IHunlifts , IHunliftt
  
--   where
--     IHunlifts : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
--     IHunlifts (↝unlift sᵢ↝) ⊢unliftsᵢ 
--       with i , j , Tᵢ , refl , ⊢sᵢ , ≈S ← unlift-inv ⊢unliftsᵢ
--       with ⊢LiftTᵢ ← proj₂ (presup-tm ⊢sᵢ)
--       with _ , ⊢Tᵢ ← Liftt-inv ⊢LiftTᵢ
--       with s≈sᵢ ← IHs sᵢ↝ ⊢sᵢ
--       = ≈-conv (unlift-cong _ ⊢Tᵢ s≈sᵢ) (≈-sym ≈S)

--     IHunliftt : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
--     IHunliftt (↝unlift tᵢ↝) ⊢unlifttᵢ
--       with i , j , Tᵢ , refl , ⊢tᵢ , ≈S ← unlift-inv ⊢unlifttᵢ
--       with ⊢LiftTᵢ ← proj₂ (presup-tm ⊢tᵢ)
--       with _ , ⊢Tᵢ ← Liftt-inv ⊢LiftTᵢ
--       with t≈tᵢ ← IHt tᵢ↝ ⊢tᵢ
--       = ≈-conv (unlift-cong _ ⊢Tᵢ t≈tᵢ) (≈-sym ≈S)

-- ⫢[]-cong : U.Δ′ ⫢ U.t′ ≈ U.s′ ∶ U.T′ →
--            U.Γ′ ⫢s U.σ′ ≈ U.τ′ ∶ U.Δ′ →
--            --------------------
--            U.Γ′ ⫢ U.t′ U.[ U.σ′ ] ≈ U.s′ U.[ U.τ′ ] ∶ U.T′ U.[ U.σ′ ]
-- ⫢[]-cong t′≈s′ σ′≈τ′
--   with _ , Δ , t , s , T , Δ₁↝ , t↝ , s↝ , ↝T , t≈s , IHΔ , IHt , IHs ← t′≈s′
--      | Γ , Δ₁ , σ , τ , Γ↝ , Δ₁↝ , σ↝ , τ↝ , σ≈τ , IHΓ , IHσ , IHτ ← σ′≈τ′
--   with ⊢Γ , ⊢σ , ⊢τ , ⊢Δ ← presup-s-≈ σ≈τ
--   with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ
--      = _ , _ , _ , _ , _ , Γ↝ , ↝sub t↝ σ↝ , ↝sub s↝ τ↝ , ↝sub ↝T σ↝ , []-cong (ctxeq-≈ Δ≈Δ₁ t≈s) σ≈τ , IHΓ ,  IHt[σ] , IHs[τ]

--   where
--     IHt[σ] : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
--     IHt[σ] (↝sub tᵢ↝ σᵢ↝) ⊢tᵢ[σᵢ] 
--       with _ , σᵢ≈σ , ⊢σᵢ , ⊢tᵢ , ≈T[σ] ← t[σ]-inv-IH IHσ ⊢tᵢ[σᵢ] σᵢ↝ ⊢σ 
--       with t≈tᵢ ← IHt tᵢ↝ (ctxeq-tm (⊢≈-sym Δ≈Δ₁) ⊢tᵢ)
--       = ≈-conv (≈-sym ([]-cong (≈-sym t≈tᵢ) (s-≈-conv σᵢ≈σ (⊢≈-sym Δ≈Δ₁)))) (≈-sym ≈T[σ])

--     IHs[τ] : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
--     IHs[τ] (↝sub sᵢ↝ τᵢ↝) ⊢sᵢ[τᵢ] 
--       with _ , τᵢ≈τ , ⊢τᵢ , ⊢sᵢ , ≈T[τ] ← t[σ]-inv-IH IHτ ⊢sᵢ[τᵢ] τᵢ↝ ⊢τ 
--       with s≈sᵢ ← IHs sᵢ↝ (ctxeq-tm (⊢≈-sym Δ≈Δ₁) ⊢sᵢ)
--       = ≈-conv (≈-sym ([]-cong (≈-sym s≈sᵢ) (s-≈-conv τᵢ≈τ (⊢≈-sym Δ≈Δ₁)))) (≈-sym ≈T[τ])

-- ⫢ze-[] :  U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--           --------------------
--           U.Γ′ ⫢ ze U.[ U.σ′ ] ≈ ze ∶ N
-- ⫢ze-[] ⫢σ′
--   with Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHΓ , IHσ ← ⫢σ′ 
--   = _ , _ , _ , _ , _ , Γ↝ , ↝sub ↝ze σ↝ , ↝ze , ↝N , ze-[] ⊢σ , IHΓ , IHze[σ] , λ { ↝ze ⊢ze → ≈-refl ⊢ze }
  
--   where
--     IHze[σ] : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
--     IHze[σ] (↝sub ↝ze σᵢ↝) ⊢ze[σᵢ]
--       with _ , σᵢ≈σ , ⊢σᵢ , ⊢ze , ≈T[σᵢ] ← t[σ]-inv-IH IHσ ⊢ze[σᵢ] σᵢ↝ ⊢σ
--       = ≈-conv (≈-sym ([]-cong (≈-refl ⊢ze) σᵢ≈σ)) (≈-sym ≈T[σᵢ])

⫢su-[] : U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
         U.Δ′ ⫢ U.t′ ∶ N →
         --------------------
         U.Γ′ ⫢ su U.t′ U.[ U.σ′ ] ≈ su (U.t′ U.[ U.σ′ ]) ∶ N
⫢su-[] ⫢σ′ ⫢t′
  with Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHΓ , IHσ ← ⫢σ′
     | _ , Δ , t , _ , Δ↝ , t↝ , ↝N , ⊢t , IHΔ , IHt ← ⫢t′ 
  with refl ← ⊢t∶N-lvl ⊢t
  with ⊢Γ , ⊢Δ₁ ← presup-s ⊢σ
     | ⊢Δ , _ ← presup-tm ⊢t
  with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
      = _ , _ , _ , _ , _ , Γ↝ , ↝sub (↝su t↝) σ↝ , ↝su (↝sub t↝ σ↝) , ↝N , (su-[] (s-conv ⊢σ (⊢≈-sym Δ≈Δ₁)) ⊢t) , IHΓ , IHsut[σ] , IHsu,t[σ]

  where
    IHsut[σ] : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
    IHsut[σ] (↝sub (↝su tᵢ↝) σᵢ↝) ⊢sutᵢ[σᵢ] 
      with _ , σᵢ≈σ , ⊢σᵢ , ⊢sutᵢ , ≈T[σ] ← t[σ]-inv-IH IHσ ⊢sutᵢ[σᵢ] σᵢ↝ ⊢σ 
      with refl , ≈N , ⊢tᵢ ← su-inv ⊢sutᵢ
      with t≈tᵢ ← IHt tᵢ↝ (ctxeq-tm (⊢≈-sym Δ≈Δ₁) ⊢tᵢ)
      = ≈-conv (≈-sym ([]-cong (≈-conv (su-cong (ctxeq-≈ Δ≈Δ₁ (≈-sym t≈tᵢ))) (≈-sym ≈N)) σᵢ≈σ)) (≈-sym ≈T[σ])

    IHsu,t[σ] : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
    IHsu,t[σ] (↝su (↝sub tᵢ↝ σᵢ↝)) ⊢su,tᵢ 
      with refl , ≈N , ⊢tᵢ[σᵢ] ← su-inv ⊢su,tᵢ
      with _ , σᵢ≈σ , ⊢σᵢ , ⊢tᵢ , ≈T[σ] ← t[σ]-inv-IH IHσ ⊢tᵢ[σᵢ] σᵢ↝ ⊢σ 
      with t≈tᵢ ← IHt tᵢ↝ (ctxeq-tm (⊢≈-sym Δ≈Δ₁) ⊢tᵢ)
      = ≈-conv (su-cong (≈-conv (≈-sym ([]-cong (ctxeq-≈ Δ≈Δ₁ (≈-sym t≈tᵢ)) σᵢ≈σ)) (≈-sym ≈T[σ]))) (≈-sym ≈N)

⫢rec-[] : ∀ {i} →
          U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
          N ∷ U.Δ′ ⫢ U.T′ ∶ Se i →
          U.Δ′ ⫢ U.s′ ∶ U.T′ U.[| ze ∶ N ] →
          U.T′ ∷ N ∷ U.Δ′ ⫢ U.r′ ∶ U.T′ U.[ (wk ∘ wk) , su (v 1) ∶ N ] →
          U.Δ′ ⫢ U.t′ ∶ N →
          --------------------
          U.Γ′ ⫢ rec U.T′ U.s′ U.r′ U.t′ U.[ U.σ′ ] ≈ rec (U.T′ U.[ U.q N U.σ′ ]) (U.s′ U.[ U.σ′ ]) (U.r′ U.[ U.q U.T′ (U.q N U.σ′) ]) (U.t′ U.[ U.σ′ ]) ∶ U.T′ U.[ U.σ′ , U.t′ U.[ U.σ′ ] ∶ N ]
⫢rec-[] ⫢σ′ ⫢T′ ⫢s′ ⫢r′ ⫢t′
  with Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHΓ , IHσ ← ⫢σ′
     | _ , _ , T , _ , ↝∷ {Γ = Δ₂} Δ₂↝ ↝N , T↝ , ↝Se , ⊢T , _ , IHT ← ⫢T′
     | i , Δ₃ , s , _ , Δ₃↝ , s↝ , ↝sub {t = T₁} T₁↝ (↝, ↝I ↝ze ↝N) , ⊢s , _ , IHs ← ⫢s′
     | _ , _ , r , _ , (↝∷ (↝∷ {Γ = Δ₄} Δ₄↝ ↝N) T₃↝) , r↝ , ↝sub {t = T₂} T₂↝ (↝, (↝∘ ↝wk ↝wk) (↝su ↝v) ↝N) , ⊢r , _ , IHr ← ⫢r′
     | _ , Δ , t , _ , Δ↝ , t↝ , ↝N , ⊢t , IHΔ , IHt ← ⫢t′
  with ⊢Γ , ⊢Δ₁ ← presup-s ⊢σ
     | ⊢∷ ⊢Δ₂ ⊢N₁ ← proj₁ (presup-tm ⊢T)
     | ⊢Δ₃ , ⊢T₁[I,ze] ← presup-tm ⊢s
     | ⊢∷ (⊢∷ ⊢Δ₄ ⊢N₂) ⊢T₃ , ⊢T₂[wkwk,suv1] ← presup-tm ⊢r
     | ⊢Δ , _ ← presup-tm ⊢t 
  with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
     | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
     | Δ≈Δ₃ ← IHΔ Δ₃↝ ⊢Δ₃
     | Δ≈Δ₄ ← IHΔ Δ₄↝ ⊢Δ₄ 
  with refl ← ⊢T:Se-lvl ⊢T 
     | refl ← ⊢t∶N-lvl ⊢t
     | refl ← N≈⇒eq-lvl (≈-refl ⊢N₁)
     | refl ← N≈⇒eq-lvl (≈-refl ⊢N₂) 
  with _ , refl , ⊢T₁ ← T[I,ze]-inv ⊢T₁[I,ze]
     | _ , refl , ⊢T₂ ← T[wkwk,suv1]-inv ⊢T₂[wkwk,suv1] 
  with Δ₂≈Δ₄ ← ⊢≈-trans (⊢≈-sym Δ≈Δ₂) Δ≈Δ₄
     | Δ₁≈Δ₂ ← ⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₂
  with N∷Δ₂≈N∷Δ ← ∷-cong-simp (⊢≈-sym Δ≈Δ₂) (≈-refl ⊢N₁)
     | N∷Δ₄≈N∷Δ₂ ← ∷-cong-simp (⊢≈-sym Δ₂≈Δ₄) (≈-refl ⊢N₂)
     | N∷Δ₁≈N∷Δ₂ ← ∷-cong-simp (⊢≈-sym Δ₁≈Δ₂) (≈-refl ⊢N₁)
  with refl , T≈T₁ ← IH-transform IHT T₁↝ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Δ≈Δ₃) Δ≈Δ₂) (≈-refl (N-wf ⊢Δ₃))) ⊢T₁) ⊢T
     | refl , T≈T₂ ← IH-transform IHT T₂↝ (ctxeq-tm N∷Δ₄≈N∷Δ₂ ⊢T₂) ⊢T
     | refl , T≈T₃ ← IH-transform IHT T₃↝ (ctxeq-tm N∷Δ₄≈N∷Δ₂ ⊢T₃) ⊢T
   = _ , _ , _ , _ , _ , Γ↝ ,
      ↝sub (↝rec T↝ s↝ r↝ t↝) σ↝ , ↝rec (↝sub T↝ (↝, (↝∘ σ↝ ↝wk) ↝v ↝N)) (↝sub s↝ σ↝) (↝sub r↝ (↝, (↝∘ (↝, (↝∘ σ↝ ↝wk) ↝v ↝N) ↝wk) ↝v T↝)) (↝sub t↝ σ↝) , ↝sub T↝ (↝, σ↝ (↝sub t↝ σ↝) ↝N) , 
      rec-[] (s-conv ⊢σ (⊢≈-sym Δ≈Δ₁)) 
             (ctxeq-tm N∷Δ₂≈N∷Δ ⊢T) 
             (conv (ctxeq-tm (⊢≈-sym Δ≈Δ₃) ⊢s) ([]-cong-Se′ (ctxeq-≈ N∷Δ₂≈N∷Δ T≈T₁) (⊢I,ze ⊢Δ))) 
             (conv (ctxeq-tm (∷-cong-simp (∷-cong-simp (⊢≈-sym Δ≈Δ₄) (≈-refl ⊢N₂)) (ctxeq-≈ (⊢≈-sym N∷Δ₄≈N∷Δ₂) T≈T₃)) ⊢r) ([]-cong-Se′ (ctxeq-≈ N∷Δ₂≈N∷Δ T≈T₂) (⊢[wk∘wk],su[v1] (⊢∷ (⊢∷ ⊢Δ (N-wf ⊢Δ)) (ctxeq-tm N∷Δ₂≈N∷Δ ⊢T) )))) 
             ⊢t , 
      IHΓ , IHrec[σ] , IHrec,t[σ]
  where
    IHrec[σ] : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
    IHrec[σ] (↝sub (↝rec Tᵢ↝ sᵢ↝ rᵢ↝ tᵢ↝) σᵢ↝) ⊢recᵢ[σᵢ] 
      with _ , σᵢ≈σ , ⊢σᵢ , ⊢recᵢ , ≈T[σ] ← t[σ]-inv-IH IHσ ⊢recᵢ[σᵢ] σᵢ↝ ⊢σ
      with refl , ⊢Tᵢ , ⊢sᵢ , ⊢rᵢ , ⊢tᵢ , ≈Tᵢ[|tᵢ] ← rec-inv ⊢recᵢ
      with refl , T≈Tᵢ ← IH-transform IHT Tᵢ↝ (ctxeq-tm (⊢≈-sym N∷Δ₁≈N∷Δ₂) ⊢Tᵢ) ⊢T
      with s≈sᵢ ← IHs sᵢ↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₃) ⊢sᵢ)
      with Tᵢ₁∷N∷Δ₁≈T₃∷N∷Δ₄ ← ∷-cong-simp (⊢≈-trans (⊢≈-sym N∷Δ₁≈N∷Δ₂) (⊢≈-sym N∷Δ₄≈N∷Δ₂)) (ctxeq-≈ N∷Δ₁≈N∷Δ₂ (≈-trans T≈Tᵢ (≈-sym T≈T₃))) 
      with r≈rᵢ ← IHr rᵢ↝ (ctxeq-tm Tᵢ₁∷N∷Δ₁≈T₃∷N∷Δ₄ ⊢rᵢ)
      with t≈tᵢ ← IHt tᵢ↝ (ctxeq-tm (⊢≈-sym Δ≈Δ₁) ⊢tᵢ)
      = ≈-conv (≈-sym ([]-cong (≈-conv (rec-cong-simp (ctxeq-≈ N∷Δ₁≈N∷Δ₂ T≈Tᵢ) 
                                                      (ctxeq-≈ (⊢≈-trans (⊢≈-sym Δ≈Δ₃) Δ≈Δ₁) (≈-sym s≈sᵢ)) 
                                                      (ctxeq-≈ (⊢≈-sym Tᵢ₁∷N∷Δ₁≈T₃∷N∷Δ₄) (≈-sym r≈rᵢ))
                                                      (ctxeq-≈ Δ≈Δ₁ (≈-sym t≈tᵢ))) 
                                       (≈-sym ≈Tᵢ[|tᵢ])) 
                               σᵢ≈σ)) 
               (≈-sym ≈T[σ])

    IHrec,t[σ] : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
    IHrec,t[σ] (↝rec (↝sub {t = Tᵢ} Tᵢ↝ (↝, (↝∘ σᵢ↝ ↝wk) ↝v ↝N)) (↝sub sᵢ↝ σᵢ₁↝) (↝sub rᵢ↝ (↝, (↝∘ (↝, (↝∘ σᵢ₂↝ ↝wk) ↝v ↝N) ↝wk) ↝v Tᵢ₁↝)) (↝sub tᵢ↝ σᵢ₃↝)) ⊢rec,tᵢ[σ] 
      with refl , ⊢Tᵢ[qσᵢ] , ⊢sᵢ[σᵢ₁] , ⊢rᵢ[qqσᵢ₂] , ⊢t[σᵢ₃] , ≈Tᵢ[|tᵢ[σᵢ₃]] ← rec-inv ⊢rec,tᵢ[σ] 
      with _ , R , ⊢qσᵢ , ⊢Tᵢ , ≈R[qσᵢ] ← t[σ]-inv ⊢Tᵢ[qσᵢ]
      with σᵢ≈σ , ⊢σᵢ , ≈N∷Δ₁ , ⊢Nᵢ₁ ← qσ-inv-IH IHσ ⊢qσᵢ σᵢ↝ ⊢σ
      with refl ← N≈⇒eq-lvl (≈-refl ⊢Nᵢ₁)
      with Rᵢ₁ , σᵢ₁≈σ , ⊢σᵢ₂ , ⊢sᵢ , ≈R[σᵢ₁] ← t[σ]-inv-IH IHσ ⊢sᵢ[σᵢ₁] σᵢ₁↝ ⊢σ
      with refl , T≈Tᵢ ← IH-transform IHT Tᵢ↝ (ctxeq-tm (⊢≈-trans ≈N∷Δ₁ (∷-cong-simp Δ₁≈Δ₂ (≈-refl (N-wf ⊢Δ₁)))) ⊢Tᵢ) ⊢T
      with s≈sᵢ ← IHs sᵢ↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₃) ⊢sᵢ)
      with _ , Rᵢ₂ , ⊢qqσᵢ , ⊢rᵢ , ≈R[qqσᵢ] ← t[σ]-inv ⊢rᵢ[qqσᵢ₂]
      with σᵢ₂≈σ , ⊢σᵢ₂ , ≈Tᵢ₁∷N∷Δ₁ ← qqσ-inv-IH IHσ ⊢qqσᵢ σᵢ₂↝ ⊢σ
      with _ , ⊢∷ (⊢∷ _ ⊢N) ⊢Tᵢ₁ ← presup-⊢≈ ≈Tᵢ₁∷N∷Δ₁
      with refl ← N≈⇒eq-lvl (≈-refl ⊢N)
      with refl , T≈Tᵢ₁ ← IH-transform IHT Tᵢ₁↝ (ctxeq-tm (⊢≈-sym N∷Δ₁≈N∷Δ₂) ⊢Tᵢ₁) ⊢T
      with Tᵢ₁∷N∷Δ₁≈T₃∷N∷Δ₄ ← ∷-cong-simp (⊢≈-trans (⊢≈-sym N∷Δ₁≈N∷Δ₂) (⊢≈-sym N∷Δ₄≈N∷Δ₂)) (ctxeq-≈ N∷Δ₁≈N∷Δ₂ (≈-trans T≈Tᵢ₁ (≈-sym T≈T₃))) 
      with r≈rᵢ ← IHr rᵢ↝ (ctxeq-tm (⊢≈-trans ≈Tᵢ₁∷N∷Δ₁ Tᵢ₁∷N∷Δ₁≈T₃∷N∷Δ₄) ⊢rᵢ)
      with Rᵢ₃ , σ≈σ₁₃ , ⊢σ₁₃ , ⊢tᵢ , N≈ ← t[σ]-inv-IH IHσ ⊢t[σᵢ₃] σᵢ₃↝ ⊢σ
      with t≈t₁ ← IHt tᵢ↝ (ctxeq-tm (⊢≈-sym Δ≈Δ₁) ⊢tᵢ) 
      = ≈-conv (≈-sym (rec-cong-simp ([]-cong-Se-simp (ctxeq-≈ N∷Δ₁≈N∷Δ₂ T≈Tᵢ) (ctxeq-s-≈ (∷-cong-simp (⊢≈-refl ⊢Γ) (N-[] ⊢σᵢ)) (q-cong σᵢ≈σ (N-wf ⊢Δ₁)))) 
                                     (≈-conv ([]-cong (≈-sym s≈sᵢ) (s-≈-conv σᵢ₁≈σ (⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₃))) (≈-sym ≈R[σᵢ₁])) 
                                     (≈-conv ([]-cong (≈-sym r≈rᵢ) (ctxeq-s-≈ (∷-cong-simp (∷-cong-simp (⊢≈-refl ⊢Γ) (N-[] ⊢σᵢ₂)) ([]-cong-Se-simp (ctxeq-≈ N∷Δ₁≈N∷Δ₂ (≈-trans T≈Tᵢ₁ (≈-sym T≈Tᵢ))) (q-cong (s-≈-trans σᵢ₂≈σ (s-≈-sym σᵢ≈σ)) (N-wf ⊢Δ₁)))) 
                                                                              (s-≈-conv (q-cong′ (q-cong σᵢ₂≈σ (N-wf ⊢Δ₁)) (ctxeq-≈ N∷Δ₁≈N∷Δ₂ T≈Tᵢ₁)) Tᵢ₁∷N∷Δ₁≈T₃∷N∷Δ₄))) (≈-sym ≈R[qqσᵢ])) 
                                     (≈-conv ([]-cong (≈-sym t≈t₁) (s-≈-conv σ≈σ₁₃ (⊢≈-sym Δ≈Δ₁))) (≈-sym  N≈)))) 
               (≈-sym ≈Tᵢ[|tᵢ[σᵢ₃]])


⫢Λ-[] : ∀ {i} →
         U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
         U.Δ′ ⫢ U.S′ ∶ Se i →
         U.S′ ∷ U.Δ′ ⫢ U.t′ ∶ U.T′ →
         --------------------
         U.Γ′ ⫢ Λ U.S′ U.t′ U.[ U.σ′ ] ≈ Λ (U.S′ U.[ U.σ′ ]) (U.t′ U.[ U.q U.S′ U.σ′ ]) ∶ Π U.S′ U.T′ U.[ U.σ′ ]
⫢Λ-[] ⫢σ′ ⫢S′ ⫢t′
  with Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHΓ , IHσ ← ⫢σ′
     | _ , Δ , S , _ , Δ↝ , S↝ , ↝Se , ⊢S , IHΔ , IHS ← ⫢S′
     | _ , _ , t , T , ↝∷ {Γ = Δ₂} {T = S₁} Δ₂↝ S₁↝ , t↝ , ↝T , ⊢t , _ , IHt ← ⫢t′
  with refl ← ⊢T:Se-lvl ⊢S
  with ⊢Γ , ⊢Δ₁ ← presup-s ⊢σ
     | ⊢Δ ← proj₁ (presup-tm ⊢S)
     | ⊢∷ ⊢Δ₂ ⊢S₁ ← proj₁ (presup-tm ⊢t)
  with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
     | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
  with refl , S≈S₁ ← IH-transform IHS S₁↝ (ctxeq-tm (⊢≈-sym Δ≈Δ₂) ⊢S₁) ⊢S 
  = _ , _ , _ , _ , _ , Γ↝ , ↝sub (↝Λ S↝ t↝) σ↝ , ↝Λ (↝sub S↝ σ↝) (↝sub t↝ (↝, (↝∘ σ↝ ↝wk) ↝v S↝)) , ↝sub (↝Π S↝ ↝T) σ↝ , 
    Λ-[] (s-conv ⊢σ (⊢≈-sym Δ≈Δ₁)) ⊢S (ctxeq-tm (∷-cong-simp (⊢≈-sym Δ≈Δ₂) (ctxeq-≈ Δ≈Δ₂ S≈S₁)) ⊢t) refl , 
    IHΓ , IHΛSt[σ] , IHΛS[σ]t[qσ]

  where
    IHΛSt[σ] : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
    IHΛSt[σ] (↝sub (↝Λ Sᵢ↝ tᵢ↝) σᵢ↝) ⊢ΛStᵢ[σ] 
      with _ , σᵢ≈σ , ⊢σᵢ , ⊢ΛSt , ≈R[σᵢ] ← t[σ]-inv-IH IHσ ⊢ΛStᵢ[σ] σᵢ↝ ⊢σ
      with _ , _ , ≈Π , refl , ⊢tᵢ ← Λ-inv′ ⊢ΛSt
      with ⊢∷ _ ⊢Sᵢ ← proj₁ (presup-tm ⊢tᵢ)
      with refl , S≈Sᵢ ← IH-transform IHS Sᵢ↝ (ctxeq-tm (⊢≈-sym Δ≈Δ₁) ⊢Sᵢ) ⊢S
      with Sᵢ∷Δ₁≈S₁∷Δ₂ ← ∷-cong-simp (⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₂) (ctxeq-≈ Δ≈Δ₁ (≈-trans S≈Sᵢ (≈-sym S≈S₁)))
      with t≈tᵢ ← IHt tᵢ↝ (ctxeq-tm Sᵢ∷Δ₁≈S₁∷Δ₂ ⊢tᵢ)
      = ≈-conv (≈-sym ([]-cong (≈-conv (Λ-cong-simp (ctxeq-≈ Δ≈Δ₁ S≈Sᵢ) (ctxeq-≈ (⊢≈-sym Sᵢ∷Δ₁≈S₁∷Δ₂) (≈-sym t≈tᵢ)) refl) (≈-sym ≈Π)) σᵢ≈σ)) (≈-sym ≈R[σᵢ])

    IHΛS[σ]t[qσ] : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
    IHΛS[σ]t[qσ] (↝Λ (↝sub {t = Sᵢ} Sᵢ↝ σᵢ↝) (↝sub tᵢ↝ (↝, {T = Sᵢ₁} (↝∘ σᵢ₁↝ ↝wk) ↝v Sᵢ₁↝))) ⊢ΛS[σ]t[qσ] 
      with _ , _ , ≈Π , refl , ⊢tᵢ[qσᵢ₁] ← Λ-inv′ ⊢ΛS[σ]t[qσ] 
      with ⊢∷ _ ⊢Sᵢ[σᵢ] ← proj₁ (presup-tm ⊢tᵢ[qσᵢ₁])
      with _ , σᵢ≈σ , ⊢σᵢ , ⊢Sᵢ , ≈R[σᵢ] ← t[σ]-inv-IH IHσ ⊢Sᵢ[σᵢ] σᵢ↝ ⊢σ
      with S≈Sᵢ ← IHS Sᵢ↝ (ctxeq-tm (⊢≈-sym Δ≈Δ₁) ⊢Sᵢ)
      with refl , ≈Se ← unique-typ ⊢S (proj₁ (proj₂ (presup-≈ S≈Sᵢ)))
      with _ , Rᵢ , ⊢qσᵢ₁ , ⊢tᵢ , ≈R[qσᵢ₁] ← t[σ]-inv ⊢tᵢ[qσᵢ₁]
      with σᵢ₁≈σ , ⊢σᵢ , ≈Sᵢ₁∷Δ₁ , ⊢Sᵢ₁ ← qσ-inv-IH IHσ ⊢qσᵢ₁ σᵢ₁↝ ⊢σ
      with S≈Sᵢ₁ ← IHS Sᵢ₁↝ (ctxeq-tm (⊢≈-sym Δ≈Δ₁) ⊢Sᵢ₁)
      with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈Sᵢ₁)))
      with Sᵢ∷Δ₁≈S₁∷Δ₂ ← ∷-cong-simp (⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₂) (ctxeq-≈ Δ≈Δ₁ (≈-trans (≈-sym S≈Sᵢ₁) (≈-sym S≈S₁)))
      with t≈tᵢ ← IHt tᵢ↝ (ctxeq-tm (⊢≈-trans ≈Sᵢ₁∷Δ₁ Sᵢ∷Δ₁≈S₁∷Δ₂) ⊢tᵢ)
      = ≈-conv (≈-sym (Λ-cong-simp (≈-conv ([]-cong (ctxeq-≈ Δ≈Δ₁ (≈-sym S≈Sᵢ)) σᵢ≈σ) (≈-sym ≈R[σᵢ])) 
        (≈-conv ([]-cong (ctxeq-≈ (⊢≈-sym Sᵢ∷Δ₁≈S₁∷Δ₂) (≈-sym t≈tᵢ)) 
                         (ctxeq-s-≈ (∷-cong-simp (⊢≈-refl ⊢Γ) ([]-cong-Se-simp (ctxeq-≈ Δ≈Δ₁ (≈-trans (≈-sym S≈Sᵢ₁) (≈-conv S≈Sᵢ (≈-sym ≈Se)))) (s-≈-trans σᵢ₁≈σ (s-≈-sym σᵢ≈σ)))) (q-cong′ σᵢ₁≈σ (ctxeq-≈ Δ≈Δ₁ (≈-sym S≈Sᵢ₁))))) 
                (≈-sym ≈R[qσᵢ₁])) refl)) (≈-sym ≈Π)

⫢$-[] : ∀ {i j} →
         U.Δ′ ⫢ U.S′ ∶ Se i →
         U.S′ ∷ U.Δ′ ⫢ U.T′ ∶ Se j →
         U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
         U.Δ′ ⫢ U.r′ ∶ Π U.S′ U.T′ →
         U.Δ′ ⫢ U.s′ ∶ U.S′ →
         --------------------
         U.Γ′ ⫢ (U.r′ $ U.s′) U.[ U.σ′ ] ≈ (U.r′ U.[ U.σ′ ]) $ (U.s′ U.[ U.σ′ ]) ∶ U.T′ U.[ U.σ′ , U.s′ U.[ U.σ′ ] ∶ U.S′ ]
⫢$-[] ⫢S′ ⫢T′ ⫢σ′ ⫢r′ ⫢s′
  with _ , Δ₁ , S , _ , Δ₁↝ , S↝ , ↝Se , ⊢S , _ , IHS ← ⫢S′
     | _ , _ , T , _ , ↝∷ {Γ = Δ₂} {T = S₁} Δ₂↝ S₁↝ , T↝ , ↝Se , ⊢T , _ , IHT ← ⫢T′
     | Γ , Δ₃ , σ , Γ↝ , Δ₃↝ , σ↝ , ⊢σ , IHΓ , IHσ ← ⫢σ′
     | _ , Δ , r , _ , Δ₄↝ , r↝ , ↝Π S₂↝ T₁↝ , ⊢r , IHΔ , IHr ← ⫢r′
     | _ , Δ₄ , s , S₃ , Δ₄↝ , s↝ , S₃↝ , ⊢s , _ , IHs ← ⫢s′
  with refl ← ⊢T:Se-lvl ⊢S
     | refl ← ⊢T:Se-lvl ⊢T
  with ⊢Δ₁ ← proj₁ (presup-tm ⊢S)
      | ⊢∷ ⊢Δ₂ ⊢S₁ ← proj₁ (presup-tm ⊢T)
      | ⊢Δ₃ ← proj₂ (presup-s ⊢σ)
      | ⊢Δ , ⊢ΠS₂T₁ ← presup-tm ⊢r
      | ⊢Δ₄ , ⊢S₃ ← presup-tm ⊢s
  with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
     | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
     | Δ≈Δ₃ ← IHΔ Δ₃↝ ⊢Δ₃
     | Δ≈Δ₄ ← IHΔ Δ₄↝ ⊢Δ₄
  with Δ₁≈Δ₂ ← ⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₂
     | Δ₄≈Δ₁ ← ⊢≈-trans (⊢≈-sym Δ≈Δ₄) Δ≈Δ₁
     | Δ₃≈Δ₄ ← ⊢≈-trans (⊢≈-sym Δ≈Δ₃) Δ≈Δ₄
  with refl , Se≈ , ⊢S₂ , ⊢T₁ ← Π-inv′ ⊢ΠS₂T₁ 
  with refl , S≈S₁ ← IH-transform IHS S₁↝ (ctxeq-tm (⊢≈-sym Δ₁≈Δ₂) ⊢S₁) ⊢S
     | refl , S≈S₂ ← IH-transform IHS S₂↝ (ctxeq-tm Δ≈Δ₁ ⊢S₂) ⊢S
     | refl , S≈S₃ ← IH-transform IHS S₃↝ (ctxeq-tm Δ₄≈Δ₁ ⊢S₃) ⊢S 
  with S₁∷Δ₂≈S₂∷Δ ← ∷-cong-simp (⊢≈-sym Δ≈Δ₂) (ctxeq-≈ Δ₁≈Δ₂ (≈-trans S≈S₁ (≈-sym S≈S₂)))
  with refl , T≈T₁ ← IH-transform IHT T₁↝ (ctxeq-tm (⊢≈-sym S₁∷Δ₂≈S₂∷Δ) ⊢T₁) ⊢T
    = _ , _ , _ , _ , _ , Γ↝ , ↝sub (↝$ r↝ s↝) σ↝ , ↝$ (↝sub r↝ σ↝) (↝sub s↝ σ↝) , ↝sub T↝ (↝, σ↝ (↝sub s↝ σ↝) S↝) , 
      $-[] (ctxeq-tm (⊢≈-sym Δ≈Δ₁) ⊢S) 
           (ctxeq-tm (∷-cong-simp (⊢≈-sym Δ≈Δ₂) (ctxeq-≈ Δ₁≈Δ₂ S≈S₁)) ⊢T) 
           (s-conv ⊢σ (⊢≈-sym Δ≈Δ₃)) 
           (conv ⊢r (Π-cong-simp (ctxeq-≈ (⊢≈-sym Δ≈Δ₁) S≈S₂) (ctxeq-≈ S₁∷Δ₂≈S₂∷Δ T≈T₁) refl)) 
           (conv (ctxeq-tm (⊢≈-sym Δ≈Δ₄) ⊢s) (ctxeq-≈ (⊢≈-sym Δ≈Δ₁) S≈S₃)) 
           refl , 
      IHΓ , IHrs[σ] , IHr[σ]s[σ]
  where
    IHrs[σ] : ∀ {r₁ i₁ T₁} → r₁ ↝ _ → Γ A.⊢ r₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ r₁ ∶[ i₁ ] T₁
    IHrs[σ] (↝sub (↝$ rᵢ↝ sᵢ↝) σᵢ↝) ⊢rᵢ$rᵢ[σ] 
      with _ , σᵢ≈σ , ⊢σᵢ , ⊢rᵢ$sᵢ , ≈Rᵢ[σᵢ] ← t[σ]-inv-IH IHσ ⊢rᵢ$rᵢ[σ] σᵢ↝ ⊢σ
      with _ , _ , Sᵢ , Tᵢ , ⊢rᵢ , ⊢sᵢ , refl , ≈Tᵢ[|sᵢ] ← $-inv ⊢rᵢ$sᵢ
      with _ , ⊢ΠSᵢTᵢ ← presup-tm ⊢rᵢ
      with _ , ⊢Sᵢ , ⊢Tᵢ ← Π-inv ⊢ΠSᵢTᵢ
      with r≈rᵢ ← IHr rᵢ↝ (ctxeq-tm (⊢≈-sym Δ≈Δ₃) ⊢rᵢ)
      with s≈sᵢ ← IHs sᵢ↝ (ctxeq-tm Δ₃≈Δ₄ ⊢sᵢ)
      = ≈-conv (≈-sym ([]-cong (≈-conv ($-cong ⊢Sᵢ ⊢Tᵢ 
                                               (ctxeq-≈ Δ≈Δ₃ (≈-sym r≈rᵢ)) 
                                               (ctxeq-≈ (⊢≈-sym Δ₃≈Δ₄) (≈-sym s≈sᵢ)) 
                                               refl) 
                                        (≈-sym ≈Tᵢ[|sᵢ])) 
                                σᵢ≈σ))
               (≈-sym ≈Rᵢ[σᵢ])

    IHr[σ]s[σ] : ∀ {r₁ i₁ T₁} → r₁ ↝ _ → Γ A.⊢ r₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ r₁ ∶[ i₁ ] T₁
    IHr[σ]s[σ] (↝$ (↝sub rᵢ↝ σᵢ↝) (↝sub sᵢ↝ σᵢ₁↝)) ⊢rᵢ[σᵢ]$sᵢ[σᵢ₁]
      with _ , _ , Sᵢ , Tᵢ , ⊢rᵢ[σᵢ] , ⊢sᵢ[σᵢ₁] , refl , ≈Tᵢ[|sᵢ[σᵢ₁]] ← $-inv ⊢rᵢ[σᵢ]$sᵢ[σᵢ₁] 
      with _ , ⊢ΠSᵢTᵢ ← presup-tm ⊢rᵢ[σᵢ]
      with _ , ⊢Sᵢ , ⊢Tᵢ ← Π-inv ⊢ΠSᵢTᵢ
      with _ , σᵢ≈σ , ⊢σᵢ , ⊢rᵢ[σᵢ] , ≈Π[σᵢ] ← t[σ]-inv-IH IHσ ⊢rᵢ[σᵢ] σᵢ↝ ⊢σ
      with _ , σᵢ₁≈σ , ⊢σᵢ₁ , ⊢sᵢ[σᵢ₁] , ≈Tᵢ[σᵢ] ← t[σ]-inv-IH IHσ ⊢sᵢ[σᵢ₁] σᵢ₁↝ ⊢σ
      with r≈rᵢ ← IHr rᵢ↝ (ctxeq-tm (⊢≈-sym Δ≈Δ₃) ⊢rᵢ[σᵢ])
      with s≈sᵢ ← IHs sᵢ↝ (ctxeq-tm Δ₃≈Δ₄ ⊢sᵢ[σᵢ₁])
      = ≈-conv (≈-sym ($-cong ⊢Sᵢ ⊢Tᵢ (≈-conv ([]-cong (≈-sym r≈rᵢ) (s-≈-conv σᵢ≈σ (⊢≈-sym Δ≈Δ₃))) (≈-sym ≈Π[σᵢ])) 
                                      (≈-conv ([]-cong (≈-sym s≈sᵢ) (s-≈-conv σᵢ₁≈σ Δ₃≈Δ₄)) (≈-sym ≈Tᵢ[σᵢ])) refl)) (≈-sym ≈Tᵢ[|sᵢ[σᵢ₁]])

  
⫢liftt-[] : ∀ {i j} →
            U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
            U.Δ′ ⫢ U.T′ ∶ Se i →
            U.Δ′ ⫢ U.t′ ∶ U.T′ →
            ------------------------
            U.Γ′ ⫢ liftt j U.t′ U.[ U.σ′ ] ≈ liftt j (U.t′ U.[ U.σ′ ]) ∶ Liftt j U.T′ U.[ U.σ′ ]
⫢liftt-[] ⫢σ′ ⫢T′ ⫢t′
  with Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHΓ , IHσ ← ⫢σ′
     | _ , Δ , T , _ , Δ↝ , T↝ , ↝Se , ⊢T , IHΔ , IHT ← ⫢T′
     | _ , Δ₂ , t , T₁ , Δ₂↝ , t↝ , T₁↝ , ⊢t , _ , IHt ← ⫢t′
  with refl ← ⊢T:Se-lvl ⊢T
  with ⊢Δ₁ ← proj₂ (presup-s ⊢σ)
     | ⊢Δ₂ , ⊢T₁ ← presup-tm ⊢t
  with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
     | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂ 
  with Δ₁≈Δ₂ ← ⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₂ 
  with refl , T≈T₁ ← IH-transform IHT T₁↝ (ctxeq-tm (⊢≈-sym Δ≈Δ₂) ⊢T₁) ⊢T
  = _ , _ , _ , _ , _ , Γ↝ , ↝sub (↝liftt t↝) σ↝ , ↝liftt (↝sub t↝ σ↝) , ↝sub (↝Liftt T↝) σ↝ , 
    liftt-[] _ ⊢σ (ctxeq-tm Δ≈Δ₁ ⊢T) (conv (ctxeq-tm (⊢≈-trans (⊢≈-sym Δ≈Δ₂) Δ≈Δ₁) ⊢t) (ctxeq-≈ Δ≈Δ₁ T≈T₁)) , 
    IHΓ , IHliftt[σ] , IHlift,t[σ]

  where
    IHliftt[σ] : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
    IHliftt[σ] (↝sub (↝liftt tᵢ↝) σᵢ↝) ⊢lifttᵢ[σᵢ] 
      with _ , σᵢ≈σ , ⊢σᵢ , ⊢lifttᵢ , ≈T[σ] ← t[σ]-inv-IH IHσ ⊢lifttᵢ[σᵢ] σᵢ↝ ⊢σ 
      with _ , Rᵢ , refl , ⊢tᵢ , ≈Liftt ← liftt-inv ⊢lifttᵢ
      with t≈tᵢ ← IHt tᵢ↝ (ctxeq-tm Δ₁≈Δ₂ ⊢tᵢ)
      = ≈-conv (≈-sym ([]-cong (≈-conv (liftt-cong _ (ctxeq-≈ (⊢≈-sym Δ₁≈Δ₂) (≈-sym t≈tᵢ))) (≈-sym ≈Liftt)) σᵢ≈σ)) (≈-sym ≈T[σ])

    IHlift,t[σ] : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
    IHlift,t[σ] (↝liftt (↝sub tᵢ↝ σᵢ↝)) ⊢lift,tᵢ[σᵢ] 
      with _ , Rᵢ , refl , ⊢tᵢ[σᵢ] , ≈Liftt ← liftt-inv ⊢lift,tᵢ[σᵢ] 
      with _ , σᵢ≈σ , ⊢σᵢ , ⊢tᵢ , ≈T[σ] ← t[σ]-inv-IH IHσ ⊢tᵢ[σᵢ] σᵢ↝ ⊢σ 
      with t≈tᵢ ← IHt tᵢ↝ (ctxeq-tm Δ₁≈Δ₂ ⊢tᵢ)
      = ≈-conv (liftt-cong _ (≈-conv (≈-sym ([]-cong (≈-sym t≈tᵢ) (s-≈-conv σᵢ≈σ Δ₁≈Δ₂))) (≈-sym ≈T[σ]))) (≈-sym ≈Liftt)

⫢unlift-[] : ∀ {i j} →
             U.Δ′ ⫢ U.T′ ∶ Se i →
             U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
             U.Δ′ ⫢ U.t′ ∶ Liftt j U.T′ →
             ---------------------------------
             U.Γ′ ⫢ unlift U.t′ U.[ U.σ′ ] ≈ unlift (U.t′ U.[ U.σ′ ]) ∶ U.T′ U.[ U.σ′ ]
⫢unlift-[] ⫢T′ ⫢σ′ ⫢t′
  with _ , Δ , T , _ , Δ₂↝ , T↝ , ↝Se , ⊢T , IHΔ , IHT ← ⫢T′
     | Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHΓ , IHσ ← ⫢σ′
     | _ , Δ₂ , t , _ , Δ₂↝ , t↝ , ↝Liftt T₁↝ , ⊢t , _ , IHt ← ⫢t′
  with refl ← ⊢T:Se-lvl ⊢T
  with ⊢Δ₁ ← proj₂ (presup-s ⊢σ)
     | ⊢Δ ← proj₁ (presup-tm ⊢T)
     | ⊢Δ₂ , ⊢LiftT₁ ← presup-tm ⊢t
  with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
     | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
  with Δ₁≈Δ₂ ← ⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₂
  with refl , ⊢T₁ , _ ← Liftt-inv′ ⊢LiftT₁
  with T≈T₁ ← IHT T₁↝ (ctxeq-tm (⊢≈-sym Δ≈Δ₂) ⊢T₁)
  with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁))) 
  = _ , _ , _ , _ , _ , Γ↝ , ↝sub (↝unlift t↝) σ↝ , ↝unlift (↝sub t↝ σ↝) , ↝sub T↝ σ↝ , 
    unlift-[] _ ⊢T (s-conv ⊢σ (⊢≈-sym Δ≈Δ₁)) (conv (ctxeq-tm (⊢≈-sym Δ≈Δ₂) ⊢t) (Liftt-cong _ (≈-sym T≈T₁))) , 
    IHΓ , IHunliftt[σ] , IHunlift,t[σ]

  where
    IHunliftt[σ] : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
    IHunliftt[σ] (↝sub (↝unlift tᵢ↝) σᵢ↝) ⊢unliftᵢ[σᵢ] 
      with _ , σᵢ≈σ , ⊢σᵢ , ⊢unliftᵢ , ≈T[σᵢ] ← t[σ]-inv-IH IHσ ⊢unliftᵢ[σᵢ] σᵢ↝ ⊢σ
      with _ , _ , Tᵢ , refl , ⊢tᵢ , ≈Tᵢ ← unlift-inv ⊢unliftᵢ
      with t≈tᵢ ← IHt tᵢ↝ (ctxeq-tm Δ₁≈Δ₂ ⊢tᵢ)
      = ≈-conv (≈-sym ([]-cong (unlift-cong _ (ctxeq-tm (⊢≈-sym Δ≈Δ₁) (proj₂ (presup-tm ⊢unliftᵢ))) (ctxeq-≈ (⊢≈-sym Δ≈Δ₂) (≈-conv (≈-sym t≈tᵢ) 
                (Liftt-cong _ (ctxeq-≈ Δ₁≈Δ₂ (≈-sym ≈Tᵢ)))))) (s-≈-conv σᵢ≈σ (⊢≈-sym Δ≈Δ₁)))) (≈-sym ≈T[σᵢ])

    IHunlift,t[σ] : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
    IHunlift,t[σ] (↝unlift (↝sub tᵢ↝ σᵢ↝)) ⊢unlift,tᵢ[σᵢ] 
      with _ , _ , Tᵢ , refl , ⊢tᵢ[σᵢ] , ≈Tᵢ ← unlift-inv ⊢unlift,tᵢ[σᵢ]
      with _ , σᵢ≈σ , ⊢σᵢ , ⊢tᵢ , ≈T[σ] ← t[σ]-inv-IH IHσ ⊢tᵢ[σᵢ] σᵢ↝ ⊢σ
      with t≈tᵢ ← IHt tᵢ↝ (ctxeq-tm Δ₁≈Δ₂ ⊢tᵢ)
      = unlift-cong _ (proj₁ (proj₂ (presup-≈ ≈Tᵢ))) 
                      (≈-conv (≈-sym ([]-cong (ctxeq-≈ (⊢≈-sym Δ≈Δ₂) (≈-sym t≈tᵢ)) 
                      (s-≈-conv σᵢ≈σ (⊢≈-sym Δ≈Δ₁)))) (≈-trans (≈-sym ≈T[σ]) (Liftt-cong _ (≈-sym ≈Tᵢ))))
  
⫢rec-β-ze : ∀ {i} →
            N ∷ U.Γ′ ⫢ U.T′ ∶ Se i →
            U.Γ′ ⫢ U.s′ ∶ U.T′ U.[| ze ∶ N ] →
            U.T′ ∷ N ∷ U.Γ′ ⫢ U.r′ ∶ U.T′ U.[ (wk ∘ wk) , su (v 1) ∶ N ] →
            --------------------
            U.Γ′ ⫢ rec U.T′ U.s′ U.r′ ze ≈ U.s′ ∶ U.T′ U.[| ze ∶ N ]
⫢rec-β-ze ⫢T′ ⫢s′ ⫢r′
  with _ , _ , T , _ , ↝∷ {Γ = Γ₁} Γ₁↝ ↝N , T↝ , ↝Se , ⊢T , _ , IHT ← ⫢T′
     | _ , Γ , s , _ , Γ↝ , s↝ , ↝sub {t = T₁} T₁↝ (↝, ↝I ↝ze ↝N) , ⊢s , IHΓ , IHs ← ⫢s′
     | _ , _ , r , _ , (↝∷ (↝∷ {Γ = Γ₂} Γ₂↝ ↝N) T₃↝) , r↝ , ↝sub {t = T₂} T₂↝ (↝, (↝∘ ↝wk ↝wk) (↝su ↝v) ↝N) , ⊢r , _ , IHr ← ⫢r′
  with ⊢∷ ⊢Γ₁ ⊢N₁ ← proj₁ (presup-tm ⊢T)
     | ⊢Γ ← proj₁ (presup-tm ⊢s)
     | ⊢∷ (⊢∷ ⊢Γ₂ ⊢N₂) ⊢T₃ ← proj₁ (presup-tm ⊢r)
  with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
     | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
  with refl ← ⊢T:Se-lvl ⊢T
     | refl ← N≈⇒eq-lvl (≈-refl ⊢N₁)
     | refl ← N≈⇒eq-lvl (≈-refl ⊢N₂)
  with N∷Γ≈N∷Γ₁ ← ∷-cong-simp (⊢≈-sym Γ≈Γ₁) (≈-refl ⊢N₁)
  with N∷Γ≈N∷Γ₂ ← ∷-cong-simp (⊢≈-sym Γ≈Γ₂) (≈-refl (N-wf ⊢Γ₂))
  with N∷Γ₁≈N∷Γ₂ ← ⊢≈-trans N∷Γ≈N∷Γ₁ (⊢≈-sym N∷Γ≈N∷Γ₂)
  with _ , refl , ⊢T₁ ← T[I,ze]-inv (proj₂ (presup-tm ⊢s))
     | _ , refl , ⊢T₂ ← T[wkwk,suv1]-inv (proj₂ (presup-tm ⊢r)) 
  with refl , T≈T₁ ← IH-transform IHT T₁↝ (ctxeq-tm (⊢≈-sym N∷Γ≈N∷Γ₁) ⊢T₁) ⊢T
     | refl , T≈T₂ ← IH-transform IHT T₂↝ (ctxeq-tm (⊢≈-sym N∷Γ₁≈N∷Γ₂) ⊢T₂) ⊢T
     | refl , T≈T₃ ← IH-transform IHT T₃↝ (ctxeq-tm (⊢≈-sym N∷Γ₁≈N∷Γ₂) ⊢T₃) ⊢T
  = _ , _ , _ , _ , _ , Γ↝ , ↝rec T↝ s↝ r↝ ↝ze , s↝ , ↝sub T↝ (↝, ↝I ↝ze ↝N) , 
    rec-β-ze (ctxeq-tm N∷Γ≈N∷Γ₁ ⊢T) 
             (conv ⊢s ([]-cong-Se′ (ctxeq-≈ N∷Γ≈N∷Γ₁ T≈T₁) (⊢I,ze ⊢Γ))) 
             (conv (ctxeq-tm (∷-cong-simp N∷Γ≈N∷Γ₂ (ctxeq-≈ N∷Γ₁≈N∷Γ₂ T≈T₃)) ⊢r) ([]-cong-Se′ (ctxeq-≈ N∷Γ≈N∷Γ₁ T≈T₂) (⊢[wk∘wk],su[v1] (⊢∷ (⊢∷ ⊢Γ (N-wf ⊢Γ)) (ctxeq-tm N∷Γ≈N∷Γ₁ ⊢T))))) , 
    IHΓ , IHrecze , IHs

  where
    IHrecze : ∀ {s₁ i₁ T₁} → s₁ ↝ _ → Γ A.⊢ s₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ s₁ ∶[ i₁ ] T₁
    IHrecze (↝rec Tᵢ↝ sᵢ↝ rᵢ↝ ↝ze) ⊢recᵢ 
      with refl , ⊢Tᵢ , ⊢sᵢ , ⊢rᵢ , ⊢tᵢ , ≈Tᵢ[|ze] ← rec-inv ⊢recᵢ
      with refl , T≈Tᵢ ← IH-transform IHT Tᵢ↝ (ctxeq-tm (⊢≈-sym N∷Γ≈N∷Γ₁) ⊢Tᵢ) ⊢T
      with s≈sᵢ ← IHs sᵢ↝ ⊢sᵢ
      with Tᵢ∷N∷Γ≈T₃∷N∷Γ₂ ← (∷-cong-simp (⊢≈-sym N∷Γ≈N∷Γ₂) (ctxeq-≈ N∷Γ≈N∷Γ₁ (≈-trans T≈Tᵢ (≈-sym T≈T₃))))
      with r≈rᵢ ← IHr rᵢ↝ (ctxeq-tm Tᵢ∷N∷Γ≈T₃∷N∷Γ₂ ⊢rᵢ)
      = ≈-conv (≈-sym (rec-cong-simp (ctxeq-≈ N∷Γ≈N∷Γ₁ T≈Tᵢ) (≈-sym s≈sᵢ) (ctxeq-≈ (⊢≈-sym Tᵢ∷N∷Γ≈T₃∷N∷Γ₂) (≈-sym r≈rᵢ)) (ze-≈ ⊢Γ))) (≈-sym ≈Tᵢ[|ze])

-- ⫢rec-β-su : ∀ {i} →
--             ⫢ U.Γ′ → -- extra condition
--             N ∷ U.Γ′ ⫢ U.T′ ∶ Se i →
--             U.Γ′ ⫢ U.s′ ∶ U.T′ U.[| ze ∶ N ] →
--             U.T′ ∷ N ∷ U.Γ′ ⫢ U.r′ ∶ U.T′ U.[ (wk ∘ wk) , su (v 1) ∶ N ] →
--             U.Γ′ ⫢ U.t′ ∶ N →
--             --------------------------------
--             U.Γ′ ⫢ rec U.T′ U.s′ U.r′ (su U.t′) ≈ U.r′ U.[ (I , U.t′ ∶ N) , rec U.T′ U.s′ U.r′ U.t′ ∶ U.T′ ] ∶ U.T′ U.[| su U.t′ ∶ N ]
-- ⫢rec-β-su ⫢Γ′ ⫢T′ ⫢s′ ⫢r′ ⫢t′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--      | _ , _ , T , _ , ↝∷ {Γ = Γ₁} Γ₁↝ ↝N , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
--      | _ , Γ₂ , s , _ , Γ₂↝ , s↝ , ↝sub {t = T₁} T₁↝ (↝, ↝I ↝ze ↝N) , ⊢s , IHs ← ⫢s′
--      | _ , _ , r , _ , (↝∷ (↝∷ {Γ = Γ₃} Γ₃↝ ↝N) T₃↝) , r↝ , ↝sub {t = T₂} T₂↝ (↝, (↝∘ ↝wk ↝wk) (↝su ↝v) ↝N) , ⊢r , IHr ← ⫢r′
--      | _ , Γ₄ , t , _ , Γ₄↝ , t↝ , ↝N , ⊢t , IHt ← ⫢t′
--   with ⊢∷ ⊢Γ₁ ⊢N₁ ← proj₁ (presup-tm ⊢T)
--      | ⊢Γ₂ ← proj₁ (presup-tm ⊢s)
--      | ⊢∷ (⊢∷ ⊢Γ₃ ⊢N₂) ⊢T₃ ← proj₁ (presup-tm ⊢r)
--      | ⊢Γ₄ ← proj₁ (presup-tm ⊢t)
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--      | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃
--      | Γ≈Γ₄ ← IHΓ Γ₄↝ ⊢Γ₄
--   with Γ₃≈Γ₁ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁
--   with N∷Γ≈N∷Γ₁ ← ∷-cong-simp (⊢≈-sym Γ≈Γ₁) (≈-refl ⊢N₁)
--   with refl ← ⊢T:Se-lvl ⊢T
--      | refl ← N≈⇒eq-lvl (≈-refl ⊢N₁)
--      | refl ← N≈⇒eq-lvl (≈-refl ⊢N₂)
--      | refl ← ⊢t∶N-lvl ⊢t
--   with _ , refl , ⊢T₁ ← T[I,ze]-inv (proj₂ (presup-tm ⊢s))
--      | _ , refl , ⊢T₂ ← T[wkwk,suv1]-inv (proj₂ (presup-tm ⊢r))
--   with T≈T₁ ← IHT T₁↝ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) (≈-refl (N-wf ⊢Γ₂))) ⊢T₁)
--      | T≈T₂ ← IHT T₂↝ (ctxeq-tm (∷-cong-simp Γ₃≈Γ₁ (≈-refl ⊢N₂)) ⊢T₂)
--      | T≈T₃ ← IHT T₃↝ (ctxeq-tm (∷-cong-simp Γ₃≈Γ₁ (≈-refl ⊢N₂)) ⊢T₃)
--   with refl , ≈Se ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
--      | refl , ≈Se₁ ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₂)))
--      | refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₃)))
--     = _ , _ , _ , _ , _ , Γ↝ , ↝rec T↝ s↝ r↝ (↝su t↝) , ↝sub r↝ (↝, (↝, ↝I t↝ ↝N) (↝rec T↝ s↝ r↝ t↝) T↝) , ↝sub T↝ (↝, ↝I (↝su t↝) ↝N) ,
--       rec-β-su (ctxeq-tm N∷Γ≈N∷Γ₁ ⊢T) (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₂) ⊢s) ([]-cong-Se′ (≈-conv (ctxeq-≈ N∷Γ≈N∷Γ₁ (≈-sym T≈T₁)) (ctxeq-≈ N∷Γ≈N∷Γ₁ (≈-sym ≈Se))) (⊢I,ze ⊢Γ)))
--         (conv (ctxeq-tm (∷-cong-simp (∷-cong-simp (⊢≈-sym Γ≈Γ₃) (≈-refl ⊢N₂)) (ctxeq-≈ (∷-cong-simp (⊢≈-sym  Γ₃≈Γ₁) (≈-refl ⊢N₁)) (≈-sym T≈T₃))) ⊢r) ([]-cong-Se′ (≈-conv (ctxeq-≈ N∷Γ≈N∷Γ₁ (≈-sym T≈T₂)) (≈-sym (ctxeq-≈ N∷Γ≈N∷Γ₁ ≈Se₁))) (⊢[wk∘wk],su[v1] (⊢∷ (⊢∷ ⊢Γ (N-wf ⊢Γ)) (ctxeq-tm N∷Γ≈N∷Γ₁ ⊢T))))) (ctxeq-tm (⊢≈-sym Γ≈Γ₄) ⊢t)

-- ⫢Λ-β : ∀ {i j} →
--         ⫢ U.Γ′ → -- extra condition
--         U.Γ′ ⫢ U.S′ ∶ Se i →
--         U.S′ ∷ U.Γ′ ⫢ U.T′ ∶ Se j →
--         U.S′ ∷ U.Γ′ ⫢ U.t′ ∶ U.T′ →
--         U.Γ′ ⫢ U.s′ ∶ U.S′ →
--         --------------------
--         U.Γ′ ⫢ (Λ U.S′ U.t′) $ U.s′ ≈ U.t′ U.[| U.s′ ∶ U.S′ ] ∶ U.T′ U.[| U.s′ ∶ U.S′ ]
-- ⫢Λ-β ⫢Γ′ ⫢S′ ⫢T′ ⫢t′ ⫢s′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--      | _ , Γ₁ , S , _ , Γ₁↝ , S↝ , ↝Se , ⊢S , IHS ← ⫢S′
--      | _ , _ , T , _ , ↝∷ {Γ = Γ₂} {T = S₁} Γ₂↝ S₁↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
--      | j , _ , t , T₁ , ↝∷ {Γ = Γ₃} {T = S₂} Γ₃↝ S₂↝ , t↝ , T₁↝ , ⊢t , IHt ← ⫢t′
--      | i , Γ₄ , s , S₃ , Γ₄↝ , s↝ , S₃↝ , ⊢s , IHs ← ⫢s′
--   with refl ← ⊢T:Se-lvl ⊢S
--      | refl ← ⊢T:Se-lvl ⊢T
--   with ⊢Γ₁ ← proj₁ (presup-tm ⊢S)
--      | ⊢∷ ⊢Γ₂ ⊢S₁ ← proj₁ (presup-tm ⊢T)
--      | ⊢∷ ⊢Γ₃ ⊢S₂ , ⊢T₁ ← presup-tm ⊢t
--      | ⊢Γ₄ , ⊢S₃ ← presup-tm ⊢s
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--      | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃
--      | Γ≈Γ₄ ← IHΓ Γ₄↝ ⊢Γ₄
--   with Γ₁≈Γ₂ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₁) Γ≈Γ₂
--      | Γ₃≈Γ₁ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁
--   with S≈S₁ ← IHS S₁↝ (ctxeq-tm (⊢≈-sym Γ₁≈Γ₂) ⊢S₁)
--      | S≈S₂ ← IHS S₂↝ (ctxeq-tm Γ₃≈Γ₁ ⊢S₂)
--      | S≈S₃ ← IHS S₃↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₄) Γ≈Γ₁) ⊢S₃)
--   with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
--      | refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₂)))
--      | refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₃)))
--   with T≈T₁ ← IHT T₁↝ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₂) (ctxeq-≈ (⊢≈-sym Γ₃≈Γ₁) (≈-trans (≈-sym S≈S₂) S≈S₁))) ⊢T₁)
--   with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
--     = _ , _ , _ , _ , _ , Γ↝ , ↝$ (↝Λ S↝ t↝) s↝ , ↝sub t↝ (↝, ↝I s↝ S↝) , ↝sub T↝ (↝, ↝I s↝ S↝) ,
--       Λ-β (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S)
--           (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (ctxeq-≈ Γ₁≈Γ₂ (≈-sym S≈S₁))) ⊢T)
--           (conv (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₃) (ctxeq-≈ (⊢≈-sym Γ₃≈Γ₁) (≈-sym S≈S₂))) ⊢t) (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (ctxeq-≈ Γ₁≈Γ₂ (≈-sym S≈S₁))) (≈-sym T≈T₁)))
--           (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₄) ⊢s) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S≈S₃)))

-- ⫢Λ-η : ∀ {i j} →
--         ⫢ U.Γ′ → -- extra condition
--         U.Γ′ ⫢ U.S′ ∶ Se i →
--         U.S′ ∷ U.Γ′ ⫢ U.T′ ∶ Se j →
--         U.Γ′ ⫢ U.t′ ∶ Π U.S′ U.T′ →
--         --------------------
--         U.Γ′ ⫢ U.t′ ≈ Λ U.S′ (U.t′ U.[ wk ] $ v 0) ∶ Π U.S′ U.T′
-- ⫢Λ-η ⫢Γ′ ⫢S′ ⫢T′ ⫢t′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--      | _ , Γ₁ , S , _ , Γ₁↝ , S↝ , ↝Se , ⊢S , IHS ← ⫢S′
--      | _ , _ , T , _ , ↝∷ {Γ = Γ₂} {T = S₁} Γ₂↝ S₁↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
--      | _ , Γ₃ , t , _ , Γ₃↝ , t↝ , ↝Π S₂↝ T₁↝ , ⊢t , IHt ← ⫢t′
--   with refl ← ⊢T:Se-lvl ⊢S
--      | refl ← ⊢T:Se-lvl ⊢T
--   with ⊢Γ₁ ← proj₁ (presup-tm ⊢S)
--      | ⊢∷ ⊢Γ₂ ⊢S₁ ← proj₁ (presup-tm ⊢T)
--      | ⊢Γ₃ , ⊢ΠS₂T₁ ← presup-tm ⊢t
--   with refl , ⊢S₂ , ⊢T₁ ← Π-inv ⊢ΠS₂T₁
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--      | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃
--   with Γ₁≈Γ₂ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₁) Γ≈Γ₂
--      | Γ₃≈Γ₁ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁
--   with S≈S₁ ← IHS S₁↝ (ctxeq-tm (⊢≈-sym Γ₁≈Γ₂) ⊢S₁)
--      | S≈S₂ ← IHS S₂↝ (ctxeq-tm Γ₃≈Γ₁ ⊢S₂)
--   with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
--      | refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₂)))
--   with T≈T₁ ← IHT T₁↝ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₂) (ctxeq-≈ (⊢≈-sym Γ₃≈Γ₁) (≈-trans (≈-sym S≈S₂) S≈S₁))) ⊢T₁)
--   with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
--     = _ , _ , _ , _ , _ , Γ↝ , t↝ , ↝Λ S↝ (↝$ (↝sub t↝ ↝wk) ↝v) , ↝Π S↝ T↝ ,
--       Λ-η (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S) (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (ctxeq-≈ Γ₁≈Γ₂ (≈-sym S≈S₁))) ⊢T)
--           (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₃) ⊢t)
--                 (Π-cong (ctxeq-tm (⊢≈-sym Γ≈Γ₃) ⊢S₂) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S≈S₂)) (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (ctxeq-≈ Γ₁≈Γ₂ (≈-trans (≈-sym S≈S₁) S≈S₂)))
--                         (≈-sym T≈T₁)) refl)) refl

-- ⫢L-β : ∀ {j} →
--        U.Γ′ ⫢ U.t′ ∶ U.T′ →
--        -----------------------------
--        U.Γ′ ⫢ unlift (liftt j U.t′) ≈ U.t′ ∶ U.T′
-- ⫢L-β ⫢t′
--   with _ , Γ , t , T , Γ↝ , t↝ , T↝ , ⊢t , IHt ← ⫢t′
--     = _ , _ , _ , _ , _ , Γ↝ , ↝unlift (↝liftt t↝) , t↝ , T↝ , L-β _ ⊢t

-- ⫢L-η : ∀ {i j} →
--        ⫢ U.Γ′ →
--        U.Γ′ ⫢ U.T′ ∶ Se i →
--        U.Γ′ ⫢ U.t′ ∶ Liftt j U.T′ →
--        -----------------------------
--        U.Γ′ ⫢ U.t′ ≈ liftt j (unlift U.t′) ∶ Liftt j U.T′
-- ⫢L-η ⫢Γ′ ⫢T′ ⫢t′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--      | _ , Γ₁ , T , _ , Γ₁↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
--      | _ , Γ₂ , t , _ , Γ₂↝ , t↝ , ↝Liftt T₁↝ , ⊢t , IHt ← ⫢t′
--   with refl ← ⊢T:Se-lvl ⊢T
--   with ⊢Γ₁ ← proj₁ (presup-tm ⊢T)
--      | ⊢Γ₂ , ⊢LiftT₁ ← presup-tm ⊢t
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--   with refl , ⊢T₁ ← Liftt-inv ⊢LiftT₁
--   with T≈T₁ ← IHT T₁↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) ⊢T₁)
--   with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
--      = _ , _ , _ , _ , _ , Γ↝ , t↝ , ↝liftt (↝unlift t↝) , ↝Liftt T↝ , L-η _ (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢T) (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₂) ⊢t) (Liftt-cong _ (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym T≈T₁))))

-- ⫢[I] : U.Γ′ ⫢ U.t′ ∶ U.T′ →
--        ---------------------
--        U.Γ′ ⫢ U.t′ U.[ I ] ≈ U.t′ ∶ U.T′
-- ⫢[I] ⫢t′
--   with _ , Γ , t , T , Γ↝ , t↝ , T↝ , ⊢t , IHt ← ⫢t′
--     = _ , _ , _ , _ , _ , Γ↝ , ↝sub t↝ ↝I , t↝ , T↝ , [I] ⊢t

-- ⫢[wk] : ∀ {i x} →
--         ⫢ U.Γ′ →
--         U.Γ′ ⫢ U.S′ ∶ Se i →
--         x ∶ U.T′ ∈! U.Γ′ →
--         ---------------------
--         U.S′ ∷ U.Γ′ ⫢ v x U.[ wk ] ≈ v (1 + x) ∶ U.T′ U.[ wk ]
-- ⫢[wk] ⫢Γ′ ⫢S′ x∈Γ′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--      | _ , Γ₁ , S , _ , Γ₁↝ , S↝ , ↝Se , ⊢S , IHS ← ⫢S′
--   with refl ← ⊢T:Se-lvl ⊢S
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ (proj₁ (presup-tm ⊢S))
--   with i , T , T↝ , x∈Γ ← U⇒A-vlookup Γ↝ x∈Γ′
--     = _ , _ , _ , _ , _ , ↝∷ Γ↝ S↝ , ↝sub ↝v ↝wk , ↝v , ↝sub T↝ ↝wk , [wk] ⊢Γ (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S) x∈Γ

-- ⫢[∘]  : ⫢ U.Ψ′ → -- extra condition
--         ⫢ U.Δ′ → -- extra condition
--         U.Γ′ ⫢s U.τ′ ∶ U.Ψ′ →
--         U.Ψ′ ⫢s U.σ′ ∶ U.Δ′ →
--         U.Δ′ ⫢ U.t′ ∶ U.T′ →
--         ---------------------
--         U.Γ′ ⫢ U.t′ U.[ U.σ′ ∘ U.τ′ ] ≈ U.t′ U.[ U.σ′ ] U.[ U.τ′ ] ∶ U.T′ U.[ U.σ′ ∘ U.τ′ ]
-- ⫢[∘] ⫢Ψ′ ⫢Δ′ ⫢τ′ ⫢σ′ ⫢t′
--   with Ψ , ⊢Ψ , Ψ↝ , IHΨ ← ⫢Ψ′
--      | Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
--      | Γ , Ψ₁ , τ , Γ↝ , Ψ₁↝ , τ↝ , ⊢τ , IHτ ← ⫢τ′
--      | Ψ₂ , Δ₁ , σ , Ψ₂↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
--      | i , Δ₂ , t , T , Δ₂↝ , t↝ , T↝ , ⊢t , IHT ← ⫢t′
--   with ⊢Ψ₁ ← proj₂ (presup-s ⊢τ)
--      | ⊢Ψ₂ , ⊢Δ₁ ← presup-s ⊢σ
--      | ⊢Δ₂ ← proj₁ (presup-tm ⊢t)
--   with Ψ≈Ψ₁ ← IHΨ Ψ₁↝ ⊢Ψ₁
--      | Ψ≈Ψ₂ ← IHΨ Ψ₂↝ ⊢Ψ₂
--   with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
--      | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
--     = _ , _ , _ , _ , _ , Γ↝ , ↝sub t↝ (↝∘ σ↝ τ↝) , ↝sub (↝sub t↝ σ↝) τ↝ , ↝sub T↝ (↝∘ σ↝ τ↝) , [∘] ⊢τ (ctxeq-s (⊢≈-trans (⊢≈-sym Ψ≈Ψ₂) Ψ≈Ψ₁) ⊢σ) (ctxeq-tm (⊢≈-trans (⊢≈-sym Δ≈Δ₂) Δ≈Δ₁) ⊢t)

-- ⫢[,]-v-ze : ∀ {i} →
--             U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--             U.Δ′ ⫢ U.S′ ∶ Se i →
--             U.Γ′ ⫢ U.s′ ∶ U.S′ U.[ U.σ′ ] →
--             ---------------------
--             U.Γ′ ⫢ v 0 U.[ U.σ′ , U.s′ ∶ U.S′ ] ≈ U.s′ ∶ U.S′ U.[ U.σ′ ]
-- ⫢[,]-v-ze ⫢σ ⫢S′ ⫢s′
--   with Γ₁ , Δ₁ , σ , Γ₁↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ
--      | _ , Δ₂ , S , _ , Δ₂↝ , S↝ , ↝Se , ⊢S , IHS ← ⫢S′
--      | i , Γ₂ , s , _ , Γ₂↝ , s↝ , ↝sub {t = S₁} S₁↝ σ₁↝ , ⊢s , IHs ← ⫢s′
--   with refl ← ⊢T:Se-lvl ⊢S
--   with ⊢Γ₁ , ⊢Δ₁ ← presup-s ⊢σ
--      | ⊢Γ₂ , ⊢S₁[σ₁] ← presup-tm ⊢s
--      | ⊢Δ₂ ← proj₁ (presup-tm ⊢S)
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--      | Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
--      | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
--   with Δ₃ , _ , ⊢σ₁ , ⊢S₁ , _ ← t[σ]-inv ⊢S₁[σ₁]
--   with σ≈σ₁ ← IHσ σ₁↝ (ctxeq-s (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) ⊢σ₁)
--   with Δ₁≈Δ₃ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σ₁)))
--   with Δ₃≈Δ₂ ← (⊢≈-trans (⊢≈-sym Δ₁≈Δ₃) (⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₂))
--   with S≈S₁ ← IHS S₁↝ (ctxeq-tm Δ₃≈Δ₂ ⊢S₁)
--   with refl , ≈Se ← unique-typ ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
--     = _ , _ , _ , _ , _ , Γ↝ , ↝sub ↝v (↝, σ↝ s↝ S↝) , s↝ , ↝sub S↝ σ↝ ,
--       [,]-v-ze (s-conv (ctxeq-s (⊢≈-sym Γ≈Γ₁) ⊢σ) (⊢≈-sym Δ≈Δ₁))
--                (ctxeq-tm (⊢≈-sym Δ≈Δ₂) ⊢S)
--                (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₂) ⊢s) ([]-cong-Se-simp (ctxeq-≈ (⊢≈-sym Δ₃≈Δ₂) (≈-conv (≈-sym S≈S₁) (≈-sym ≈Se))) (ctxeq-s-≈ (⊢≈-sym Γ≈Γ₁) (s-≈-sym σ≈σ₁))))

-- ⫢[,]-v-su : ∀ {i x} →
--             U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--             U.Δ′ ⫢ U.S′ ∶ Se i →
--             U.Γ′ ⫢ U.s′ ∶ U.S′ U.[ U.σ′ ] →
--             x ∶ U.T′ ∈! U.Δ′ →
--             ---------------------
--             U.Γ′ ⫢ v (1 + x) U.[ U.σ′ , U.s′ ∶ U.S′ ] ≈ v x U.[ U.σ′ ] ∶ U.T′ U.[ U.σ′ ]
-- ⫢[,]-v-su ⫢σ ⫢S′ ⫢s′ x∈Δ′
--   with Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHΓ , IHσ ← ⫢σ
--      | _ , Δ , S , _ , Δ↝ , S↝ , ↝Se , ⊢S , IHΔ , IHS ← ⫢S′
--      | i , Γ₁ , s , _ , Γ₁↝ , s↝ , ↝sub {t = S₁} S₁↝ σ₁↝ , ⊢s , _ , IHs ← ⫢s′
--   with refl ← ⊢T:Se-lvl ⊢S
--   with ⊢Γ , ⊢Δ₁ ← presup-s ⊢σ
--      | ⊢Γ₁ , ⊢S₁[σ₁] ← presup-tm ⊢s
--      | ⊢Δ ← proj₁ (presup-tm ⊢S)
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
--   with Δ₃ , _ , ⊢σ₁ , ⊢S₁ , _ ← t[σ]-inv ⊢S₁[σ₁]
--   with σ≈σ₁ ← IHσ σ₁↝ (ctxeq-s (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) ⊢σ₁)
--   with Δ₁≈Δ₃ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σ₁)))
--   with Δ₃≈Δ₂ ← (⊢≈-trans (⊢≈-sym Δ₁≈Δ₃) (⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₂))
--   with S≈S₁ ← IHS S₁↝ (ctxeq-tm Δ₃≈Δ₂ ⊢S₁)
--   with refl , ≈Se ← unique-typ ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
--   with j , T , T↝ , x∈Δ ← U⇒A-vlookup Δ↝ x∈Δ′
--     = _ , _ , _ , _ , _ , Γ↝ , ↝sub ↝v (↝, σ↝ s↝ S↝) , ↝sub ↝v σ↝ , ↝sub T↝ σ↝ ,
--         [,]-v-su (s-conv (ctxeq-s (⊢≈-sym Γ≈Γ₁) ⊢σ) (⊢≈-sym Δ≈Δ₁)) (ctxeq-tm (⊢≈-sym Δ≈Δ₂) ⊢S)
--         (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₂) ⊢s) ([]-cong-Se-simp (ctxeq-≈ (⊢≈-sym Δ₃≈Δ₂) (≈-conv (≈-sym S≈S₁) (≈-sym ≈Se))) (ctxeq-s-≈ (⊢≈-sym Γ≈Γ₁) (s-≈-sym σ≈σ₁))))
--         x∈Δ

-- ⫢≈-conv : ∀ {i} →
--           U.Γ′ ⫢ U.s′ ≈ U.t′ ∶ U.S′ →
--           U.Γ′ ⫢ U.S′ ≈ U.T′ ∶ Se i →
--           ---------------------
--           U.Γ′ ⫢ U.s′ ≈ U.t′ ∶ U.T′
-- ⫢≈-conv s′≈t′ S′≈T′
--   with _ , Γ , s , t , S , Γ↝ , s↝ , t↝ , S₁↝ , s≈t , IHΓ , IHs , IHt ← s′≈t′
--      | _ , Γ₁ , S , T , _ , Γ↝ , S↝ , T↝ , ↝Se , S≈T , IHΓ , IHS , IHT ← S′≈T′
--   with refl ← ⊢T:Se-lvl ⊢S
--   with ⊢Γ₁ ← proj₁ (presup-tm ⊢S)
--      | ⊢Γ₂ , ⊢s , ⊢t , ⊢S₁ ← presup-≈ s≈t
--      | ⊢Γ₃ , ⊢S₂ , ⊢T , _ ← presup-≈ S≈T
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--      | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃
--   with S≈S₁ ← IHS S₁↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) ⊢S₁)
--      | S≈S₂ ← IHS S₂↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁) ⊢S₂)
--   with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
--      | refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₂)))
--     = _ , _ , _ , _ , _ , Γ↝ , s↝ , t↝ , T↝ , ≈-conv (≈-conv (ctxeq-≈ (⊢≈-sym Γ≈Γ₂) s≈t) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S≈S₁))) (≈-trans (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) S≈S₂) (ctxeq-≈ (⊢≈-sym Γ≈Γ₃) S≈T))

-- ⫢≈-sym : U.Γ′ ⫢ U.s′ ≈ U.t′ ∶ U.S′ →
--          ---------------------
--          U.Γ′ ⫢ U.t′ ≈ U.s′ ∶ U.S′
-- ⫢≈-sym s′≈t′
--   with _ , Γ , s , t , S , Γ↝ , s↝ , t↝ , S↝ , s≈t ← s′≈t′
--     = _ , _ , _ , _ , _ , Γ↝ , t↝ , s↝ , S↝ , ≈-sym s≈t

-- ⫢≈-trans : ⫢ U.Γ′ → -- extra condition
--            U.Γ′ ⫢ U.s′ ≈ U.t′ ∶ U.S′ →
--            U.Γ′ ⫢ U.t′ ≈ U.r′ ∶ U.S′ →
--            ---------------------
--            U.Γ′ ⫢ U.s′ ≈ U.r′ ∶ U.S′
-- ⫢≈-trans s′≈t′ t′≈r′
--   with _ , Γ , s , t , S , Γ↝ , s↝ , t↝ , S↝ , s≈t , IHΓ , IHs , IHt ← s′≈t′
--      | _ , Γ₁ , t₁ , r , S₁ , Γ₁↝ , t₁↝ , r↝ , S₁↝ , t≈r , _ , _ , IHr ← t′≈r′
--   with ⊢Γ , ⊢s , ⊢t₁ , ⊢S ← presup-≈ s≈t
--      | ⊢Γ₁ , ⊢t₂ , ⊢r , ⊢S₁ ← presup-≈ t≈r
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--   with t≈t₁ ← IHt t₁↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) ⊢t₁)
--      | t≈t₂ ← IHt t₂↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁) ⊢t₂)
--   with refl , S≈S₁ ← unique-typ ⊢t (proj₁ (proj₂ (presup-≈ t≈t₁)))
--      | refl , S≈S₂ ← unique-typ ⊢t (proj₁ (proj₂ (presup-≈ t≈t₂)))
--   with t₁≈t₂ ← ≈-trans (≈-sym t≈t₁) (≈-conv t≈t₂ (≈-trans (≈-sym S≈S₂) S≈S₁))
--     = _ , _ , _ , _ , _ , Γ↝ , s↝ , r↝ , S↝ ,
--       ≈-trans (≈-conv (ctxeq-≈ (⊢≈-sym Γ≈Γ₂) s≈t) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S≈S₁))) (≈-trans (≈-conv (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) t₁≈t₂) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S≈S₁))) (≈-conv (ctxeq-≈ (⊢≈-sym Γ≈Γ₃) t≈r) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S≈S₂))))

-- ⫢I-≈ : ⫢ U.Γ′ →
--        ----------------
--         U.Γ′ ⫢s I ≈ I ∶ U.Γ′
-- ⫢I-≈ ⫢Γ′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--     = _ , _ , _ , _ , Γ↝ , Γ↝ , ↝I , ↝I , I-≈ ⊢Γ

-- ⫢wk-≈ : ⫢ U.S′ ∷ U.Γ′ →
--         ---------------------
--         U.S′ ∷ U.Γ′ ⫢s wk ≈ wk ∶ U.Γ′
-- ⫢wk-≈ ⫢S∷Γ′
--   with Γ , ⊢S∷Γ , S∷Γ↝@(↝∷ Γ↝ S↝) , IHΓ ← ⫢S∷Γ′ = _ , _ , _ , _ , S∷Γ↝ , Γ↝ , ↝wk , ↝wk , wk-≈ ⊢S∷Γ

-- ⫢∘-cong : ∀ {σ₁′ σ₂′ τ₁′ τ₂′} →
--           ⫢ U.Ψ′ → -- extra condition
--           U.Γ′ ⫢s τ₁′ ≈ τ₂′ ∶ U.Ψ′ →
--           U.Ψ′ ⫢s σ₁′ ≈ σ₂′ ∶ U.Δ′ →
--           ---------------------
--           U.Γ′ ⫢s σ₁′ ∘ τ₁′ ≈ σ₂′ ∘ τ₂′ ∶ U.Δ′
-- ⫢∘-cong ⫢Ψ′ τ₁′≈τ₂′ σ₁′≈σ₂′
--   with Ψ , ⊢Ψ , Ψ↝ , IHΨ ← ⫢Ψ′
--      | Γ , Ψ₁ , τ₁ , τ₂ , Γ↝ , Ψ₁↝ , τ₁↝ , τ₂↝ , τ₁≈τ₂ ← τ₁′≈τ₂′
--      | Ψ₂ , Δ , σ₁ , σ₂ , Ψ₂↝ , Δ↝ , σ₁↝ , σ₂↝ , σ₁≈σ₂ ← σ₁′≈σ₂′
--   with Ψ≈Ψ₁ ← IHΨ Ψ₁↝ (proj₂ (proj₂ (proj₂ (presup-s-≈ τ₁≈τ₂))))
--      | Ψ≈Ψ₂ ← IHΨ Ψ₂↝ (proj₁ (presup-s-≈ σ₁≈σ₂))
--   = _ , _ , _ , _ , Γ↝ , Δ↝ , ↝∘ σ₁↝ τ₁↝ , ↝∘ σ₂↝ τ₂↝ , ∘-cong (s-≈-conv τ₁≈τ₂ (⊢≈-sym Ψ≈Ψ₁)) (ctxeq-s-≈ (⊢≈-sym Ψ≈Ψ₂) σ₁≈σ₂)

⫢,-cong : ∀ {i σ₁′ σ₂′ t₁′ t₂′ T₁′ T₂′ } →
          U.Γ′ ⫢s σ₁′ ≈ σ₂′ ∶ U.Δ′ →
          U.Δ′ ⫢ T₁′ ∶ Se i →
          U.Δ′ ⫢ T₁′ ≈ T₂′ ∶ Se i →
          U.Γ′ ⫢ t₁′ ≈ t₂′ ∶ T₁′ U.[ σ₁′ ] →
          ----------------------
          U.Γ′ ⫢s (σ₁′ , t₁′ ∶ T₁′) ≈ (σ₂′ , t₂′ ∶ T₂′) ∶ T₁′ ∷ U.Δ′
⫢,-cong σ₁′≈σ₂′ _ T₁′≈T₂′ t₁′≈t₂′
  with Γ , Δ₁ , σ₁₁ , σ₂ , Γ↝ , Δ₁↝ , σ₁₁↝ , σ₂₁↝ , σ₁₁≈σ₂₁ , IHΓ , IHσ₁ , IHσ₂  ← σ₁′≈σ₂′
     | _ , Δ , T₁₁ , T₂₁ , _ , Δ↝ , T₁₁↝ , T₂₁↝ , ↝Se , T₁≈T₂ , IHΔ , IHT₁ , IHT₂ ← T₁′≈T₂′
     | i , Γ₁ , t₁ , t₂ , _ , Γ₁↝ , t₁↝ , t₂↝ , ↝sub {t = T₁₂} {σ = σ₁₂} T₁₂↝ σ₁₂↝ , t₁≈t₂ , _ , IHt₁ , IHt₂ ← t₁′≈t₂′
  with ⊢Γ , ⊢σ₁₁ , ⊢σ₂₁ , ⊢Δ₁ ← presup-s-≈ σ₁₁≈σ₂₁
     | ⊢Δ , ⊢T₁₁ , ⊢T₂₁ , _ ← presup-≈ T₁≈T₂
     | ⊢Γ₁ , ⊢t₁ , ⊢t₂ , ⊢T₁₂[σ₁₂] ← presup-≈ t₁≈t₂
  with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
     | Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
  with _ , σ₁₂≈ , ⊢σ₁₂ , ⊢T₁₂ , _ ← t[σ]-inv-IH IHσ₁ (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢T₁₂[σ₁₂]) σ₁₂↝ ⊢σ₁₁ 
  with σ≈σ₁₂ ← IHσ₁ σ₁₂↝ ⊢σ₁₂
  with refl , T₁₁≈T₁₂ ← IH-transform IHT₁ T₁₂↝ (ctxeq-tm (⊢≈-sym Δ≈Δ₁) ⊢T₁₂) ⊢T₁₁
  with refl ← ⊢T≈S:Se-lvl T₁₁≈T₁₂
  = _ , _ , _ , _ , Γ↝ , ↝∷ Δ↝ T₁₁↝ , ↝, σ₁₁↝ t₁↝ T₁₁↝ , ↝, σ₂₁↝ t₂↝ T₂₁↝ , 
    ,-cong (s-≈-conv σ₁₁≈σ₂₁ (⊢≈-sym Δ≈Δ₁)) ⊢T₁₁ T₁≈T₂ 
           (≈-conv (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) t₁≈t₂) ([]-cong-Se-simp T₁₁≈T₁₂ (s-≈-conv (s-≈-sym  σ≈σ₁₂) (⊢≈-sym Δ≈Δ₁)))) , 
    IHΓ , IHσ₁,t₁ , IHσ₂,t₂

  where
    IHσ₁,t₁ : (∀ {σᵢ Δᵢ} → σᵢ ↝s _ → Γ A.⊢s σᵢ ∶ Δᵢ → Γ A.⊢s _ ≈ σᵢ ∶ Δᵢ)
    IHσ₁,t₁ (↝, {σ = σᵢ} {t = tᵢ} σᵢ↝ tᵢ↝ Tᵢ↝) ⊢σᵢ,tᵢ 
      with σ≈σᵢ , ⊢σᵢ , ⊢tᵢ , T∷Δ₁≈ ← ,-inv-IH IHσ₁ ⊢σᵢ,tᵢ σᵢ↝ ⊢σ₁₁
      with ⊢∷ _ ⊢Tᵢ , _ ← presup-⊢≈ T∷Δ₁≈
      with T₁≈Tᵢ ← IHT₁ Tᵢ↝ (ctxeq-tm (⊢≈-sym Δ≈Δ₁) ⊢Tᵢ)
      with Δ₁⊢T₁≈Tᵢ ← ctxeq-≈ Δ≈Δ₁ (≈-sym T₁≈Tᵢ)
      with t₁≈tᵢ ← IHt₁ tᵢ↝ (ctxeq-tm Γ≈Γ₁ ⊢tᵢ)
      with refl , ≈T ← unique-typ ⊢t₁ (proj₁ (proj₂ (presup-≈ t₁≈tᵢ)))
      = s-≈-conv (s-≈-sym (,-cong σ≈σᵢ ⊢Tᵢ Δ₁⊢T₁≈Tᵢ (≈-conv (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym t₁≈tᵢ)) ([]-cong-Se‴ ⊢Tᵢ (s-≈-sym σ≈σᵢ))))) T∷Δ₁≈

    IHσ₂,t₂ : (∀ {σᵢ Δᵢ} → σᵢ ↝s _ → Γ A.⊢s σᵢ ∶ Δᵢ → Γ A.⊢s _ ≈ σᵢ ∶ Δᵢ)
    IHσ₂,t₂ (↝, {σ = σᵢ} {t = tᵢ} σᵢ↝ tᵢ↝ Tᵢ↝) ⊢σᵢ,tᵢ 
      with σ≈σᵢ , ⊢σᵢ , ⊢tᵢ , T∷Δ₁≈ ← ,-inv-IH IHσ₂ ⊢σᵢ,tᵢ σᵢ↝ ⊢σ₂₁
      with ⊢∷ _ ⊢Tᵢ , _ ← presup-⊢≈ T∷Δ₁≈
      with T₂≈Tᵢ ← IHT₂ Tᵢ↝ (ctxeq-tm (⊢≈-sym Δ≈Δ₁) ⊢Tᵢ)
      with Δ₁⊢T₂≈Tᵢ ← ctxeq-≈ Δ≈Δ₁ (≈-sym T₂≈Tᵢ)
      with t₂≈tᵢ ← IHt₂ tᵢ↝ (ctxeq-tm Γ≈Γ₁ ⊢tᵢ)
      with refl , ≈T ← unique-typ ⊢t₂ (proj₁ (proj₂ (presup-≈ t₂≈tᵢ)))
      = s-≈-conv (s-≈-sym (,-cong σ≈σᵢ ⊢Tᵢ Δ₁⊢T₂≈Tᵢ (≈-conv (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym t₂≈tᵢ)) ([]-cong-Se‴ ⊢Tᵢ (s-≈-sym σ≈σᵢ))))) T∷Δ₁≈

-- ⫢I-∘ : U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--        ---------------------
--        U.Γ′ ⫢s I ∘ U.σ′ ≈ U.σ′ ∶ U.Δ′
-- ⫢I-∘ ⫢σ′
--   with Γ , Δ , σ , Γ↝ , Δ↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
--     = _ , _ , _ , _ , Γ↝ , Δ↝ , ↝∘ ↝I σ↝ , σ↝ , I-∘ ⊢σ

-- ⫢∘-I : U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--        ---------------------
--        U.Γ′ ⫢s U.σ′ ∘ I ≈ U.σ′ ∶ U.Δ′
-- ⫢∘-I ⫢σ′
--   with Γ , Δ , σ , Γ↝ , Δ↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
--     = _ , _ , _ , _ , Γ↝ , Δ↝ , ↝∘ σ↝ ↝I , σ↝ , ∘-I ⊢σ

-- ⫢∘-assoc : ∀ {ζ′ Ω′} →
--            U.Ψ′ ⫢s ζ′ ∶ Ω′ →
--            U.Δ′ ⫢s U.τ′ ∶ U.Ψ′ →
--            U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--            ---------------------
--            U.Γ′ ⫢s (ζ′ ∘ U.τ′) ∘ U.σ′ ≈ ζ′ ∘ (U.τ′ ∘ U.σ′) ∶ Ω′
-- ⫢∘-assoc ⫢ζ′ ⫢τ′ ⫢σ′
--   with Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
--      | Δ₂ , Ψ₁ , τ , Δ₂↝ , Ψ₁↝ , τ↝ , ⊢τ , IHτ ← ⫢τ′
--      | Ψ₂ , Ω , ζ , Ψ₂↝ , Ω↝ , ζ↝ , ⊢ζ , IHζ ← ⫢ζ′
--   with ⊢Δ₁ ← proj₂ (presup-s ⊢σ)
--      | ⊢Δ₂ , ⊢Ψ₁ ← presup-s ⊢τ
--      | ⊢Ψ₂ ← proj₁ (presup-s ⊢ζ)
--   with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
--      | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
--      | Ψ≈Ψ₁ ← IHΨ Ψ₁↝ ⊢Ψ₁
--      | Ψ≈Ψ₂ ← IHΨ Ψ₂↝ ⊢Ψ₂
--     = _ , _ , _ , _ , Γ↝ , Ω↝ , ↝∘ (↝∘ ζ↝ τ↝) σ↝ , ↝∘ ζ↝ (↝∘ τ↝ σ↝) ,
--       ∘-assoc (ctxeq-s (⊢≈-trans (⊢≈-sym Ψ≈Ψ₂) Ψ≈Ψ₁) ⊢ζ) (ctxeq-s (⊢≈-trans (⊢≈-sym Δ≈Δ₂) Δ≈Δ₁) ⊢τ) ⊢σ

-- ⫢,-∘ : ∀ {i} →
--        U.Δ′ ⫢s U.σ′ ∶ U.Ψ′ →
--        U.Ψ′ ⫢ U.T′ ∶ Se i →
--        U.Δ′ ⫢ U.t′ ∶ U.T′ U.[ U.σ′ ] →
--        U.Γ′ ⫢s U.τ′ ∶ U.Δ′ →
--        ---------------------
--        U.Γ′ ⫢s (U.σ′ , U.t′ ∶ U.T′) ∘ U.τ′ ≈ (U.σ′ ∘ U.τ′) , U.t′ U.[ U.τ′ ] ∶ U.T′ ∶ U.T′ ∷ U.Ψ′
-- ⫢,-∘ ⫢σ′ ⫢T′ ⫢t′ ⫢τ′
--   with Δ₁ , Ψ₁ , σ , Δ₁↝ , Ψ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
--      | _ , Ψ₂ , T , _ , Ψ₂↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
--      | i , Δ₂ , t , _ , Δ₂↝ , t↝ , ↝sub {t = T₁} T₁↝ σ₁↝ , ⊢t , IHt ← ⫢t′
--      | Γ , Δ₃ , τ , Γ↝ , Δ₃↝ , τ↝ , ⊢τ , IHτ ← ⫢τ′
--   with refl ← ⊢T:Se-lvl ⊢T
--   with ⊢Δ₁ , ⊢Ψ₁ ← presup-s ⊢σ
--      | ⊢Ψ₂ ← proj₁ (presup-tm ⊢T)
--      | ⊢Δ₂ , ⊢T₁[σ] ← presup-tm ⊢t
--      | _ , ⊢Δ₃ ← presup-s ⊢τ
--   with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
--      | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
--      | Δ≈Δ₃ ← IHΔ Δ₃↝ ⊢Δ₃
--      | Ψ≈Ψ₁ ← IHΨ Ψ₁↝ ⊢Ψ₁
--      | Ψ≈Ψ₂ ← IHΨ Ψ₂↝ ⊢Ψ₂
--   with Δ₁≈Δ₃ ← ⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₃
--      | Δ₂≈Δ₃ ← ⊢≈-trans (⊢≈-sym Δ≈Δ₂) Δ≈Δ₃
--   with Ψ₃ , _ , ⊢σ₁ , ⊢T₁ , _ ← t[σ]-inv ⊢T₁[σ]
--   with σ≈σ₁ ← IHσ σ₁↝ (ctxeq-s (⊢≈-trans (⊢≈-sym Δ≈Δ₂) Δ≈Δ₁) ⊢σ₁)
--   with Ψ₁≈Ψ₃ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σ₁)))
--   with Ψ₂≈Ψ₃ ← ⊢≈-trans (⊢≈-trans (⊢≈-sym Ψ≈Ψ₂) Ψ≈Ψ₁) Ψ₁≈Ψ₃
--   with T≈T₁ ← IHT T₁↝ (ctxeq-tm (⊢≈-sym Ψ₂≈Ψ₃) ⊢T₁)
--   with refl , ≈Se ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
--     = _ , _ , _ , _ , Γ↝ , ↝∷ Ψ↝ T↝ , ↝∘ (↝, σ↝ t↝ T↝) τ↝ , ↝, (↝∘ σ↝ τ↝) (↝sub t↝ τ↝) T↝ ,
--       ,-∘ (s-conv (ctxeq-s Δ₁≈Δ₃ ⊢σ) (⊢≈-sym Ψ≈Ψ₁)) (ctxeq-tm (⊢≈-sym Ψ≈Ψ₂) ⊢T)
--           (conv (ctxeq-tm Δ₂≈Δ₃ ⊢t) ([]-cong-Se-simp (≈-conv (≈-sym T≈T₁) (≈-sym ≈Se)) (ctxeq-s-≈ Δ₁≈Δ₃ (s-≈-conv (s-≈-sym σ≈σ₁) (⊢≈-sym Ψ₂≈Ψ₃))))) ⊢τ

-- ⫢p-, : ∀ {i} →
--        U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--        U.Δ′ ⫢ U.T′ ∶ Se i →
--        U.Γ′ ⫢ U.t′ ∶ U.T′ U.[ U.σ′ ] →
--        ---------------------
--        U.Γ′ ⫢s U.p (U.σ′ , U.t′ ∶ U.T′) ≈ U.σ′ ∶ U.Δ′
-- ⫢p-, ⫢σ′ ⫢T′ ⫢t′
--   with Γ₁ , Δ₁ , σ , Γ₁↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
--      | _ , Δ₂ , T , _ , Δ₂↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
--      | i , Γ₂ , t , _ , Γ₂↝ , t↝ , ↝sub {t = T₁} T₁↝ σ₁↝ , ⊢t , IHt ← ⫢t′
--   with ⊢Γ₁ , ⊢Δ₁ ← presup-s ⊢σ
--      | ⊢Δ₂ ← proj₁ (presup-tm ⊢T)
--      | ⊢Γ₂ , ⊢T₁[σ] ← presup-tm ⊢t
--   with Δ₃ , _ , ⊢σ₁ , ⊢T₁ , _ ← t[σ]-inv ⊢T₁[σ]
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--      | Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
--      | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
--   with σ≈σ₁ ← IHσ σ₁↝ (ctxeq-s (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) ⊢σ₁)
--   with Δ₁≈Δ₃ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σ₁)))
--   with Δ₂≈Δ₃ ← ⊢≈-trans (⊢≈-sym Δ≈Δ₂) (⊢≈-trans Δ≈Δ₁ Δ₁≈Δ₃)
--   with T≈T₁ ← IHT T₁↝ (ctxeq-tm (⊢≈-sym Δ₂≈Δ₃) ⊢T₁)
--   with refl , ≈Se ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
--   with refl ← ⊢T:Se-lvl ⊢T
--     = _ , _ , _ , _ , Γ↝ , Δ↝ , ↝∘ ↝wk (↝, σ↝ t↝ T↝) , σ↝ ,
--       p-, (ctxeq-s (⊢≈-sym Γ≈Γ₁) (s-conv ⊢σ (⊢≈-sym Δ≈Δ₁))) (ctxeq-tm (⊢≈-sym Δ≈Δ₂) ⊢T)
--           (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₂) ⊢t) ([]-cong-Se-simp (ctxeq-≈ Δ₂≈Δ₃ (≈-conv (≈-sym T≈T₁) (≈-sym ≈Se))) (ctxeq-s-≈ (⊢≈-sym Γ≈Γ₁) (s-≈-sym σ≈σ₁))))

-- ⫢,-ext : U.Γ′ ⫢s U.σ′ ∶ U.T′ ∷ U.Δ′ →
--          ---------------------
--          U.Γ′ ⫢s U.σ′ ≈ U.p U.σ′ , v 0 U.[ U.σ′ ] ∶ U.T′ ∶ U.T′ ∷ U.Δ′
-- ⫢,-ext ⫢σ′
--   with Γ , Δ , σ , Γ↝ , ↝T∷Δ@(↝∷ Δ↝ T↝) , σ↝ , ⊢σ , IHσ ← ⫢σ′
--     = _ , _ , _ , _ , Γ↝ , ↝T∷Δ , σ↝ , ↝, (↝∘ ↝wk σ↝) (↝sub ↝v σ↝) T↝ , ,-ext ⊢σ

-- ⫢s-≈-sym : U.Γ′ ⫢s U.σ′ ≈ U.τ′ ∶ U.Δ′ →
--            ---------------------
--            U.Γ′ ⫢s U.τ′ ≈ U.σ′ ∶ U.Δ′
-- ⫢s-≈-sym σ′≈τ′
--   with Γ , Δ , σ , τ , Γ↝ , Δ↝ , σ↝ , τ↝ , σ≈τ ← σ′≈τ′
--     = _ , _ , _ , _ , Γ↝ , Δ↝ , τ↝ , σ↝ , s-≈-sym σ≈τ

-- ⫢s-≈-trans : ∀ {ζ′} →
--              U.Γ′ ⫢s U.τ′ ∶ U.Δ′ →
--              U.Γ′ ⫢s U.σ′ ≈ U.τ′ ∶ U.Δ′ →
--              U.Γ′ ⫢s U.τ′ ≈ ζ′ ∶ U.Δ′ →
--              ---------------------
--              U.Γ′ ⫢s U.σ′ ≈ ζ′ ∶ U.Δ′
-- ⫢s-≈-trans ⫢τ′ σ′≈τ′ τ′≈ζ′
--   with Γ , Γ↝ , ⊢Γ , IHΓ ← ⫢Γ′
--      | Γ₁ , Δ , τ , Γ₁↝ , Δ↝ , τ↝ , ⊢τ , IHτ ← ⫢τ′
--      | Γ₂ , Δ₁ , σ , τ₁ , Γ₂↝ , Δ₁↝ , σ↝ , τ₁↝ , σ≈τ ← σ′≈τ′
--      | Γ₃ , Δ₂ , τ₂ , ζ , Γ₃↝ , Δ₂↝ , τ₂↝ , ζ↝ , τ≈ζ ← τ′≈ζ′
--   with ⊢Γ₁ , ⊢Δ ← presup-s ⊢τ
--      | ⊢Γ₂ , _ , ⊢τ₁ , ⊢Δ₁ ← presup-s-≈ σ≈τ
--      | ⊢Γ₃ , ⊢τ₂ , _ , ⊢Δ₂ ← presup-s-≈ τ≈ζ
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--      | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃
--   with τ≈τ₁ ← IHτ τ₁↝ (ctxeq-s (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) ⊢τ₁)
--      | τ≈τ₂ ← IHτ τ₂↝ (ctxeq-s (⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁) ⊢τ₂)
--   with Δ≈Δ₁ ← unique-ctx ⊢τ (proj₁ (proj₂ (presup-s-≈ τ≈τ₁)))
--      | Δ≈Δ₂ ← unique-ctx ⊢τ (proj₁ (proj₂ (presup-s-≈ τ≈τ₂)))
--   with Δ₁≈Δ₂ ← ⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₂
--   with τ₁≈τ₂ ← s-≈-trans (s-≈-sym τ≈τ₁) (s-≈-conv τ≈τ₂ (⊢≈-sym Δ₁≈Δ₂))
--     = _ , _ , _ , _ , Γ₂↝ , Δ₁↝ , σ↝ , ζ↝ , s-≈-trans σ≈τ (s-≈-trans (ctxeq-s-≈ (⊢≈-trans (⊢≈-sym Γ≈Γ₁) Γ≈Γ₂) τ₁≈τ₂) (s-≈-conv (ctxeq-s-≈ (⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₂) τ≈ζ) (⊢≈-sym Δ₁≈Δ₂)))

-- ⫢s-≈-conv : ⫢ U.Δ′ → -- extra condition
--             U.Γ′ ⫢s U.σ′ ≈ U.τ′ ∶ U.Δ′ →
--             ⫢ U.Δ′ ≈ U.Ψ′ →
--             ---------------------
--             U.Γ′ ⫢s U.σ′ ≈ U.τ′ ∶ U.Ψ′
-- ⫢s-≈-conv ⫢Δ′ σ′≈τ′ Δ′≈Ψ′
--   with Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
--      | Γ , Δ₁ , σ , τ , Γ↝ , Δ₁↝ , σ↝ , τ↝ , σ≈τ ← σ′≈τ′
--      | Δ₂ , Ψ , Δ₂↝ , Ψ↝ , Δ≈Ψ ← Δ′≈Ψ′
--   with ⊢Δ₁ ← proj₂ (proj₂ (proj₂ (presup-s-≈ σ≈τ)))
--      | ⊢Δ₂ ← proj₁ (presup-⊢≈ Δ≈Ψ)
--   with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
--      | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂ = _ , _ , _ , _ , Γ↝ , Ψ↝ , σ↝ , τ↝ , s-≈-conv σ≈τ (⊢≈-trans (⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₂) Δ≈Ψ)

-- mutual
--   fundamental-⊢⇒⫢ : U.⊢ U.Γ →
--                     --------------------
--                     ⫢ U.Γ
--   fundamental-⊢⇒⫢ ⊢[] = ⫢⊢[]
--   fundamental-⊢⇒⫢ (⊢∷ ⊢Γ ⊢T) = ⫢⊢∷ (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢T)

--   fundamental-⊢≈⇒⫢≈ : U.⊢ U.Γ ≈ U.Δ →
--                       --------------------
--                       ⫢ U.Γ ≈ U.Δ
--   fundamental-⊢≈⇒⫢≈ []-≈ = ⫢[]-≈
--   fundamental-⊢≈⇒⫢≈ (∷-cong ⊢Γ ⊢Δ Γ≈Δ ⊢S ⊢T Γ⊢S≈T Δ⊢S≈T) = ⫢∷-cong (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢≈⇒⫢≈ Γ≈Δ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t≈⇒⫢t≈ Γ⊢S≈T) (fundamental-⊢t≈⇒⫢t≈ Δ⊢S≈T)

--   fundamental-⊢t⇒⫢t : U.Γ ⊢ U.t ∶ U.T →
--                       --------------------
--                       U.Γ ⫢ U.t ∶ U.T
--   fundamental-⊢t⇒⫢t (N-wf ⊢Γ) = ⫢N-wf (fundamental-⊢⇒⫢ ⊢Γ)
--   fundamental-⊢t⇒⫢t (Se-wf i ⊢Γ) = ⫢Se-wf (fundamental-⊢⇒⫢ ⊢Γ)
--   fundamental-⊢t⇒⫢t (Liftt-wf n ⊢T) = ⫢Liftt-wf (fundamental-⊢t⇒⫢t ⊢T)
--   fundamental-⊢t⇒⫢t (Π-wf ⊢Γ ⊢S ⊢T i≡maxjk) = ⫢Π-wf (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t⇒⫢t ⊢T) i≡maxjk
--   fundamental-⊢t⇒⫢t (vlookup ⊢Γ x∈Γ) = ⫢vlookup (fundamental-⊢⇒⫢ ⊢Γ) x∈Γ
--   fundamental-⊢t⇒⫢t (ze-I ⊢Γ) = ⫢ze-I (fundamental-⊢⇒⫢ ⊢Γ)
--   fundamental-⊢t⇒⫢t (su-I ⊢t) = ⫢su-I (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t⇒⫢t (N-E ⊢Γ ⊢T ⊢s ⊢r ⊢t) = ⫢N-E (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t⇒⫢t ⊢s) (fundamental-⊢t⇒⫢t ⊢r) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t⇒⫢t (Λ-I ⊢Γ ⊢S ⊢t) = ⫢Λ-I (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t⇒⫢t (Λ-E ⊢Γ ⊢S ⊢T ⊢r ⊢s) = ⫢Λ-E (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t⇒⫢t ⊢r) (fundamental-⊢t⇒⫢t ⊢s)
--   fundamental-⊢t⇒⫢t (L-I j ⊢t) = ⫢L-I (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t⇒⫢t (L-E j ⊢Γ ⊢T ⊢t) = ⫢L-E (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t⇒⫢t (t[σ] ⊢Δ ⊢t ⊢σ) = ⫢t[σ] (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢t⇒⫢t ⊢t) (fundamental-⊢s⇒⫢s ⊢σ)
--   fundamental-⊢t⇒⫢t (conv ⊢Γ ⊢t ⊢S S≈T) = ⫢conv (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢t) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t≈⇒⫢t≈ S≈T)

--   fundamental-⊢s⇒⫢s : U.Γ U.⊢s U.σ ∶ U.Δ →
--                       --------------------
--                       U.Γ ⫢s U.σ ∶ U.Δ
--   fundamental-⊢s⇒⫢s (s-I ⊢Γ) = ⫢s-I (fundamental-⊢⇒⫢ ⊢Γ)
--   fundamental-⊢s⇒⫢s (s-wk ⊢S∷Γ) = ⫢s-wk (fundamental-⊢⇒⫢ ⊢S∷Γ)
--   fundamental-⊢s⇒⫢s (s-∘ ⊢Δ ⊢τ ⊢σ) = ⫢s-∘ (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢s⇒⫢s ⊢τ) (fundamental-⊢s⇒⫢s ⊢σ)
--   fundamental-⊢s⇒⫢s (s-, ⊢Γ ⊢Δ ⊢σ ⊢T ⊢t) = ⫢s-, (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢s⇒⫢s (s-conv ⊢Δ ⊢σ Δ≈Ψ) = ⫢s-conv (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢≈⇒⫢≈ Δ≈Ψ)

--   fundamental-⊢t≈⇒⫢t≈ : U.Γ ⊢ U.t ≈ U.s ∶ U.T →
--                         --------------------
--                         U.Γ ⫢ U.t ≈ U.s ∶ U.T
--   fundamental-⊢t≈⇒⫢t≈ (N-[] ⊢σ) = ⫢N-[] (fundamental-⊢s⇒⫢s ⊢σ)
--   fundamental-⊢t≈⇒⫢t≈ (Se-[] i ⊢σ) = ⫢Se-[] (fundamental-⊢s⇒⫢s ⊢σ)
--   fundamental-⊢t≈⇒⫢t≈ (Liftt-[] n ⊢Δ ⊢σ ⊢T) = ⫢Liftt-[] (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢T)
--   fundamental-⊢t≈⇒⫢t≈ (Π-[] ⊢Δ ⊢σ ⊢S ⊢T k≡maxij) = ⫢Π-[] (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t⇒⫢t ⊢T) k≡maxij
--   fundamental-⊢t≈⇒⫢t≈ (Π-cong ⊢Γ ⊢S S≈S′ T≈T′ k≡maxij) = ⫢Π-cong (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t≈⇒⫢t≈ S≈S′) (fundamental-⊢t≈⇒⫢t≈ T≈T′) k≡maxij
--   fundamental-⊢t≈⇒⫢t≈ (Liftt-cong j T≈T′) = ⫢Liftt-cong (fundamental-⊢t≈⇒⫢t≈ T≈T′)
--   fundamental-⊢t≈⇒⫢t≈ (v-≈ ⊢Γ x∈Γ) = ⫢v-≈ (fundamental-⊢⇒⫢ ⊢Γ) x∈Γ
--   fundamental-⊢t≈⇒⫢t≈ (ze-≈ ⊢Γ) = ⫢ze-≈ (fundamental-⊢⇒⫢ ⊢Γ)
--   fundamental-⊢t≈⇒⫢t≈ (su-cong t≈t′) = ⫢su-cong (fundamental-⊢t≈⇒⫢t≈ t≈t′)
--   fundamental-⊢t≈⇒⫢t≈ (rec-cong ⊢Γ ⊢T T≈T′ s≈s′ r≈r′ t≈t′) = ⫢rec-cong (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t≈⇒⫢t≈ T≈T′) (fundamental-⊢t≈⇒⫢t≈ s≈s′) (fundamental-⊢t≈⇒⫢t≈ r≈r′) (fundamental-⊢t≈⇒⫢t≈ t≈t′)
--   fundamental-⊢t≈⇒⫢t≈ (Λ-cong ⊢Γ ⊢S S≈S′ t≈t′) = ⫢Λ-cong (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t≈⇒⫢t≈ S≈S′) (fundamental-⊢t≈⇒⫢t≈ t≈t′)
--   fundamental-⊢t≈⇒⫢t≈ ($-cong ⊢Γ ⊢S ⊢T r≈r′ s≈s′) = ⫢$-cong (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t≈⇒⫢t≈ r≈r′) (fundamental-⊢t≈⇒⫢t≈ s≈s′)
--   fundamental-⊢t≈⇒⫢t≈ (liftt-cong j t≈t′) = ⫢liftt-cong (fundamental-⊢t≈⇒⫢t≈ t≈t′)
--   fundamental-⊢t≈⇒⫢t≈ (unlift-cong n ⊢Γ ⊢T t≈t′) = ⫢unliftt-cong (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t≈⇒⫢t≈ t≈t′)
--   fundamental-⊢t≈⇒⫢t≈ ([]-cong ⊢Δ t≈t′ σ≈σ′) = ⫢[]-cong (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢t≈⇒⫢t≈ t≈t′) (fundamental-⊢s≈⇒⫢s≈ σ≈σ′)
--   fundamental-⊢t≈⇒⫢t≈ (ze-[] ⊢σ) = ⫢ze-[] (fundamental-⊢s⇒⫢s ⊢σ)
--   fundamental-⊢t≈⇒⫢t≈ (su-[] ⊢Δ ⊢σ ⊢t) = ⫢su-[] (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t≈⇒⫢t≈ (rec-[] ⊢Δ ⊢σ ⊢T ⊢s ⊢r ⊢t) = ⫢rec-[] (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t⇒⫢t ⊢s) (fundamental-⊢t⇒⫢t ⊢r) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t≈⇒⫢t≈ (Λ-[] ⊢Δ ⊢σ ⊢S ⊢t) = ⫢Λ-[] (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t≈⇒⫢t≈ ($-[] ⊢Δ ⊢S ⊢T ⊢σ ⊢r ⊢s) = ⫢$-[] (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢r) (fundamental-⊢t⇒⫢t ⊢s)
--   fundamental-⊢t≈⇒⫢t≈ (liftt-[] n ⊢Δ ⊢σ ⊢T ⊢t) = ⫢liftt-[] (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t≈⇒⫢t≈ (unlift-[] n ⊢Δ ⊢T ⊢σ ⊢t) = ⫢unlift-[] (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t≈⇒⫢t≈ (rec-β-ze ⊢Γ ⊢T ⊢s ⊢r) = ⫢rec-β-ze (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t⇒⫢t ⊢s) (fundamental-⊢t⇒⫢t ⊢r)
--   fundamental-⊢t≈⇒⫢t≈ (rec-β-su ⊢Γ ⊢T ⊢s ⊢r ⊢t) = ⫢rec-β-su (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t⇒⫢t ⊢s) (fundamental-⊢t⇒⫢t ⊢r) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t≈⇒⫢t≈ (Λ-β ⊢Γ ⊢S ⊢T ⊢t ⊢s) = ⫢Λ-β (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t⇒⫢t ⊢t) (fundamental-⊢t⇒⫢t ⊢s)
--   fundamental-⊢t≈⇒⫢t≈ (Λ-η ⊢Γ ⊢S ⊢T ⊢t) = ⫢Λ-η (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t≈⇒⫢t≈ (L-β j ⊢s) = ⫢L-β (fundamental-⊢t⇒⫢t ⊢s)
--   fundamental-⊢t≈⇒⫢t≈ (L-η n ⊢Γ ⊢T ⊢t) = ⫢L-η (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t≈⇒⫢t≈ ([I] ⊢s) = ⫢[I] (fundamental-⊢t⇒⫢t ⊢s)
--   fundamental-⊢t≈⇒⫢t≈ ([wk] ⊢Γ ⊢S x∈Γ) = ⫢[wk] (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢S) x∈Γ
--   fundamental-⊢t≈⇒⫢t≈ ([∘] ⊢Γ′ ⊢Γ″ ⊢τ ⊢σ ⊢t) = ⫢[∘] (fundamental-⊢⇒⫢ ⊢Γ′) (fundamental-⊢⇒⫢ ⊢Γ″) (fundamental-⊢s⇒⫢s ⊢τ) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t≈⇒⫢t≈ ([,]-v-ze ⊢Γ ⊢Δ ⊢σ ⊢S ⊢s) = ⫢[,]-v-ze (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t⇒⫢t ⊢s)
--   fundamental-⊢t≈⇒⫢t≈ ([,]-v-su ⊢Γ ⊢Δ ⊢σ ⊢S ⊢s x∈Γ) = ⫢[,]-v-su (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t⇒⫢t ⊢s)  x∈Γ
--   fundamental-⊢t≈⇒⫢t≈ (≈-conv ⊢Γ ⊢S t≈s T≈S) = ⫢≈-conv (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t≈⇒⫢t≈ t≈s) (fundamental-⊢t≈⇒⫢t≈ T≈S)
--   fundamental-⊢t≈⇒⫢t≈ (≈-sym t≈s) = ⫢≈-sym (fundamental-⊢t≈⇒⫢t≈ t≈s)
--   fundamental-⊢t≈⇒⫢t≈ (≈-trans ⊢Γ ⊢s t≈s s≈r) = ⫢≈-trans (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢s) (fundamental-⊢t≈⇒⫢t≈ t≈s) (fundamental-⊢t≈⇒⫢t≈ s≈r)

--   fundamental-⊢s≈⇒⫢s≈ : U.Γ U.⊢s U.σ ≈ U.τ ∶ U.Δ →
--                         --------------------
--                         U.Γ ⫢s U.σ ≈ U.τ ∶ U.Δ
--   fundamental-⊢s≈⇒⫢s≈ (I-≈ ⊢Γ) = ⫢I-≈ (fundamental-⊢⇒⫢ ⊢Γ)
--   fundamental-⊢s≈⇒⫢s≈ (wk-≈ ⊢T∷Γ) = ⫢wk-≈ (fundamental-⊢⇒⫢ ⊢T∷Γ)
--   fundamental-⊢s≈⇒⫢s≈ (∘-cong ⊢Γ′ σ≈σ′ τ≈τ′) = ⫢∘-cong (fundamental-⊢⇒⫢ ⊢Γ′) (fundamental-⊢s≈⇒⫢s≈ σ≈σ′) (fundamental-⊢s≈⇒⫢s≈ τ≈τ′)
--   fundamental-⊢s≈⇒⫢s≈ (,-cong ⊢Γ ⊢Δ ⊢σ σ≈τ ⊢T T≈T′ t≈t′) = ⫢,-cong (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢s≈⇒⫢s≈ σ≈τ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t≈⇒⫢t≈ T≈T′) (fundamental-⊢t≈⇒⫢t≈ t≈t′)
--   fundamental-⊢s≈⇒⫢s≈ (I-∘ ⊢σ) = ⫢I-∘ (fundamental-⊢s⇒⫢s ⊢σ)
--   fundamental-⊢s≈⇒⫢s≈ (∘-I ⊢σ) = ⫢∘-I (fundamental-⊢s⇒⫢s ⊢σ)
--   fundamental-⊢s≈⇒⫢s≈ (∘-assoc ⊢Γ″ ⊢Γ′ ⊢σ ⊢τ ⊢γ) = ⫢∘-assoc (fundamental-⊢⇒⫢ ⊢Γ″) (fundamental-⊢⇒⫢ ⊢Γ′) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢s⇒⫢s ⊢τ) (fundamental-⊢s⇒⫢s ⊢γ)
--   fundamental-⊢s≈⇒⫢s≈ (,-∘ ⊢Γ′ ⊢Γ″ ⊢σ ⊢T ⊢t ⊢τ) = ⫢,-∘ (fundamental-⊢⇒⫢ ⊢Γ′) (fundamental-⊢⇒⫢ ⊢Γ″) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t⇒⫢t ⊢t) (fundamental-⊢s⇒⫢s ⊢τ)
--   fundamental-⊢s≈⇒⫢s≈ (p-, ⊢Γ′ ⊢Γ ⊢σ ⊢T ⊢t) = ⫢p-, (fundamental-⊢⇒⫢ ⊢Γ′) (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢s≈⇒⫢s≈ (,-ext ⊢σ) = ⫢,-ext (fundamental-⊢s⇒⫢s ⊢σ)
--   fundamental-⊢s≈⇒⫢s≈ (s-≈-sym σ≈τ) = ⫢s-≈-sym (fundamental-⊢s≈⇒⫢s≈ σ≈τ)
--   fundamental-⊢s≈⇒⫢s≈ (s-≈-trans ⊢Γ ⊢τ σ≈τ τ≈γ) = ⫢s-≈-trans (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢s⇒⫢s ⊢τ) (fundamental-⊢s≈⇒⫢s≈ σ≈τ) (fundamental-⊢s≈⇒⫢s≈ τ≈γ)
--   fundamental-⊢s≈⇒⫢s≈ (s-≈-conv ⊢Δ σ≈τ Δ≈Ψ) = ⫢s-≈-conv (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢s≈⇒⫢s≈ σ≈τ) (fundamental-⊢≈⇒⫢≈ Δ≈Ψ)             