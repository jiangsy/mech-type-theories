
{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

module NonCumulative.Statics.Unascribed.Equiv  (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂)  where

open import Lib

open import NonCumulative.Statics.Ascribed.Presup as A
open import NonCumulative.Statics.Ascribed.CtxEquiv as A
open import NonCumulative.Statics.Ascribed.Refl as A
open import NonCumulative.Statics.Ascribed.Properties.Contexts as A
open import NonCumulative.Completeness.Consequences fext
open import NonCumulative.Consequences fext
open import NonCumulative.Statics.Ascribed.Full as A renaming (Ctx to lCtx)
open import NonCumulative.Statics.Ascribed.Simpl
open import NonCumulative.Statics.Unascribed.Full as U
open import NonCumulative.Statics.Unascribed.Transfer

U⇒A-vlookup : ∀ {x} →
  A.Γ [↝] U.Γ′ → 
  x ∶ U.T′ ∈! U.Γ′ →
  ∃₂ λ i T →  (T ↝ U.T′) × (x ∶[ i ] T ∈! A.Γ)
U⇒A-vlookup (↝∷ {Γ′} {Γ} {T′} {T} {i′} Γ↝Γ′ T↝T′) here = _ , _ , (↝sub T↝T′ ↝wk , here) 
U⇒A-vlookup (↝∷ Γ↝Γ′ _) (there x∈Γ') with U⇒A-vlookup Γ↝Γ′ x∈Γ'
... | i , T , T↝T′ , x∈Γ = _ , _ , ↝sub T↝T′ ↝wk , there x∈Γ

mutual
  U⇒A-⊢′ : U.⊢ U.Γ′ →
          -------
          (∃ λ Γ → A.⊢ Γ × Γ [↝] U.Γ′) × (∀ {Γ₁ Γ₂} → Γ₁ [↝] U.Γ′ → Γ₂ [↝] U.Γ′ → A.⊢ Γ₁ → A.⊢ Γ₂ → A.⊢ Γ₁ ≈ Γ₂)
  U⇒A-⊢′ ⊢[] = (_ , ⊢[] , ↝[]), helper
    where 
      helper : ∀ {Γ₁ Γ₂} → Γ₁ [↝] L.[] → Γ₂ [↝] L.[] → A.⊢ Γ₁ → A.⊢ Γ₂ → A.⊢ Γ₁ ≈ Γ₂
      helper ↝[] ↝[] _ _ = []-≈
  U⇒A-⊢′ (⊢∷ {Γ′} {T′} {i = i′} ⊢Γ′ ⊢T′) 
    with U⇒A-tm′ ⊢T′ 
       | U⇒A-⊢′ ⊢Γ′
  ... | ( i , Γ , T , .(Se i′) , (Γ[↝]Γ′ , T↝T′ , ↝Se) , ⊢T) , IHT , _ 
      | _ , IHΓ
    with ⊢T:Se-lvl ⊢T 
       | presup-tm ⊢T
  ...  | refl 
       | ⊢Γ , _ = (_ , ⊢∷ ⊢Γ ⊢T , ↝∷ {i = i′} Γ[↝]Γ′ T↝T′) , helper 
    where 
      helper : ∀ {Γ₁ Γ₂} → Γ₁ [↝] T′ L.∷ Γ′ → Γ₂ [↝] T′ L.∷ Γ′ → A.⊢ Γ₁ → A.⊢ Γ₂ → A.⊢ Γ₁ ≈ Γ₂
      helper (↝∷ ↝Γ₁ T₁↝) (↝∷ ↝Γ₂ T₂↝) (⊢∷ ⊢Γ₁ ⊢T₁) (⊢∷ ⊢Γ₂ ⊢T₂) 
        with IHΓ ↝Γ₁ ↝Γ₂ ⊢Γ₁ ⊢Γ₂
      ... | Γ₁≈Γ₂
        with ctxeq-tm Γ₁≈Γ₂ ⊢T₁
      ... | ⊢T₁′ 
        with IHT {i = i′} {!   !} T₁↝ T₂↝ ↝Γ₂ ⊢T₁′ ⊢T₂ 
      ... | b = {!   !}

      --   with IHT T₁↝ T₂↝ ↝Γ₂ ↝Se ↝Se {!   !} {!   !}
      -- ... | b = {!   !}

  U⇒A-tm′ : U.Γ′ U.⊢ U.t′ ∶ U.T′ →
          -------------
           (∃ λ i → ∃ λ Γ → ∃ λ t → ∃ λ T → ((Γ [↝] U.Γ′) × (t ↝ U.t′) × (T ↝ U.T′)) × Γ A.⊢ t ∶[ i ] T) × 
           (∀ {i Γ t₁ t₂ i₁ i₂ T₁ T₂} → U.Γ′ ⊢ U.T′ ≈ Se i ∶ Se (1 + i) → t₁ ↝ U.t′ → t₂ ↝ U.t′ → Γ [↝] U.Γ′ →  
            Γ ⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ t₂ ∶[ i₂ ] T₂ → Γ A.⊢ t₁ ≈ t₂ ∶[ i₁ ] T₁) × 
           (∀ {Γ t₁ t₂ i₁ i₂ T₁ T₂} → t₁ ↝ U.t′ → t₂ ↝ U.t′ → Γ [↝] U.Γ′ → 
            -- cannot have this condition , otherwise cannot be used at 𝟙 
            T₁ ↝ U.T′ → T₂ ↝ U.T′ → 
            Γ ⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ t₂ ∶[ i₂ ] T₂ → Γ A.⊢ t₁ ≈ t₂ ∶[ i₁ ] T₁)
  U⇒A-tm′ (N-wf ⊢Γ′) = {!   !} , {!   !} , {!   !} 
  U⇒A-tm′ (Se-wf i x) = {!   !} , {!   !} , {!   !}
  U⇒A-tm′ (Liftt-wf n ⊢t′) = _ , {!   !} , {!   !} 
  U⇒A-tm′ (Π-wf ⊢t′ ⊢t′₁ x) = {!   !}
  U⇒A-tm′ (vlookup x x₁) = {!   !}
  U⇒A-tm′ (ze-I x) = {!   !}
  U⇒A-tm′ (su-I ⊢t′) = {!   !}
  U⇒A-tm′ (N-E ⊢t′ ⊢t′₁ ⊢t′₂ ⊢t′₃) = {!   !}
  U⇒A-tm′ (Λ-I {Γ = Γ′} {S = S′} {t = t′} {T = T′} ⊢S′ ⊢t′) 
    with U⇒A-tm′ ⊢S′ 
       | U⇒A-tm′ ⊢t′ 
  ...  | x , IHS₁ , IHS₂
       | y , IHt₁ , IHt₂ = {!   !} , {!   !} , helper
    where 
      helper : ∀ {Γ t₁ t₂ i₁ i₂ T₁ T₂} →
        t₁ ↝ Λ t′ →
        t₂ ↝ Λ t′ →
        Γ [↝] Γ′ →
        T₁ ↝ Π S′ T′ →
        T₂ ↝ Π S′ T′ →
        Γ ⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ t₂ ∶[ i₂ ] T₂ → Γ ⊢ t₁ ≈ t₂ ∶[ i₁ ] T₁
      helper (↝Λ t₁↝) (↝Λ t₂↝) Γ↝ (↝Π S₁↝ T₁↝) (↝Π S₂↝ T₂↝) ⊢t₁ ⊢t₂ 
        with Λ-inv ⊢t₁ 
           | Λ-inv ⊢t₂
      ...  | refl , refl , ⊢S₁ , ⊢t₁ 
           | refl , refl , ⊢S₂ , ⊢t₂ 
        with IHS₁ _ S₁↝ S₂↝
      ... | b = {!   !}

  U⇒A-tm′ (Λ-E ⊢t′ ⊢t′₁ ⊢t′₂ ⊢t′₃) = {!   !}
  U⇒A-tm′ (L-I n ⊢t′) = {!   !}
  U⇒A-tm′ (L-E n ⊢t′ ⊢t′₁) = {!   !}
  U⇒A-tm′ (t[σ] ⊢t′ x) = {!   !}
  U⇒A-tm′ (conv ⊢t′ x) = {!   !}      