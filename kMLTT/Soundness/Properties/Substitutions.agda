{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

-- prove that the gluing model is cumulative
module kMLTT.Soundness.Properties.Substitutions (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Data.Nat.Properties as ℕₚ
open import Data.List.Properties as Lₚ

open import kMLTT.Completeness.LogRel
open import kMLTT.Completeness.Contexts fext
open import kMLTT.Completeness.Fundamental fext
open import kMLTT.Statics.Properties as Sta
open import kMLTT.Semantics.Readback
open import kMLTT.Semantics.Realizability fext
open import kMLTT.Semantics.Properties.Domain fext as Sem
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Soundness.Cumulativity fext
open import kMLTT.Soundness.LogRel
open import kMLTT.Soundness.Properties.LogRel fext
open import kMLTT.Soundness.Properties.Mt fext


⊢s®⇒⊢s : (⊢Δ : ⊢ Δ) →
         Γ ⊢s σ ∶ ⊢Δ ® ρ →
         Γ ⊢s σ ∶ Δ
⊢s®⇒⊢s ⊢[]      σ∼ρ = σ∼ρ
⊢s®⇒⊢s (⊢κ _)   σ∼ρ = Gluκ.⊢σ σ∼ρ
⊢s®⇒⊢s (⊢∺ _ _) σ∼ρ = Glu∺.⊢σ σ∼ρ

⊢s®⇒⟦⟧ρ : (⊢Δ : ⊢ Δ) →
          Γ ⊢s σ ∶ ⊢Δ ® ρ →
          ρ ∈′ ⟦ fundamental-⊢Γ ⊢Δ ⟧ρ
⊢s®⇒⟦⟧ρ ⊢[] σ∼ρ       = _
⊢s®⇒⟦⟧ρ (⊢κ ⊢Δ) σ∼ρ
  with ⊢s®⇒⟦⟧ρ ⊢Δ (Gluκ.step σ∼ρ)
...  | ρ∈        = ρ∈ , refl
⊢s®⇒⟦⟧ρ {_} {_} {_} {ρ} (⊢∺ ⊢Δ ⊢T) σ∼ρ
  with fundamental-⊢Γ ⊢Δ | fundamental-⊢t ⊢T | ⊢s®⇒⟦⟧ρ ⊢Δ (Glu∺.step σ∼ρ)
...  | ⊨Δ | ⊨T | ρ∈ = ρ∈ , helper
  where
    open Glu∺ σ∼ρ

    helper : lookup ρ 0 ∈′ El _ (RelTyp.T≈T′ (∺-cong-helper ⊨T ⊨Δ ρ∈))
    helper
      with ∺-cong-helper ⊨T ⊨Δ ρ∈
    ...  | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′ }
        rewrite ⟦⟧-det ↘⟦T⟧₁ ↘⟦T⟧
              | ⟦⟧-det ↘⟦T′⟧₁ ↘⟦T⟧ = 𝕌-irrel T∈𝕌 T≈T′ (®El⇒∈El T∈𝕌 t∼ρ0)

⊢s®⇒⟦⟧ρ′ : (⊢Δ : ⊢ Δ) →
           Γ ⊢s σ ∶ ⊢Δ ® ρ →
           Σ (⊨ Δ) λ ⊨Δ → ρ ∈′ ⟦ ⊨Δ ⟧ρ
⊢s®⇒⟦⟧ρ′ ⊢Δ σ∼ρ = fundamental-⊢Γ ⊢Δ , ⊢s®⇒⟦⟧ρ ⊢Δ σ∼ρ


⊢s®-resp-s≈ : (⊢Δ : ⊢ Δ) →
              Γ ⊢s σ ∶ ⊢Δ ® ρ →
              Γ ⊢s σ ≈ σ′ ∶ Δ →
              -------------------
              Γ ⊢s σ′ ∶ ⊢Δ ® ρ
⊢s®-resp-s≈                      ⊢[]     σ∼ρ σ≈σ′ = proj₁ (proj₂ (proj₂ (presup-s-≈ σ≈σ′)))
⊢s®-resp-s≈ {_} {Γ} {_} {ρ} {σ′} (⊢κ ⊢Δ) σ∼ρ σ≈σ′ = helper
  where
    module gluκ = Gluκ σ∼ρ
    open gluκ

    helper : Γ ⊢s σ′ ∶ ⊢κ ⊢Δ ® ρ
    helper = record
             { gluκ
             ; ⊢σ = proj₁ (proj₂ (proj₂ (presup-s-≈ σ≈σ′)))
             ; ≈σ∥ = s-≈-trans (s-≈-sym (∥-resp-≈″ Ψs⁻ L.[ [] ] (subst (_⊢s _ ≈ _ ∶ _) Γ≡ σ≈σ′) len≡)) ≈σ∥
             ; O≡ = trans (sym (O-resp-≈ 1 σ≈σ′)) O≡
             ; len≡ = trans len≡ (O-resp-≈ 1 σ≈σ′)
             }
⊢s®-resp-s≈ {_} {Γ} {_} {ρ} {σ′} ⊢TΔ@(⊢∺ ⊢Δ ⊢T) σ∼ρ σ≈σ′ = helper
  where
    module glu∺ = Glu∺ σ∼ρ
    open glu∺

    σ′≈σ = s-≈-sym σ≈σ′
    ⊢σ′ = proj₁ (proj₂ (proj₂ (presup-s-≈ σ≈σ′)))

    helper : Γ ⊢s σ′ ∶ ⊢∺ ⊢Δ ⊢T ® ρ
    helper = record
             { glu∺
             ; ⊢σ = ⊢σ′
             ; ≈pσ = s-≈-trans (p-cong (proj₂ (proj₂ (proj₂ (presup-s-≈ σ≈σ′)))) σ′≈σ) ≈pσ
             ; ≈v0σ = ≈-trans (≈-conv ([]-cong (≈-refl (vlookup ⊢TΔ here)) σ′≈σ) (≈-trans (≈-trans ([∘]-Se ⊢T (s-wk ⊢TΔ) ⊢σ′) ([]-cong-Se″ ⊢T (∘-cong σ′≈σ (wk-≈ ⊢TΔ)))) ([]-cong-Se″ ⊢T ≈pσ))) ≈v0σ
             }


⊢s®-resp-≈ : (⊢Δ : ⊢ Δ) →
             Γ ⊢s σ ∶ ⊢Δ ® ρ →
             ⊢ Δ ≈ Δ′ →
             -------------------
             Σ (⊢ Δ′) λ ⊢Δ′ → Γ ⊢s σ ∶ ⊢Δ′ ® ρ
⊢s®-resp-≈ ⊢[] σ∼ρ []-≈ = ⊢[] , σ∼ρ
⊢s®-resp-≈ (⊢κ ⊢Δ) σ∼ρ (κ-cong Δ≈Δ′)
  with ⊢s®-resp-≈ ⊢Δ (Gluκ.step σ∼ρ) Δ≈Δ′
...  | ⊢Δ′ , σ∼ρ′ = ⊢κ ⊢Δ′
                   , record
                     { gluκ
                     ; ⊢σ = s-conv ⊢σ (κ-cong Δ≈Δ′)
                     ; ≈σ∥ = s-≈-conv ≈σ∥ Δ≈Δ′
                     ; step = σ∼ρ′
                     }
  where
    open module gluκ = Gluκ σ∼ρ
⊢s®-resp-≈ {(_ ∷ Ψ) ∷ Ψs} {Γ} (⊢∺ ⊢Δ ⊢T) σ∼ρ (∺-cong Δ≈Δ′ T≈T′)
  with ⊢s®-resp-≈ ⊢Δ (Glu∺.step σ∼ρ) Δ≈Δ′ | fundamental-t≈t′ T≈T′
...  | ⊢Δ′ , σ∼ρ′ | ⊨Δ₁ , _ , Trel₁
    with Trel₁ (⊨-irrel (fundamental-⊢Γ ⊢Δ) ⊨Δ₁ (⊢s®⇒⟦⟧ρ ⊢Δ (Glu∺.step σ∼ρ)))
...    | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n _ }
       , record { ⟦t′⟧ = ⟦T′⟧ ; ↘⟦t⟧ = ↘⟦T⟧₁ ; ↘⟦t′⟧ = ↘⟦T′⟧₁ ; t≈t′ = T≈T′₁ }
      rewrite 𝕌-wellfounded-≡-𝕌 _ i<n
            | ⟦⟧-det (Glu∺.↘⟦T⟧ σ∼ρ) ↘⟦T⟧₁ = ⊢∺ ⊢Δ′ (ctxeq-tm Δ≈Δ′ (proj₁ (proj₂ (proj₂ (presup-≈ T≈T′)))))
                   , record
                     { glu∺
                     ; ⊢σ = s-conv ⊢σ (∺-cong Δ≈Δ′ T≈T′)
                     ; ⟦T⟧ = _
                     ; lvl = _
                     ; ≈pσ = s-≈-conv ≈pσ Δ≈Δ′
                     ; ≈v0σ = ≈-conv ≈v0σ ([]-cong-Se′ T≈T′ ⊢pσ)
                     ; ↘⟦T⟧ = ↘⟦T′⟧₁
                     ; T∈𝕌 = T′∈𝕌
                     -- we need a ®El-one-sided′ which operates on the right-side type
                     ; t∼ρ0 = ®El-resp-T≈ T′∈𝕌 (®El-one-sided (𝕌-cumu (m≤m⊔n _ _) (𝕌-sym T≈T′₁)) T′∈𝕌 {!!}) ([]-cong-Se′ (lift-⊢≈-Se T≈T′ (m≤m⊔n _ _)) ⊢pσ)
                     ; step = σ∼ρ′
                     }
  where
    open module glu∺ = Glu∺ σ∼ρ

    T′∈𝕌 : ⟦T′⟧ ∈′ 𝕌 _
    T′∈𝕌 = 𝕌-cumu (m≤m⊔n _ lvl) (𝕌-refl (𝕌-sym T≈T′₁))

    ⊢pσ : Γ ⊢s pσ ∶ Ψ ∷ Ψs
    ⊢pσ = proj₁ (proj₂ (proj₂ (presup-s-≈ ≈pσ)))


⊢s®-resp-O : ∀ n →
             (⊢Δ : ⊢ Δ) →
             Γ ⊢s σ ∶ ⊢Δ ® ρ →
             n < len Δ →
             --------------------
             O σ n ≡ O ρ n
⊢s®-resp-O {_} {_} {_} {_} 0       ⊢Δ        σ∼ρ n<Δ       = refl
⊢s®-resp-O {_} {_} {_} {ρ} (suc n) ⊢[]       σ∼ρ (s≤s ())
⊢s®-resp-O {_} {_} {σ} {ρ} (suc n) (⊢κ ⊢Δ)   σ∼ρ (s≤s n<Δ) = trans (Sta.O-+ σ 1 _) (cong₂ _+_ O≡ (trans (O-resp-≈ n ≈σ∥) (⊢s®-resp-O n ⊢Δ step n<Δ)))
  where
    open Gluκ σ∼ρ
⊢s®-resp-O {_} {_} {σ} {_} (suc n) (⊢∺ ⊢Δ x) σ∼ρ n<Δ       = trans (O-resp-≈ (suc n) ≈pσ) (⊢s®-resp-O (suc n) ⊢Δ step n<Δ)
  where
    open Glu∺ σ∼ρ


∥-⊢s® : ∀ n →
        (⊢Δ : ⊢ Δ) →
        Γ ⊢s σ ∶ ⊢Δ ® ρ →
        n < len Δ →
        -----------------------------------------------
        ∃₂ λ Ψs Ψs′ → ∃₂ λ Γ′ Δ′ →
           Γ ≡ Ψs ++⁺ Γ′ × Δ ≡ Ψs′ ++⁺ Δ′
         × len Ψs ≡ O σ n × len Ψs′ ≡ n
         × Σ (⊢ Δ′) λ ⊢Δ′ → Γ′ ⊢s σ ∥ n ∶ ⊢Δ′ ® ρ ∥ n
∥-⊢s®                 0       ⊢Δ         σ∼ρ n<Δ       = [] , []
                                                       , _ , _
                                                       , refl , refl
                                                       , refl , refl
                                                       , ⊢Δ , σ∼ρ
∥-⊢s®                 (suc n) ⊢[]        σ∼ρ (s≤s ())
∥-⊢s® {Δ} {Γ} {σ} {ρ} (suc n) (⊢κ ⊢Δ)    σ∼ρ (s≤s n<Δ) = helper
  where
    open Gluκ σ∼ρ

    helper : ∃₂ λ Ψs Ψs′ →
             ∃₂ λ Γ′ Δ′ →
                  Γ ≡ Ψs ++⁺ Γ′ × Δ ≡ Ψs′ ++⁺ Δ′
                × len Ψs ≡ O σ (suc n) × len Ψs′ ≡ suc n
                × Σ (⊢ Δ′) λ ⊢Δ′ → Γ′ ⊢s σ ∥ suc n ∶ ⊢Δ′ ® ρ ∥ suc n
    helper
      with ∥-⊢s® n ⊢Δ step n<Δ
    ...  | Ψs , Ψs′ , _ , _ , refl , refl , Ψs≡Oσ∥ , refl , ⊢Δ′ , σ∥∼ρ∥
          rewrite Sta.∥-+ σ 1 (len Ψs′)   = Ψs⁻ ++ Ψs , _ ∷ Ψs′
                                          , _ , _
                                          , trans Γ≡ (sym (++-++⁺ Ψs⁻)) , refl
                                          , trans (length-++ Ψs⁻) (trans (cong₂ _+_
                                                                                len≡
                                                                                (trans Ψs≡Oσ∥ (sym (O-resp-≈ (len Ψs′) ≈σ∥))))
                                                                         (sym (Sta.O-+ σ 1 _))) , refl
                                          , ⊢Δ′ , ⊢s®-resp-s≈ ⊢Δ′ σ∥∼ρ∥ (∥-resp-≈″ Ψs Ψs′ (s-≈-sym ≈σ∥) Ψs≡Oσ∥)
∥-⊢s® {Δ} {Γ} {σ} {ρ} (suc n) (⊢∺ ⊢Δ ⊢T) σ∼ρ n<Δ     = helper
  where
    open Glu∺ σ∼ρ

    helper : ∃₂ λ Ψs Ψs′ →
             ∃₂ λ Γ′ Δ′ →
                  Γ ≡ Ψs ++⁺ Γ′ × Δ ≡ Ψs′ ++⁺ Δ′
                × len Ψs ≡ O σ (suc n) × len Ψs′ ≡ suc n
                × Σ (⊢ Δ′) λ ⊢Δ′ → Γ′ ⊢s σ ∥ suc n ∶ ⊢Δ′ ® ρ ∥ suc n
    helper
      with ∥-⊢s® (suc n) ⊢Δ step n<Δ
    ...  | Ψs , Ψ′ ∷ Ψs′ , _ , _ , refl , refl , Ψs≡Opσ , refl , ⊢Δ′ , pσ∼drop[ρ]
        rewrite O-resp-≈ (suc (len Ψs′)) ≈pσ = Ψs , (_ ∷ Ψ′) ∷ Ψs′
                                             , _ , _
                                             , refl , refl
                                             , Ψs≡Opσ , refl
                                             , ⊢Δ′ , ⊢s®-resp-s≈ ⊢Δ′ pσ∼drop[ρ] (s-≈-trans (∥-resp-≈″ Ψs (Ψ′ ∷ Ψs′) (s-≈-sym ≈pσ) Ψs≡Opσ) (I-∘ (∥-⊢s″ Ψs ((_ ∷ Ψ′) ∷ Ψs′) ⊢σ (trans Ψs≡Opσ (sym (O-resp-≈ (suc (len Ψs′)) ≈pσ))))))

∥-⊢s®′ : ∀ Ψs →
        (⊢ΨsΔ : ⊢ Ψs ++⁺ Δ) →
        Γ ⊢s σ ∶ ⊢ΨsΔ ® ρ →
        -----------------------------------------------
        ∃₂ λ Ψs′ Γ′ →
           Γ ≡ Ψs′ ++⁺ Γ′
         × len Ψs′ ≡ O σ (len Ψs)
         × Σ (⊢ Δ) λ ⊢Δ → Γ′ ⊢s σ ∥ (len Ψs) ∶ ⊢Δ ® ρ ∥ (len Ψs)
∥-⊢s®′ Ψs ⊢ΨsΔ σ∼ρ
  with ∥-⊢s® (len Ψs) ⊢ΨsΔ σ∼ρ (length-<-++⁺ Ψs)
... | Ψs′ , Ψs₁ , _ , _ , Γ≡Ψs′Γ′ , ΨsΔ≡Ψs₁Δ₁ , Ψs′≡Oσ , Ψs≡Ψs₁ , ⊢Δ₁ , σ∥≈
    rewrite ++⁺-cancelˡ′ Ψs Ψs₁ ΨsΔ≡Ψs₁Δ₁ (sym Ψs≡Ψs₁) = Ψs′ , _ , Γ≡Ψs′Γ′ , Ψs′≡Oσ , ⊢Δ₁ , σ∥≈

∥-⊢s®″ : ∀ Ψs Ψs′ →
        (⊢Ψs′Δ : ⊢ Ψs′ ++⁺ Δ) →
        Ψs ++⁺ Γ ⊢s σ ∶ ⊢Ψs′Δ ® ρ →
        len Ψs ≡ O σ (len Ψs′) →
        -----------------------------------------------
        Σ (⊢ Δ) λ ⊢Δ → Γ ⊢s σ ∥ (len Ψs′) ∶ ⊢Δ ® ρ ∥ (len Ψs′)
∥-⊢s®″ Ψs Ψs′ ⊢Ψs′Δ σ∼ρ Ψs≡Oσ
  with ∥-⊢s®′ Ψs′ ⊢Ψs′Δ σ∼ρ
... | Ψs₁ , _ , ΨsΓ≡Ψs₁Γ₁ , Ψs≡Oσ₁ , ⊢Δ₁ , σ∥≈
    rewrite ++⁺-cancelˡ′ Ψs Ψs₁ ΨsΓ≡Ψs₁Γ₁ (trans Ψs≡Oσ (sym Ψs≡Oσ₁)) = ⊢Δ₁ , σ∥≈
