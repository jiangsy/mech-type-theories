{-# OPTIONS --without-K --safe #-}

-- Equivalence of the Sound formulation and the other two formulations
module Cumulative.Soundness.Equiv where

open import Lib

open import Cumulative.Statics.Full as F
open import Cumulative.Statics.Concise as C
open import Cumulative.Statics.Equiv
open import Cumulative.Statics.Presup
open import Cumulative.Statics.Misc
open import Cumulative.Statics.Properties.Pi
open import Cumulative.Soundness.Typing as S

-- The Sound and Full formulations are equivalent.
mutual
  S⇒F-⊢ : S.⊢ Γ →
          -------
          F.⊢ Γ
  S⇒F-⊢ ⊢[]        = ⊢[]
  S⇒F-⊢ (⊢∷ ⊢Γ ⊢T) = ⊢∷ (S⇒F-⊢ ⊢Γ) (S⇒F-tm ⊢T)


  S⇒F-tm : Γ S.⊢ t ∶ T →
           -------------
           Γ F.⊢ t ∶ T
  S⇒F-tm (N-wf i ⊢Γ)          = N-wf i (S⇒F-⊢ ⊢Γ)
  S⇒F-tm (Se-wf i ⊢Γ)         = Se-wf i (S⇒F-⊢ ⊢Γ)
  S⇒F-tm (Π-wf ⊢S ⊢T)         = Π-wf (S⇒F-tm ⊢S) (S⇒F-tm ⊢T)
  S⇒F-tm (vlookup ⊢Γ T∈Γ)     = vlookup (S⇒F-⊢ ⊢Γ) T∈Γ
  S⇒F-tm (ze-I ⊢Γ)            = ze-I (S⇒F-⊢ ⊢Γ)
  S⇒F-tm (su-I ⊢t)            = su-I (S⇒F-tm ⊢t)
  S⇒F-tm (N-E ⊢T ⊢s ⊢w ⊢t)    = N-E (S⇒F-tm ⊢T) (S⇒F-tm ⊢s) (S⇒F-tm ⊢w) (S⇒F-tm ⊢t)
  S⇒F-tm (Λ-I ⊢t)
    with presup-tm (S⇒F-tm ⊢t)
  ... | ⊢∷ _ ⊢S , _           = Λ-I ⊢S (S⇒F-tm ⊢t)
  S⇒F-tm (Λ-E ⊢T ⊢t ⊢w)
    with presup-tm (S⇒F-tm ⊢t)
  ...  | _ , _ , ⊢Π
       with inv-Π-wf′ ⊢Π
  ...     | _ , ⊢S            = Λ-E (lift-⊢-Se-max ⊢S) (lift-⊢-Se-max′ (S⇒F-tm ⊢T)) (S⇒F-tm ⊢t) (S⇒F-tm ⊢w)
  S⇒F-tm (t[σ] ⊢t ⊢σ)         = t[σ] (S⇒F-tm ⊢t) (S⇒F-s ⊢σ)
  S⇒F-tm (cumu ⊢t)            = cumu (S⇒F-tm ⊢t)
  S⇒F-tm (conv ⊢t T≈T′)       = conv (S⇒F-tm ⊢t) (C⇒F-≈ T≈T′)


  S⇒F-s : Γ S.⊢s σ ∶ Δ →
          --------------
          Γ F.⊢s σ ∶ Δ
  S⇒F-s (s-I ⊢Γ)           = s-I (S⇒F-⊢ ⊢Γ)
  S⇒F-s (s-wk ⊢TΓ)         = s-wk (S⇒F-⊢ ⊢TΓ)
  S⇒F-s (s-∘ ⊢σ ⊢δ)        = s-∘ (S⇒F-s ⊢σ) (S⇒F-s ⊢δ)
  S⇒F-s (s-, ⊢σ ⊢T ⊢t)     = s-, (S⇒F-s ⊢σ) (S⇒F-tm ⊢T) (S⇒F-tm ⊢t)
  S⇒F-s (s-conv ⊢σ Δ′≈Δ)   = s-conv (S⇒F-s ⊢σ) (C⇒F-⊢≈ Δ′≈Δ)


mutual
  F⇒S-⊢ : F.⊢ Γ →
          -------
          S.⊢ Γ
  F⇒S-⊢ ⊢[]        = ⊢[]
  F⇒S-⊢ (⊢∷ ⊢Γ ⊢T) = ⊢∷ (F⇒S-⊢ ⊢Γ) (F⇒S-tm ⊢T)


  F⇒S-tm : Γ F.⊢ t ∶ T →
           -------------
           Γ S.⊢ t ∶ T
  F⇒S-tm (N-wf i ⊢Γ)          = N-wf i (F⇒S-⊢ ⊢Γ)
  F⇒S-tm (Se-wf i ⊢Γ)         = Se-wf i (F⇒S-⊢ ⊢Γ)
  F⇒S-tm (Π-wf ⊢S ⊢T)         = Π-wf (F⇒S-tm ⊢S) (F⇒S-tm ⊢T)
  F⇒S-tm (vlookup ⊢Γ T∈Γ)     = vlookup (F⇒S-⊢ ⊢Γ) T∈Γ
  F⇒S-tm (ze-I ⊢Γ)            = ze-I (F⇒S-⊢ ⊢Γ)
  F⇒S-tm (su-I ⊢t)            = su-I (F⇒S-tm ⊢t)
  F⇒S-tm (N-E ⊢T ⊢s ⊢w ⊢t)    = N-E (F⇒S-tm ⊢T) (F⇒S-tm ⊢s) (F⇒S-tm ⊢w) (F⇒S-tm ⊢t)
  F⇒S-tm (Λ-I _ ⊢t)           = Λ-I (F⇒S-tm ⊢t)
  F⇒S-tm (Λ-E _ ⊢T ⊢t ⊢w)     = Λ-E (F⇒S-tm ⊢T) (F⇒S-tm ⊢t) (F⇒S-tm ⊢w)
  F⇒S-tm (t[σ] ⊢t ⊢σ)         = t[σ] (F⇒S-tm ⊢t) (F⇒S-s ⊢σ)
  F⇒S-tm (cumu ⊢t)            = cumu (F⇒S-tm ⊢t)
  F⇒S-tm (conv ⊢t T≈T′)       = conv (F⇒S-tm ⊢t) (F⇒C-≈ T≈T′)


  F⇒S-s : Γ F.⊢s σ ∶ Δ →
          --------------
          Γ S.⊢s σ ∶ Δ
  F⇒S-s (s-I ⊢Γ)           = s-I (F⇒S-⊢ ⊢Γ)
  F⇒S-s (s-wk ⊢Γ)          = s-wk (F⇒S-⊢ ⊢Γ)
  F⇒S-s (s-∘ ⊢σ ⊢δ)        = s-∘ (F⇒S-s ⊢σ) (F⇒S-s ⊢δ)
  F⇒S-s (s-, ⊢σ ⊢T ⊢t)     = s-, (F⇒S-s ⊢σ) (F⇒S-tm ⊢T) (F⇒S-tm ⊢t)
  F⇒S-s (s-conv ⊢σ Δ′≈Δ)   = s-conv (F⇒S-s ⊢σ) (F⇒C-⊢≈ Δ′≈Δ)


-- The Concise formulation is subsumed by the Sound formulation.
--
-- We could have also proved the other direction but in the actual proof we do not
-- need this property.
C⇒S-⊢ : C.⊢ Γ →
        -------
        S.⊢ Γ
C⇒S-⊢ ⊢Γ = F⇒S-⊢ (C⇒F-⊢ ⊢Γ)


C⇒S-tm : Γ C.⊢ t ∶ T →
         -------------
         Γ S.⊢ t ∶ T
C⇒S-tm ⊢t = F⇒S-tm (C⇒F-tm ⊢t)


C⇒S-s : Γ C.⊢s σ ∶ Δ →
        --------------
        Γ S.⊢s σ ∶ Δ
C⇒S-s ⊢σ = F⇒S-s (C⇒F-s ⊢σ)
