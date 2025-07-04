{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Semantic judgments for contexts
module Cumulative.Soundness.Contexts (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Lib

open import Cumulative.Statics.Properties as Sta
open import Cumulative.Soundness.LogRel
open import Cumulative.Soundness.ToSyntax fext
open import Cumulative.Soundness.Properties.LogRel fext


⊢[]′ : ⊩ []
⊢[]′ = ⊩[]

⊢∷′-helper : ∀ {i}
             (⊩T : Γ ⊩ T ∶ Se i) →
             Δ ⊢s σ ∶ _⊩_∶_.⊩Γ ⊩T ® ρ →
             GluTyp i Δ T σ ρ
⊢∷′-helper record { krip = krip } σ∼ρ
  with krip σ∼ρ
...  | record { ⟦t⟧ = ⟦T⟧ ; ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦T⟧ ; T∈𝕌 = U i<l _ ; t∼⟦t⟧ = T∼⟦T⟧ }
     rewrite Glu-wellfounded-≡ i<l = record
     { ⟦T⟧   = ⟦T⟧
     ; ↘⟦T⟧  = ↘⟦T⟧
     ; T∈𝕌   = A∈𝕌
     ; T∼⟦T⟧ = rel
     }
  where open GluU T∼⟦T⟧


⊢∷′ : ∀ {i} →
      Γ ⊩ T ∶ Se i →
      --------------
      ⊩ T ∷ Γ
⊢∷′ {_} {T} ⊩T = ⊩∷ ⊩Γ (⊩⇒⊢-tm ⊩T) (⊢∷′-helper ⊩T)
  where open _⊩_∶_ ⊩T
