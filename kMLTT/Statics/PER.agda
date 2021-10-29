{-# OPTIONS --without-K --safe #-}

module kMLTT.Statics.PER where

open import Relation.Binary using (PartialSetoid; IsPartialEquivalence)
import Relation.Binary.Reasoning.PartialSetoid as PS

open import kMLTT.Statics.Full
open import kMLTT.Statics.Misc

Exp≈-isPER : IsPartialEquivalence (Γ ⊢_≈_∶ T)
Exp≈-isPER {Γ} {T} = record
  { sym   = ≈-sym
  ; trans = ≈-trans
  }

Exp≈-PER : Ctxs → Typ → PartialSetoid _ _
Exp≈-PER Γ T = record
  { Carrier              = Exp
  ; _≈_                  = Γ ⊢_≈_∶ T
  ; isPartialEquivalence = Exp≈-isPER
  }

module ER {Γ T} = PS (Exp≈-PER Γ T)

Substs≈-isPER : IsPartialEquivalence (Γ ⊢s_≈_∶ Δ)
Substs≈-isPER = record
  { sym   = s-≈-sym
  ; trans = s-≈-trans
  }

Substs≈-PER : Ctxs → Ctxs → PartialSetoid _ _
Substs≈-PER Γ Δ = record
  { Carrier              = Substs
  ; _≈_                  = Γ ⊢s_≈_∶ Δ
  ; isPartialEquivalence = Substs≈-isPER
  }

module SR {Γ Δ} = PS (Substs≈-PER Γ Δ)

⊢-sym : ⊢ Γ ≈ Δ → ⊢ Δ ≈ Γ
⊢-sym []-≈                     = []-≈
⊢-sym (κ-cong Γ≈Δ)             = κ-cong (⊢-sym Γ≈Δ)
⊢-sym (∷-cong Γ≈Δ ⊢T ⊢T′ T≈T′) = ∷-cong (⊢-sym Γ≈Δ) ⊢T′ ⊢T {!≈-sym T≈T′!}

⊢-trans : ⊢ Γ ≈ Γ′ → ⊢ Γ′ ≈ Γ″ → ⊢ Γ ≈ Γ″
⊢-trans []-≈                 []-≈                  = []-≈
⊢-trans (κ-cong Γ≈Γ′)        (κ-cong Γ′≈Γ″)        = κ-cong (⊢-trans Γ≈Γ′ Γ′≈Γ″)
⊢-trans (∷-cong Γ≈Γ′ ⊢T ⊢T′ T≈T′) (∷-cong Γ′≈Γ″ ⊢S ⊢S′ S≈S′) = ∷-cong (⊢-trans Γ≈Γ′ Γ′≈Γ″) (lift-⊢-Se-max ⊢T) (lift-⊢-Se-max′ ⊢S′) {!!}

Ctxs≈-isPER : IsPartialEquivalence (λ Γ → ⊢ Γ ≈_) -- weird parser bug here
Ctxs≈-isPER = record
  { sym   = ⊢-sym
  ; trans = ⊢-trans
  }

Ctxs≈-PER : PartialSetoid _ _
Ctxs≈-PER = record
  { Carrier              = Ctxs
  ; _≈_                  = ⊢_≈_
  ; isPartialEquivalence = Ctxs≈-isPER
  }

module CR = PS Ctxs≈-PER
