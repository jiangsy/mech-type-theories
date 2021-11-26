{-# OPTIONS --without-K --safe #-}

module kMLTT.Completeness.LogRel where

open import Lib
open import kMLTT.Semantics.Domain public
open import kMLTT.Semantics.Evaluation public
open import kMLTT.Semantics.PER public


record RelExp t ρ t′ ρ′ (R : Ty) : Set where
  field
    ⟦t⟧   : D
    ⟦t′⟧  : D
    ↘⟦t⟧  : ⟦ t ⟧ ρ ↘ ⟦t⟧
    ↘⟦t′⟧ : ⟦ t′ ⟧ ρ′ ↘ ⟦t′⟧
    t≈t′  : ⟦t⟧ ≈ ⟦t′⟧ ∈ R
    nat   : ∀ (κ : UnMoT) → ⟦ t ⟧ ρ [ κ ] ↘ ⟦t⟧ [ κ ]
    nat′  : ∀ (κ : UnMoT) → ⟦ t′ ⟧ ρ′ [ κ ] ↘ ⟦t′⟧ [ κ ]


_⊨_≈_∶_ : Ctxs → Exp → Exp → Typ → Set
Γ ⊨ t ≈ t′ ∶ T = Σ (⊨ Γ) λ ⊨Γ → ∀ {ρ ρ′} (ρ≈ρ′ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ) → Σ (RelTyp T ρ T ρ′) λ rel → let open RelTyp rel in RelExp t ρ t′ ρ′ (El∞ T≈T′)

_⊨_∶_ : Ctxs → Exp → Typ → Set
Γ ⊨ t ∶ T = Γ ⊨ t ≈ t ∶ T


record RelSubsts σ ρ δ ρ′ (R : Evs) : Set where
  field
    ⟦σ⟧  : Envs
    ⟦δ⟧  : Envs
    ↘⟦σ⟧ : ⟦ σ ⟧s ρ ↘ ⟦σ⟧
    ↘⟦δ⟧ : ⟦ δ ⟧s ρ′ ↘ ⟦δ⟧
    σ≈δ  : ⟦σ⟧ ≈ ⟦δ⟧ ∈ R
    nat  : ∀ (κ : UnMoT) → ⟦ σ ⟧s ρ [ κ ] ↘ ⟦σ⟧ [ κ ]
    nat′ : ∀ (κ : UnMoT) → ⟦ δ ⟧s ρ′ [ κ ] ↘ ⟦δ⟧ [ κ ]


_⊨s_≈_∶_ : Ctxs → Substs → Substs → Ctxs → Set
Γ ⊨s σ ≈ σ′ ∶ Δ = Σ (⊨ Γ) λ ⊨Γ → Σ (⊨ Δ) λ ⊨Δ → ∀ {ρ ρ′} (ρ≈ρ′ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ) → RelSubsts σ ρ σ′ ρ′ ⟦ ⊨Δ ⟧ρ

_⊨s_∶_ : Ctxs → Substs → Ctxs → Set
Γ ⊨s σ ∶ Δ = Γ ⊨s σ ≈ σ ∶ Δ

RelExp⇒RepTyp : RelExp T ρ T′ ρ′ 𝕌∞ → RelTyp T ρ T′ ρ′
RelExp⇒RepTyp rel = record
  { ⟦T⟧   = ⟦t⟧
  ; ⟦T′⟧  = ⟦t′⟧
  ; ↘⟦T⟧  = ↘⟦t⟧
  ; ↘⟦T′⟧ = ↘⟦t′⟧
  ; T≈T′  = t≈t′
  ; nat   = nat
  ; nat′  = nat′
  }
  where open RelExp rel

RelExp⇒RepTyp′ : ∀ {i} → RelExp T ρ T′ ρ′ (𝕌 i) → RelTyp T ρ T′ ρ′
RelExp⇒RepTyp′ rel = record
  { ⟦T⟧   = ⟦t⟧
  ; ⟦T′⟧  = ⟦t′⟧
  ; ↘⟦T⟧  = ↘⟦t⟧
  ; ↘⟦T′⟧ = ↘⟦t′⟧
  ; T≈T′  = _ , t≈t′
  ; nat   = nat
  ; nat′  = nat′
  }
  where open RelExp rel
