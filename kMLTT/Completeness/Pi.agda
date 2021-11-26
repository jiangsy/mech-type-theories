{-# OPTIONS --without-K --safe #-}

module kMLTT.Completeness.Pi where


-- Π-[]       : ∀ {i} →
--              Γ ⊨s σ ∶ Δ →
--              Δ ⊨ S ∶ Se i →
--              S ∺ Δ ⊨ T ∶ Se i →
--              -------------------------------------------------
--              Γ ⊨ Π S T [ σ ] ≈ Π (S [ σ ]) (T [ q σ ]) ∶ Se i
-- Π-cong     : ∀ {i} →
--              Γ ⊨ S ≈ S′ ∶ Se i →
--              S ∺ Γ ⊨ T ≈ T′ ∶ Se i →
--              --------------------------
--              Γ ⊨ Π S T ≈ Π S′ T′ ∶ Se i
-- Λ-cong     : S ∺ Γ ⊨ t ≈ t′ ∶ T →
--              -----------------------
--              Γ ⊨ Λ t ≈ Λ t′ ∶ Π S T
-- $-cong     : Γ ⊨ r ≈ r′ ∶ Π S T →
--              Γ ⊨ s ≈ s′ ∶ S →
--              -------------------------------
--              Γ ⊨ r $ s ≈ r′ $ s′ ∶ T [| s ]
-- Λ-[]       : Γ ⊨s σ ∶ Δ →
--              S ∺ Δ ⊨ t ∶ T →
--              --------------------------------------------
--              Γ ⊨ Λ t [ σ ] ≈ Λ (t [ q σ ]) ∶ Π S T [ σ ]
-- $-[]       : Γ ⊨s σ ∶ Δ →
--              Δ ⊨ r ∶ Π S T →
--              Δ ⊨ s ∶ S →
--              ---------------------------------------------------------
--              Γ ⊨ (r $ s) [ σ ] ≈ r [ σ ] $ s [ σ ] ∶ T [ σ , s [ σ ] ]
-- Λ-β        : S ∺ Γ ⊨ t ∶ T →
--              Γ ⊨ s ∶ S →
--              ----------------------------------
--              Γ ⊨ Λ t $ s ≈ t [| s ] ∶ T [| s ]
-- Λ-η        : Γ ⊨ t ∶ Π S T →
--              ----------------------------------
--              Γ ⊨ t ≈ Λ (t [ wk ] $ v 0) ∶ Π S T
