{-# OPTIONS --without-K --safe #-}

module NonCumulative.Ascribed.Statics.Simpl where

open import Lib

open import NonCumulative.Ascribed.Statics.Full
open import NonCumulative.Ascribed.Statics.Refl
open import NonCumulative.Ascribed.Statics.Presup
open import NonCumulative.Ascribed.Statics.CtxEquiv
open import NonCumulative.Ascribed.Statics.Inversion
open import NonCumulative.Ascribed.Statics.Misc

∷-cong-simp : ∀ {i} →
              ⊢ Γ ≈ Δ →
              Γ ⊢ T ≈ T′ ∶[ 1 + i ] Se i →
              ----------------
              ⊢ (T ↙ i) ∷ Γ ≈ (T′ ↙ i) ∷ Δ
∷-cong-simp Γ≈Δ T≈T′
  with presup-≈ T≈T′
...  | _ , ⊢T , ⊢T′ , _ = ∷-cong Γ≈Δ ⊢T (ctxeq-tm Γ≈Δ ⊢T′) T≈T′ (ctxeq-≈ Γ≈Δ T≈T′)

Π-cong-simp : ∀ {i j k} →
              Γ ⊢ S ≈ S′ ∶[ 1 + i ] Se i →
              (S ↙ i) ∷ Γ ⊢ T ≈ T′ ∶[ 1 + j ] Se j →
              k ≡ max i j →
              ------------------------------------------
              Γ ⊢ Π (S ↙ i) (T ↙ j) ≈ Π (S′ ↙ i) (T′ ↙ j) ∶[ 1 + k ] Se k
Π-cong-simp S≈S′ T≈T′ k≡maxij
  with _ , ⊢S , _ ← presup-≈ S≈S′ = Π-cong ⊢S S≈S′ T≈T′ k≡maxij

rec-cong-simp : ∀ {i} →
                N₀ ∷ Γ ⊢ T ≈ T′ ∶[ 1 + i ] Se i →
                Γ ⊢ s ≈ s′ ∶[ i ] T [| ze ∶ N₀ ] →
                (T ↙ i) ∷ N₀ ∷ Γ ⊢ r ≈ r′ ∶[ i ] T [ (wk ∘ wk) , su (v 1) ∶ N₀ ] →
                Γ ⊢ t ≈ t′ ∶[ 0 ] N →
                --------------------------------------------
                Γ ⊢ rec (T ↙ i) s r t ≈ rec (T′ ↙ i) s′ r′ t′ ∶[ i ] T [| t ∶ N₀ ]
rec-cong-simp  T≈T′ s≈s′ r≈r′ t≈t′
  with _ , ⊢T , _ , _ ← presup-≈ T≈T′ = rec-cong ⊢T T≈T′ s≈s′ r≈r′ t≈t′

Λ-cong-simp : ∀ {i j k} →
              Γ ⊢ S ≈ S′ ∶[ 1 + i ] Se i →
              (S ↙ i) ∷ Γ ⊢ t ≈ t′ ∶[ j ] T →
              k ≡ max i j →
              --------------------------------
              Γ ⊢ Λ (S ↙ i) t ≈ Λ (S′ ↙ i) t′ ∶[ k ] Π (S ↙ i) (T ↙ j)
Λ-cong-simp S≈S′ t≈t′ k≡maxij
  with _ , ⊢S , _ ← presup-≈ S≈S′ = Λ-cong ⊢S S≈S′ t≈t′ k≡maxij

[]-cong-Se-simp : ∀ {i} → Δ ⊢ T ≈ T′ ∶[ 1 + i ] Se i → Γ ⊢s σ ≈ σ′ ∶ Δ → Γ ⊢ T [ σ ] ≈ T′ [ σ′ ] ∶[ 1 + i ] Se i
[]-cong-Se-simp T≈T′ σ≈σ′
  with _ , ⊢σ , _ ← presup-s-≈ σ≈σ′ 
  = []-cong-Se T≈T′ ⊢σ σ≈σ′

[]-cong-Se-simp′ : ∀ {i} → Δ ⊢ T ∶[ 1 + i ] Se i → Γ ⊢s σ ≈ σ′ ∶ Δ → Γ ⊢ T [ σ ] ≈ T [ σ′ ] ∶[ 1 + i ] Se i
[]-cong-Se-simp′ ⊢T σ≈σ′ = []-cong-Se-simp (≈-refl ⊢T) σ≈σ′

,-cong-simp : ∀ {i} →
              Γ ⊢s σ ≈ σ′ ∶ Δ →
              Δ ⊢ T ≈ T′ ∶[ 1 + i ] Se i →
              Γ ⊢ t ≈ t′ ∶[ i ] T [ σ ] →
              -----------------------------
              Γ ⊢s σ , t ∶ T ↙ i ≈ σ′ , t′ ∶ T′ ↙ i ∶ (T ↙ i) ∷ Δ
,-cong-simp σ≈σ′ T≈T′ t≈t′
  with _ , ⊢T , _ ← presup-≈ T≈T′
  = ,-cong σ≈σ′ ⊢T T≈T′ t≈t′

$-cong-simp : ∀ {i j k} →
              Γ ⊢ r ≈ r′ ∶[ k ] Π (S ↙ i) (T ↙ j) →
              Γ ⊢ s ≈ s′ ∶[ i ] S →
              k ≡ max i j →
              -------------------------------
              Γ ⊢ r $ s ≈ r′ $ s′ ∶[ j ] T [| s ∶ S ↙ i ]
$-cong-simp r≈r′ s≈s′ k≡maxij
  with _ , _ , _ , ⊢ΠST ← presup-≈ r≈r′
  with _ , ⊢S , ⊢T ← Π-inv ⊢ΠST
  = $-cong ⊢S ⊢T r≈r′ s≈s′ k≡maxij