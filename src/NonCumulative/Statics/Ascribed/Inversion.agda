{-# OPTIONS --without-K --safe #-}

module NonCumulative.Statics.Ascribed.Inversion where

open import Lib
open import Data.Nat.Properties as ℕₚ

open import NonCumulative.Statics.Ascribed.Full
open import NonCumulative.Statics.Ascribed.Properties
open import NonCumulative.Statics.Ascribed.Presup
open import NonCumulative.Statics.Ascribed.Refl
open import NonCumulative.Statics.Ascribed.CtxEquiv
open import NonCumulative.Statics.Ascribed.Misc
open import NonCumulative.Statics.Ascribed.Properties.Contexts
open import NonCumulative.Statics.Ascribed.Properties.Subst

Λ-inv′ : ∀ {i k R} →
         Γ ⊢ Λ (S ↙ i) t ∶[ k ] R → 
         ∃₂ λ j T → Γ ⊢ R ≈ Π (S ↙ i) (T ↙ j) ∶[ 1 + k ] Se k × k ≡ max i j × (S ↙ i) ∷ Γ ⊢ t ∶[ j ] T
Λ-inv′ (Λ-I {T = T} {j = j} ⊢S ⊢t k≡maxij) = _ , _ , ≈-refl (Π-wf ⊢S (proj₂ (presup-tm ⊢t)) k≡maxij) , k≡maxij , ⊢t
Λ-inv′ (conv ⊢t x) 
  with Λ-inv′ ⊢t 
... | j , T , ≈R , k≡maxij , ⊢t = _ , _ , ≈-trans (≈-sym x) ≈R , k≡maxij , ⊢t 

su-inv : ∀ {i } →
         Γ ⊢ su t ∶[ i ] T →
         i ≡ 0 × Γ ⊢ T ≈ N ∶[ 1 ] Se 0 × Γ ⊢ t ∶[ 0 ] N
su-inv (su-I ⊢t) = refl , ≈-refl (N-wf (proj₁ (presup-tm ⊢t))) , ⊢t
su-inv (conv ⊢sut T≈) 
  with su-inv ⊢sut 
... | refl , ≈N , ⊢t = refl , ≈-trans (≈-sym T≈) ≈N , ⊢t

$-inv : ∀ {i R} →
         Γ ⊢ r $ s ∶[ i ] R →
         ∃₂ λ j k → ∃₂ λ S T → Γ ⊢ r ∶[ k ] Π (S ↙ j) (T ↙ i) × Γ ⊢ s ∶[ j ] S × k ≡ max j i × (Γ ⊢ R ≈ T [ I , s ∶ S ↙ j ] ∶[ 1 + i ] Se i)
$-inv (Λ-E ⊢S ⊢T ⊢r ⊢s x) = _ , _ , _ , _ , ⊢r , ⊢s , x , []-cong-Se′ (≈-refl ⊢T) (s-, (s-I (proj₁ (presup-tm ⊢S))) ⊢S (conv ⊢s (≈-sym ([I] ⊢S))))
$-inv (conv ⊢rs T≈) 
  with $-inv ⊢rs
... | j , k , S , T , ⊢r , ⊢s , refl , ≈Ts = _ , _ , _ , _ , ⊢r , ⊢s , refl , ≈-trans (≈-sym T≈) ≈Ts

t[σ]-inv : ∀ {i T} →
           Γ ⊢ t [ σ ] ∶[ i ] T →
           ∃₂ λ Δ S → Γ ⊢s σ ∶ Δ × Δ ⊢ t ∶[ i ] S × Γ ⊢ T ≈ S [ σ ] ∶[ 1 + i ] Se i
t[σ]-inv (t[σ] ⊢t ⊢σ) = _ , _ , ⊢σ , ⊢t , []-cong-Se′ (≈-refl (proj₂ (presup-tm ⊢t))) ⊢σ 
t[σ]-inv (conv ⊢t ≈T) 
  with t[σ]-inv ⊢t
... | Δ , S , ⊢σ , ⊢t , ≈S[σ] = _ , _ , ⊢σ , ⊢t , ≈-trans (≈-sym ≈T) ≈S[σ]        