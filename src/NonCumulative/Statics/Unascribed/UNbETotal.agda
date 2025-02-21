{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

module NonCumulative.Statics.Unascribed.UNbETotal (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂) where

open import Lib hiding (lookup)
open import NonCumulative.Statics.Ascribed.Full as A
open import NonCumulative.Semantics.Domain as A
open import NonCumulative.Semantics.Evaluation as A
open import NonCumulative.Semantics.Readback as A
open import NonCumulative.Statics.Unascribed.Full as U
open import NonCumulative.Statics.Unascribed.Domain as U
open import NonCumulative.Statics.Unascribed.Evaluation as U
open import NonCumulative.Statics.Unascribed.Readback as U


mutual
    ⌊_⌋ : A.Exp → U.Exp
    ⌊ N ⌋ = N
    ⌊ Π (S ↙ _) (T ↙ _) ⌋ = Π ⌊ S ⌋ ⌊ T ⌋
    ⌊ Liftt i (T ↙ j) ⌋ = Liftt i ⌊ T ⌋
    ⌊ Se i ⌋ = Se i
    ⌊ v x ⌋ = v x
    ⌊ ze ⌋ = ze
    ⌊ su t ⌋ = su ⌊ t ⌋
    ⌊ rec (T ↙ i) r s t ⌋ = rec ⌊ T ⌋ ⌊ r ⌋ ⌊ s ⌋ ⌊ t ⌋
    ⌊ Λ (S ↙ _) t ⌋ = Λ ⌊ S ⌋ ⌊ t ⌋
    ⌊ r $ s ⌋ = ⌊ r ⌋ $ ⌊ s ⌋
    ⌊ liftt i t ⌋ = liftt i ⌊ t ⌋
    ⌊ unlift t ⌋ = unlift ⌊ t ⌋
    ⌊ sub t σ ⌋ = sub ⌊ t ⌋ ⌊ σ ⌋ˢ

    ⌊_⌋ˢ : A.Subst → U.Subst
    ⌊ I ⌋ˢ = I
    ⌊ wk ⌋ˢ = wk
    ⌊ σ ∘ τ ⌋ˢ = ⌊ σ ⌋ˢ ∘ ⌊ τ ⌋ˢ
    ⌊ σ , s ∶ T ↙ _ ⌋ˢ = ⌊ σ ⌋ˢ , ⌊ s ⌋ ∶ ⌊ T ⌋

mutual 
    ⌊_⌋ⁿᶠ : A.Nf → U.Nf
    ⌊ ne u ⌋ⁿᶠ = ne ⌊ u ⌋ⁿᵉ 
    ⌊ N ⌋ⁿᶠ = N
    ⌊ Π (V ↙ _) (W ↙ _) ⌋ⁿᶠ = Π ⌊ V ⌋ⁿᶠ ⌊ W ⌋ⁿᶠ 
    ⌊ Liftt i (T ↙ j) ⌋ⁿᶠ = Liftt i ⌊ T ⌋ⁿᶠ 
    ⌊ Se i ⌋ⁿᶠ = Se i
    ⌊ ze ⌋ⁿᶠ = ze
    ⌊ su w ⌋ⁿᶠ = su ⌊ w ⌋ⁿᶠ 
    ⌊ Λ (W ↙ i) w ⌋ⁿᶠ = Λ ⌊ W ⌋ⁿᶠ ⌊ w ⌋ⁿᶠ 
    ⌊ liftt i w ⌋ⁿᶠ = liftt i ⌊ w ⌋ⁿᶠ
    
    ⌊_⌋ⁿᵉ : A.Ne → U.Ne
    ⌊ v x ⌋ⁿᵉ = v x
    ⌊ rec (W ↙ _) z s u ⌋ⁿᵉ = rec ⌊ W ⌋ⁿᶠ ⌊ z ⌋ⁿᶠ ⌊ s ⌋ⁿᶠ ⌊ u ⌋ⁿᵉ 
    ⌊ u $ w ⌋ⁿᵉ = ⌊ u ⌋ⁿᵉ $ ⌊ w ⌋ⁿᶠ
    ⌊ unlift u ⌋ⁿᵉ = unlift ⌊ u ⌋ⁿᵉ
    
mutual
    ⌊_⌋ᵈᶠ : A.Df → U.Df
    ⌊ ↓ i A a ⌋ᵈᶠ = ↓ ⌊ A ⌋ᵈ ⌊ a ⌋ᵈ

    ⌊_⌋ᵈ : A.D → U.D
    ⌊ N ⌋ᵈ = N 
    ⌊ Π _ a (T ↙ i) ρ ⌋ᵈ = Π ⌊ a ⌋ᵈ ⌊ T ⌋ λ n → ⌊ ρ n ⌋ᵈ
    ⌊ U i ⌋ᵈ = U i 
    ⌊ Li i j a ⌋ᵈ = Li i ⌊ a ⌋ᵈ
    ⌊ ze ⌋ᵈ = ze
    ⌊ su a ⌋ᵈ = su ⌊ a ⌋ᵈ
    ⌊ Λ t ρ ⌋ᵈ = Λ ⌊ t ⌋ (λ n → ⌊ ρ n ⌋ᵈ)
    ⌊ li i a ⌋ᵈ = li i ⌊ a ⌋ᵈ
    ⌊ ↑ i A e ⌋ᵈ = ↑ ⌊ A ⌋ᵈ ⌊ e ⌋ᵈⁿ

    ⌊_⌋ᵈⁿ : A.Dn → U.Dn
    ⌊ l x ⌋ᵈⁿ = l x   
    ⌊ rec (T ↙ i) a t ρ e ⌋ᵈⁿ = rec ⌊ T ⌋ ⌊ a ⌋ᵈ ⌊ t ⌋ (λ n → ⌊ ρ n ⌋ᵈ) ⌊ e ⌋ᵈⁿ
    ⌊ e $ d ⌋ᵈⁿ = ⌊ e ⌋ᵈⁿ $ ⌊ d ⌋ᵈᶠ
    ⌊ unli e ⌋ᵈⁿ = unli ⌊ e ⌋ᵈⁿ

↦-⌊⌋-comm : ∀ ρ a → 
            (λ n → ⌊ (ρ A.↦ a) n ⌋ᵈ) ≡ ((λ n → ⌊ ρ n ⌋ᵈ) U.↦ ⌊ a ⌋ᵈ )
↦-⌊⌋-comm ρ a = fext helper
  where
    helper : ∀ n → _ ≡ _ 
    helper ℕ.zero = refl
    helper (ℕ.suc n) = refl

mutual
  ⟦⟧-⌊⌋-total : A.⟦ A.t ⟧ A.ρ ↘ A.a → 
                (U.⟦ ⌊ A.t ⌋ ⟧ (λ n → ⌊ A.ρ n ⌋ᵈ) ↘ ⌊ A.a ⌋ᵈ)
  ⟦⟧-⌊⌋-total ⟦N⟧ = ⟦N⟧
  ⟦⟧-⌊⌋-total (⟦Π⟧ ⟦t⟧) = ⟦Π⟧ (⟦⟧-⌊⌋-total ⟦t⟧)
  ⟦⟧-⌊⌋-total (⟦Liftt⟧ ⟦t⟧) = ⟦Liftt⟧ (⟦⟧-⌊⌋-total ⟦t⟧)
  ⟦⟧-⌊⌋-total (⟦Se⟧ i) = ⟦Se⟧ i
  ⟦⟧-⌊⌋-total (⟦v⟧ n) = ⟦v⟧ n
  ⟦⟧-⌊⌋-total ⟦ze⟧ = ⟦ze⟧
  ⟦⟧-⌊⌋-total (⟦su⟧ ⟦t⟧) = ⟦su⟧ ( ⟦⟧-⌊⌋-total ⟦t⟧ )
  ⟦⟧-⌊⌋-total (⟦rec⟧ ⟦r⟧ ⟦t⟧ rec∙a) = ⟦rec⟧ (⟦⟧-⌊⌋-total ⟦r⟧) (⟦⟧-⌊⌋-total ⟦t⟧) (rec∙-⌊⌋-total rec∙a)
  ⟦⟧-⌊⌋-total (⟦Λ⟧ t) = ⟦Λ⟧ ⌊ t ⌋
  ⟦⟧-⌊⌋-total (⟦$⟧ ⟦r⟧ ⟦s⟧ f∙a) = ⟦$⟧ (⟦⟧-⌊⌋-total ⟦r⟧) (⟦⟧-⌊⌋-total ⟦s⟧) (∙-⌊⌋-total f∙a)
  ⟦⟧-⌊⌋-total (⟦liftt⟧ ⟦t⟧) = ⟦liftt⟧ (⟦⟧-⌊⌋-total ⟦t⟧)
  ⟦⟧-⌊⌋-total (⟦unlift⟧ ⟦t⟧ unli∙a) = ⟦unlift⟧ (⟦⟧-⌊⌋-total ⟦t⟧) (unli∙-⌊⌋-total unli∙a)
  ⟦⟧-⌊⌋-total (⟦[]⟧ ⟦σ⟧ ⟦t⟧) = ⟦[]⟧ (⟦⟧ˢ-⌊⌋-total ⟦σ⟧) (⟦⟧-⌊⌋-total ⟦t⟧)

  ⟦⟧ˢ-⌊⌋-total : A.⟦ A.σ ⟧s A.ρ ↘ A.ρ′ → 
                 U.⟦ ⌊ A.σ ⌋ˢ ⟧s (λ n → ⌊ A.ρ n ⌋ᵈ) ↘ (λ n → ⌊ A.ρ′ n ⌋ᵈ)
  ⟦⟧ˢ-⌊⌋-total ⟦I⟧ = ⟦I⟧ 
  ⟦⟧ˢ-⌊⌋-total ⟦wk⟧ = ⟦wk⟧
  ⟦⟧ˢ-⌊⌋-total (⟦,⟧ {ρ′ = ρ′} {a = a} ⟦σ⟧ ⟦t⟧) 
    rewrite ↦-⌊⌋-comm ρ′ a
    = ⟦,⟧ (⟦⟧ˢ-⌊⌋-total ⟦σ⟧) (⟦⟧-⌊⌋-total ⟦t⟧) 
  ⟦⟧ˢ-⌊⌋-total (⟦∘⟧ ⟦σ⟧ ⟦τ⟧) = ⟦∘⟧ (⟦⟧ˢ-⌊⌋-total ⟦σ⟧) (⟦⟧ˢ-⌊⌋-total ⟦τ⟧)  

  ∙-⌊⌋-total : A.f A.∙ A.a ↘ A.b → 
               ⌊ A.f ⌋ᵈ U.∙ ⌊ A.a ⌋ᵈ ↘ ⌊ A.b ⌋ᵈ
  ∙-⌊⌋-total (Λ∙ {ρ = ρ} {a = a} ⟦t⟧)
    with ⟦t⟧′ ← ⟦⟧-⌊⌋-total ⟦t⟧
    rewrite (↦-⌊⌋-comm ρ a)
    = Λ∙ ⟦t⟧′ 
  ∙-⌊⌋-total ($∙ {ρ = ρ} {a = a} A c ⟦T⟧) 
    with ⟦T⟧′ ← ⟦⟧-⌊⌋-total ⟦T⟧
    rewrite (↦-⌊⌋-comm ρ a)
    = $∙ _ _ ⟦T⟧′

  unli∙-⌊⌋-total : A.unli∙ A.a ↘ A.b → 
                   U.unli∙ ⌊ A.a ⌋ᵈ ↘ ⌊ A.b ⌋ᵈ
  unli∙-⌊⌋-total li↘ = li↘ 
  unli∙-⌊⌋-total unli↘ = unli↘

  rec∙-⌊⌋-total : ∀ {i} →  
                  A.rec∙ (A.T ↙ i) , A.a , A.r , A.ρ , A.b ↘ A.a′ → 
                  U.rec∙ ⌊ A.T ⌋ , ⌊ A.a ⌋ᵈ , ⌊ A.r ⌋ , (λ n → ⌊ A.ρ n ⌋ᵈ) , ⌊ A.b ⌋ᵈ ↘ ⌊ A.a′ ⌋ᵈ
  rec∙-⌊⌋-total ze↘ = ze↘ 
  rec∙-⌊⌋-total (su↘ {ρ = ρ} {b = b} {b′ = b′} {a′ = a′} rec∙b ⟦r⟧) 
    with ⟦r⟧′ ← ⟦⟧-⌊⌋-total ⟦r⟧
    rewrite (↦-⌊⌋-comm (ρ A.↦ b) b′)
    rewrite (↦-⌊⌋-comm ρ b)
    = su↘ (rec∙-⌊⌋-total rec∙b) ⟦r⟧′
  rec∙-⌊⌋-total (rec∙ {ρ = ρ} {A′ = A′} {c = c} {j = j} ⟦T⟧) 
    with ⟦T⟧′ ← ⟦⟧-⌊⌋-total ⟦T⟧
    rewrite (↦-⌊⌋-comm ρ (↑ j A′ c))
    = rec∙ ⟦T⟧′

mutual 
  Rf-⌊⌋-total : ∀ {n} →
                A.Rf n - A.d ↘ A.w → 
                U.Rf n - ⌊ A.d ⌋ᵈᶠ ↘ ⌊ A.w ⌋ⁿᶠ
  Rf-⌊⌋-total (RU′ _ ↘W) = RU _ (Rty-⌊⌋-total ↘W) 
  Rf-⌊⌋-total (Rze _) = Rze _
  Rf-⌊⌋-total (Rsu _ ↘w) = Rsu _ (Rf-⌊⌋-total ↘w)
  Rf-⌊⌋-total (RΛ {A = A} {ρ = ρ} {i = i} n ↘W ↘b ⟦T⟧ Rf-d) 
    with ⟦T⟧′ ← ⟦⟧-⌊⌋-total ⟦T⟧
    rewrite (↦-⌊⌋-comm ρ (↑ i A (l n)))
    = RΛ _ (Rty-⌊⌋-total ↘W) (∙-⌊⌋-total ↘b) ⟦T⟧′ (Rf-⌊⌋-total Rf-d)
  Rf-⌊⌋-total (Rli _ x Rf-d) = Rli _ (unli∙-⌊⌋-total x) (Rf-⌊⌋-total Rf-d) 
  Rf-⌊⌋-total (RN _ ↘u) = RN _ (Rne-⌊⌋-total ↘u)
  Rf-⌊⌋-total (Rne′ _ ↘u) = Rne _ (Rne-⌊⌋-total ↘u)

  Rne-⌊⌋-total : ∀ {n} →
                 A.Re n - A.c ↘ A.u → 
                 U.Re n - ⌊ A.c ⌋ᵈⁿ ↘ ⌊ A.u ⌋ⁿᵉ
  Rne-⌊⌋-total (Rl _ x) = Rl _ x 
  Rne-⌊⌋-total (R$ _ ↘u ↘w) = R$ _ (Rne-⌊⌋-total ↘u) (Rf-⌊⌋-total ↘w)
  Rne-⌊⌋-total (Rr {ρ = ρ} {A = A} {i = i} n ⟦T⟧ ↘W ⟦T⟧₁ ↘w ⟦t⟧ ⟦T⟧₂ ↘w₁ ↘u) 
    with ⟦T⟧′ ← ⟦⟧-⌊⌋-total ⟦T⟧
    with ⟦T⟧₁′ ← ⟦⟧-⌊⌋-total ⟦T⟧₁
    with ⟦T⟧₂′ ← ⟦⟧-⌊⌋-total ⟦T⟧₂
    with ⟦t⟧′ ← ⟦⟧-⌊⌋-total ⟦t⟧
    rewrite (↦-⌊⌋-comm ρ ze) 
    rewrite (↦-⌊⌋-comm ρ (su (↑ 0 N (l n)))) 
    rewrite (↦-⌊⌋-comm (ρ A.↦ ↑ 0 N (l n)) (↑ i A (l (1 + n)))) 
    rewrite (↦-⌊⌋-comm ρ (↑ 0 N (l n))) 
    = Rr _ ⟦T⟧′ (Rty-⌊⌋-total ↘W) ⟦T⟧₁′ (Rf-⌊⌋-total ↘w) ⟦t⟧′ ⟦T⟧₂′ (Rf-⌊⌋-total ↘w₁) (Rne-⌊⌋-total ↘u)
  Rne-⌊⌋-total (Runli _ ↘u) = Runli _ (Rne-⌊⌋-total ↘u)

  Rty-⌊⌋-total : ∀ {n i} →
                 A.Rty n - A.a at i ↘ A.W → 
                 U.Rty n - ⌊ A.a ⌋ᵈ  ↘ ⌊ A.W ⌋ⁿᶠ
  Rty-⌊⌋-total (RU _) = RU _ 
  Rty-⌊⌋-total (RN _) = RN _
  Rty-⌊⌋-total (RΠ  {A = A} {ρ = ρ} {i = j} n ↘V ⟦T⟧ ↘W) 
    with ⟦T⟧′ ← ⟦⟧-⌊⌋-total ⟦T⟧
    rewrite (↦-⌊⌋-comm ρ (↑ j A (l n)))
    = RΠ _ (Rty-⌊⌋-total ↘V) ⟦T⟧′ (Rty-⌊⌋-total ↘W)
  Rty-⌊⌋-total (RL _ ↘W) = RL _ (Rty-⌊⌋-total ↘W)
  Rty-⌊⌋-total (Rne′ _ ↘U) = Rne _ (Rne-⌊⌋-total ↘U)