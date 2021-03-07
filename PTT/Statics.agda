{-# OPTIONS --without-K --safe #-}

module PTT.Statics where

open import Lib

infixl 10 _$_
infixl 11 _[_] _[|_]

mutual
  Typ = Exp

  data Exp : Set where
    N    : Typ
    Π    : Typ → Typ → Typ
    Se   : (i : ℕ) → Typ
    v    : (x : ℕ) → Exp
    ze   : Exp
    su   : Exp → Exp
    rec  : (T : Typ) (z s t : Exp) → Exp
    Λ    : Exp → Exp
    _$_  : Exp → Exp → Exp
    _[_] : Exp → Subst → Exp

  infixl 3 _∘_
  data Subst : Set where
    ↑   : Subst
    I   : Subst
    _∘_ : Subst → Subst → Subst
    _,_ : Subst → Exp → Subst

infixr 5 _⟶_
_⟶_ : Typ → Typ → Typ
S ⟶ T = Π S (T [ ↑ ])

_[|_] : Exp → Exp → Exp
t [| s ] = t [ I , s ]

Env = List Typ

T-rec-su : Typ → Typ
T-rec-su T = Π N (Π ((T [ ↑ ] $ v 0)) (T [ ↑ ∘ ↑ ] $ su (v 1)))

q : Subst → Subst
q σ = (σ ∘ ↑) , v 0

mutual
  data Ne : Set where
    v   : (x : ℕ) → Ne
    rec : (T : Nf) (z s : Nf) → Ne → Ne
    _$_ : Ne → (n : Nf) → Ne

  data Nf : Set where
    ne : (u : Ne) → Nf
    ze : Nf
    su : Nf → Nf
    Λ  : Nf → Nf
    N  : Nf
    Π  : Nf → Nf → Nf
    Se : (i : ℕ) → Nf

variable
  S S′ S″ : Typ
  T T′ T″ : Typ
  Γ Γ′ Γ″ : Env
  Δ Δ′ Δ″ : Env
  t t′ t″ : Exp
  r r′ r″ : Exp
  s s′ s″ : Exp
  σ σ′ σ″ : Subst
  τ τ′ τ″ : Subst
  u u′ u″ : Ne
  w w′ w″ : Nf


mutual
  Ne⇒Exp : Ne → Exp
  Ne⇒Exp (v x)         = v x
  Ne⇒Exp (rec T z s u) = rec (Nf⇒Exp T) (Nf⇒Exp z) (Nf⇒Exp s) (Ne⇒Exp u)
  Ne⇒Exp (u $ n)       = Ne⇒Exp u $ Nf⇒Exp n

  Nf⇒Exp : Nf → Exp
  Nf⇒Exp (ne u)  = Ne⇒Exp u
  Nf⇒Exp ze      = ze
  Nf⇒Exp (su w)  = su (Nf⇒Exp w)
  Nf⇒Exp (Λ w)   = Λ (Nf⇒Exp w)
  Nf⇒Exp N       = N
  Nf⇒Exp (Π S T) = Π (Nf⇒Exp S) (Nf⇒Exp T)
  Nf⇒Exp (Se i)  = Se i

infix 2 _∶_∈!_
data _∶_∈!_ : ℕ → Typ → Env → Set where
  here : 0 ∶ T [ ↑ ] ∈! T ∷ Γ
  there : ∀ {n T S Γ} → n ∶ T ∈! Γ → suc n ∶ T [ ↑ ] ∈! S ∷ Γ

infix 4 ⊢_ ⊢_≲_ _⊢_ _⊢_∶_ _⊢s_∶_ _⊢_≲_ _⊢_≈_∶_ _⊢s_≈_∶_

mutual
  _⊢_ : Env → Typ → Set
  Γ ⊢ T = ∃ λ i → Γ ⊢ T ∶ Se i

  data ⊢_ : Env → Set where
    ⊢[] : ⊢ []
    ⊢∷  : ∀ {i} →
          ⊢ Γ →
          Γ ⊢ T ∶ Se i →
          ----------------
          ⊢ T ∷ Γ

  data ⊢_≲_ : Env → Env → Set where
    ≈[] : ⊢ [] ≲ []
    ≈∷  : ⊢ Γ ≲ Δ →
          Δ ⊢ S ≲ T →
          ⊢ S ∷ Γ ≲ T ∷ Δ

  data _⊢_∶_ : Env → Exp → Typ → Set where
    N-wf    : ∀ i →
              ⊢ Γ →
              -------------
              Γ ⊢ N ∶ Se i
    Se-wf   : ∀ {i j} →
              ⊢ Γ →
              i < j →
              ----------------
              Γ ⊢ Se i ∶ Se j
    Π-wf    : ∀ {i j k} →
              Γ ⊢ S ∶ Se i →
              S ∷ Γ ⊢ T ∶ Se j →
              i ≤ k → j ≤ k →
              --------------------
              Γ ⊢ Π S T ∶ Se k
    vlookup : ∀ {x} →
              ⊢ Γ →
              x ∶ T ∈! Γ →
              ------------
              Γ ⊢ v x ∶ T
    ze-I    : ⊢ Γ →
              -----------
              Γ ⊢ ze ∶ N
    su-I    : Γ ⊢ t ∶ N →
              -------------
              Γ ⊢ su t ∶ N
    N-E     : ∀ {i} →
              Γ ⊢ T ∶ Π N (Se i) →
              Γ ⊢ s ∶ T $ ze →
              Γ ⊢ r ∶ T-rec-su T →
              Γ ⊢ t ∶ N →
              --------------------------
              Γ ⊢ rec T s r t ∶ T $ t
    Λ-I     : ∀ {i} →
              Γ ⊢ S ∶ Se i →
              S ∷ Γ ⊢ t ∶ T →
              ------------------
              Γ ⊢ Λ t ∶ Π S T
    Λ-E     : Γ ⊢ r ∶ Π S T →
              Γ ⊢ s ∶ S →
              ---------------------
              Γ ⊢ r $ s ∶ T [| s ]
    t[σ]    : Δ ⊢ t ∶ T →
              Γ ⊢s σ ∶ Δ →
              ---------------------
              Γ ⊢ t [ σ ] ∶ T [ σ ]
    conv    : Γ ⊢ t ∶ S →
              Γ ⊢ S ≲ T →
              ------------
              Γ ⊢ t ∶ T

  data _⊢s_∶_ : Env → Subst → Env → Set where
    S-↑    : ⊢ S ∷ Γ →
             ---------------
             S ∷ Γ ⊢s ↑ ∶ Γ
    S-I    : ⊢ Γ →
             ------------
             Γ ⊢s I ∶ Γ
    S-∘    : Γ ⊢s τ ∶ Γ′ →
             Γ′ ⊢s σ ∶ Γ″ →
             ----------------
             Γ ⊢s σ ∘ τ ∶ Γ″
    S-,    : ∀ {i} →
             Γ ⊢s σ ∶ Δ →
             Δ ⊢ S ∶ Se i →
             Γ ⊢ s ∶ S [ σ ] →
             -------------------
             Γ ⊢s σ , s ∶ S ∷ Δ
    S-conv : ⊢ Δ ≲ Δ′ →
             Γ ⊢s σ ∶ Δ →
             --------------
             Γ ⊢s σ ∶ Δ′

  data _⊢_≲_ : Env → Typ → Typ → Set where
    Se-≲ : ∀ {i j} →
           ⊢ Γ →
           i ≤ j →
           ----------------
           Γ ⊢ Se i ≲ Se j
    ≈-≲  : ∀ {i} →
           Γ ⊢ S ≈ T ∶ Se i →
           -------------------
           Γ ⊢ S ≲ T

  data _⊢_≈_∶_ : Env → Exp → Exp → Typ → Set where
    N-[]     : ∀ i →
               Γ ⊢s σ ∶ Δ →
               -----------------------
               Γ ⊢ N [ σ ] ≈ N ∶ Se i
    Se-[]    : ∀ {i j} →
               Γ ⊢s σ ∶ Δ →
               i < j →
               ----------------------------------
               Γ ⊢ Se i [ σ ] ≈ Se i ∶ Se j
    Π-[]     : ∀ {i j k} →
               Γ ⊢s σ ∶ Δ →
               Δ ⊢ S ∶ Se i →
               S ∷ Δ ⊢ T ∶ Se j →
               i ≤ k → j ≤ k →
               ------------------------
               Γ ⊢ Π S T [ σ ] ≈ Π (S [ σ ]) (T [ q σ ]) ∶ Se k
    Π-cong   : ∀ {i j k i′} →
               Γ ⊢ S ∶ Se i′ →
               Γ ⊢ S ≈ S′ ∶ Se i →
               S ∷ Γ ⊢ T ≈ T′ ∶ Se j →
               i ≤ k → j ≤ k →
               ------------------------
               Γ ⊢ Π S T ≈ Π S′ T′ ∶ Se k
    v-≈      : ∀ {x} →
               ⊢ Γ →
               x ∶ T ∈! Γ →
               -----------------
               Γ ⊢ v x ≈ v x ∶ T
    ze-≈     : ⊢ Γ →
               ----------------
               Γ ⊢ ze ≈ ze ∶ N
    su-cong  : Γ ⊢ t ≈ t′ ∶ N →
               --------- ------------
               Γ ⊢ su t ≈ su t′ ∶ N
    rec-cong : ∀ {i} →
               Γ ⊢ T ≈ T″ ∶ Π N (Se i) →
               Γ ⊢ s ≈ s′ ∶ T $ ze →
               Γ ⊢ r ≈ r′ ∶ T-rec-su T →
               Γ ⊢ t ≈ t′ ∶ N →
               ------------------------------------------
               Γ ⊢ rec T s r t ≈ rec T″ s′ r′ t′ ∶ T $ t
    Λ-cong   : S ∷ Γ ⊢ t ≈ t′ ∶ T →
               -----------------------
               Γ ⊢ Λ t ≈ Λ t′ ∶ Π S T
    $-cong   : Γ ⊢ r ≈ r′ ∶ Π S T →
               Γ ⊢ s ≈ s′ ∶ S →
               -------------------------------
               Γ ⊢ r $ s ≈ r′ $ s′ ∶ T [| s ]
    []-cong  : Γ ⊢s σ ≈ σ′ ∶ Δ →
               Δ ⊢ t ≈ t′ ∶ T →
               ----------------------------
               Γ ⊢ t [ σ ] ≈ t′ [ σ′ ] ∶ T [ σ ]
    ze-[]    : Γ ⊢s σ ∶ Δ →
               ----------------------
               Γ ⊢ ze [ σ ] ≈ ze ∶ N
    su-[]    : Γ ⊢s σ ∶ Δ →
               Δ ⊢ t ∶ N →
               ----------------------------------
               Γ ⊢ su t [ σ ] ≈ su (t [ σ ]) ∶ N
    Λ-[]     : Γ ⊢s σ ∶ Δ →
               S ∷ Δ ⊢ t ∶ T →
               --------------------------------------------
               Γ ⊢ Λ t [ σ ] ≈ Λ (t [ q σ ]) ∶ Π S T [ σ ]
    $-[]     : Γ ⊢s σ ∶ Δ →
               Δ ⊢ r ∶ Π S T →
               Δ ⊢ s ∶ S →
               -----------------------------------------------------
               Γ ⊢ (r $ s) [ σ ] ≈ r [ σ ] $ s [ σ ] ∶ T [| s [ σ ] ]
    rec-[]   : ∀ {i} →
               Γ ⊢s σ ∶ Δ →
               Δ ⊢ T ∶ Π N (Se i) →
               Δ ⊢ s ∶ T $ ze →
               Δ ⊢ r ∶ T-rec-su T →
               Δ ⊢ t ∶ N →
               -------------------------------------------------------------------------
               Γ ⊢ rec T s r t [ σ ] ≈ rec T (s [ σ ]) (r [ σ ]) (t [ σ ]) ∶ T [ σ ] $ t
    rec-β-ze : ∀ {i} →
               Γ ⊢ T ∶ Π N (Se i) →
               Γ ⊢ s ∶ T $ ze →
               Γ ⊢ r ∶ T-rec-su T →
               --------------------------------
               Γ ⊢ rec T s r ze ≈ s ∶ T $ ze
    rec-β-su : ∀ {i} →
               Γ ⊢ T ∶ Π N (Se i) →
               Γ ⊢ s ∶ T $ ze →
               Γ ⊢ r ∶ T-rec-su T →
               Γ ⊢ t ∶ N →
               -------------------------------------------------------
               Γ ⊢ rec T s r (su t) ≈ r $ t $ (rec T s r t) ∶ T $ su t
    Λ-β      : S ∷ Γ ⊢ t ∶ T →
               Γ ⊢ s ∶ S →
               ----------------------------------
               Γ ⊢ Λ t $ s ≈ t [| s ] ∶ T [| s ]
    Λ-η      : Γ ⊢ t ∶ Π S T →
               ----------------------------------
               Γ ⊢ t ≈ Λ (t [ ↑ ] $ v 0) ∶ Π S T
    [I]      : Γ ⊢ t ∶ T →
               --------------------
               Γ ⊢ t [ I ] ≈ t ∶ T
    ↑-lookup : ∀ {x} →
               ⊢ S ∷ Γ →
               x ∶ T ∈! Γ →
               ---------------------------------------
               S ∷ Γ ⊢ v x [ ↑ ] ≈ v (suc x) ∶ T [ ↑ ]
    [∘]      : Γ ⊢s τ ∶ Γ′ →
               Γ′ ⊢s σ ∶ Γ″ →
               Γ″ ⊢ t ∶ T →
               ---------------------------------------------
               Γ ⊢ t [ σ ∘ τ ] ≈ t [ σ ] [ τ ] ∶ T [ σ ∘ τ ]
    [,]-v-ze : ∀ {i} →
               Γ ⊢s σ ∶ Δ →
               Δ ⊢ S ∶ Se i →
               Γ ⊢ s ∶ S [ σ ] →
               --------------------------------
               Γ ⊢ v 0 [ σ , s ] ≈ s ∶ S [ σ ]
    [,]-v-su : ∀ {i x} →
               Γ ⊢s σ ∶ Δ →
               Δ ⊢ S ∶ Se i →
               Γ ⊢ s ∶ S [ σ ] →
               x ∶ T ∈! Δ →
               ---------------------------------------------
               Γ ⊢ v (suc x) [ σ , s ] ≈ v x [ σ ] ∶ T [ σ ]
    ≈-conv   : Γ ⊢ s ≈ t ∶ S →
               Γ ⊢ S ≲ T →
               --------------------
               Γ ⊢ s ≈ t ∶ T
    ≈-sym    : Γ ⊢ t ≈ t′ ∶ T →
               ----------------
               Γ ⊢ t′ ≈ t ∶ T
    ≈-trans  : Γ ⊢ t ≈ t′ ∶ T →
               Γ ⊢ t′ ≈ t″ ∶ T →
               ------ ------------
               Γ ⊢ t ≈ t″ ∶ T

  data _⊢s_≈_∶_ : Env → Subst → Subst → Env → Set where
    ↑-≈       : ⊢ S ∷ Γ →
                ------------------
                S ∷ Γ ⊢s ↑ ≈ ↑ ∶ Γ
    I-≈       : ⊢ Γ →
                ---------------
                Γ ⊢s I ≈ I ∶ Γ
    ∘-cong    : Γ ⊢s τ ≈ τ′ ∶ Γ′ →
                Γ′ ⊢s σ ≈ σ′ ∶ Γ″ →
                -----------------------------------------
                Γ ⊢s σ ∘ τ ≈ σ′ ∘ τ′ ∶ Γ″
    ,-cong    : ∀ {i} →
                Δ ⊢ S ∶ Se i →
                Γ ⊢s σ ≈ σ′ ∶ Δ →
                Γ ⊢ s ≈ s′ ∶ S [ σ ] →
                ------------------------------
                Γ ⊢s σ , s ≈ σ′ , s′ ∶ S ∷ Δ
    ↑-∘-,     : ∀ {i} →
                Γ ⊢s σ ∶ Δ →
                Δ ⊢ S ∶ Se i →
                Γ ⊢ s ∶ S [ σ ] →
                --------------------------
                Γ ⊢s ↑ ∘ (σ , s) ≈ σ ∶ Δ
    I-∘       : Γ ⊢s σ ∶ Δ →
                ---------------------------------------
                Γ ⊢s I ∘ σ ≈ σ ∶ Δ
    ∘-I       : Γ ⊢s σ ∶ Δ →
                -------------------
                Γ ⊢s σ ∘ I ≈ σ ∶ Δ
    ∘-assoc   : ∀ {Γ‴} →
                Γ′ ⊢s σ ∶ Γ →
                Γ″ ⊢s σ′ ∶ Γ′ →
                Γ‴ ⊢s σ″ ∶ Γ″ →
                ---------------------------------------
                Γ‴ ⊢s σ ∘ σ′ ∘ σ″ ≈ σ ∘ (σ′ ∘ σ″) ∶ Γ
    ,-ext     : Γ ⊢s σ ∶ S ∷ Δ →
                -------------------------------------
                Γ ⊢s σ ≈ (↑ ∘ σ) , v 0 [ σ ] ∶ S ∷ Δ
    S-≈-conv  : ⊢ Δ ≲ Δ′ →
                Γ ⊢s σ ≈ τ ∶ Δ →
                -----------------
                Γ ⊢s σ ≈ τ ∶ Δ′
    S-≈-sym   : Γ ⊢s σ ≈ σ′ ∶ Δ →
                ------------------
                Γ ⊢s σ′ ≈ σ ∶ Δ
    S-≈-trans : Γ ⊢s σ ≈ σ′ ∶ Δ →
                Γ ⊢s σ′ ≈ σ″ ∶ Δ →
                -------------------
                Γ ⊢s σ ≈ σ″ ∶ Δ
