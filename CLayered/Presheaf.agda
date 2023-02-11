{-# OPTIONS --without-K --safe #-}

module CLayered.Presheaf where

open import Data.List.Relation.Unary.Any.Properties
open import Data.List.Relation.Unary.All.Properties

open import CLayered.Typ

open All′ using (lookup) public


record Monotone {C : Set} (A : C → Set) (R : C → C → Set) : Set where
  infixl 8 _[_]
  field
    _[_] : ∀ {c c′} → A c′ → R c c′ → A c

open Monotone {{...}} public


-- Definitions of expressions, normal forms and neutral forms
-------------------------------------------------------------

infixl 10 _$_

mutual

  data Exp : Layer → GCtx → LCtx → Typ → Set where
    var  : gwfs? Ψ → wfs? i Γ → T ∈ Γ → Exp i Ψ Γ T
    gvar : LSubst i Ψ Γ Δ → (Δ , T) ∈ Ψ → Exp i Ψ Γ T
    zero : gwfs? Ψ → wfs? i Γ → Exp i Ψ Γ N
    succ : Exp i Ψ Γ N → Exp i Ψ Γ N
    Λ    : Exp i Ψ (S ∷ Γ) T → Exp i Ψ Γ (S ⟶ T)
    _$_  : Exp i Ψ Γ (S ⟶ T) → Exp i Ψ Γ S → Exp i Ψ Γ T
    box  : types? Γ → Exp zer Ψ Δ T → Exp one Ψ Γ (□ Δ T)
    mat  : Exp one Ψ Γ (□ Δ T′) → Branches Ψ Γ T (Δ , T′) → Exp one Ψ Γ T

  data LSubst : Layer → GCtx → LCtx → LCtx → Set where
    []  : gwfs? Ψ → wfs? i Γ → LSubst i Ψ Γ []
    _∷_ : Exp i Ψ Γ T → LSubst i Ψ Γ Δ → LSubst i Ψ Γ (T ∷ Δ)

  data Branch : ℕ → GCtx → LCtx → Typ → LCtx × Typ → Set where
    -- TODO: check here
    bvar  : cores? Δ → Exp one Ψ Γ T′ → Branch 0 Ψ Γ T′ (Δ , T)
    bzero : cores? Δ → Exp one Ψ Γ T′ → Branch 1 Ψ Γ T′ (Δ , N)
    bsucc : Exp one ((Δ , N) ∷ Ψ) Γ T′ → Branch 2 Ψ Γ T′ (Δ , N)
    bΛ    : Exp one ((S ∷ Δ , T) ∷ Ψ) Γ T′ → Branch 3 Ψ Γ T′ (Δ , S ⟶ T)
    b$    : (∀ {S} → core? S → Exp one ((Δ , S) ∷ (Δ , S ⟶ T) ∷ Ψ) Γ T′) → Branch 4 Ψ Γ T′ (Δ , T)

  data Branches : GCtx → LCtx → Typ → LCtx × Typ → Set where
    bsN : Branch 0 Ψ Γ T (Δ , N) →
          Branch 1 Ψ Γ T (Δ , N) →
          Branch 2 Ψ Γ T (Δ , N) →
          Branch 4 Ψ Γ T (Δ , N) →
          Branches Ψ Γ T (Δ , N)
    bs⟶ : Branch 0 Ψ Γ T (Δ , S ⟶ T) →
          Branch 3 Ψ Γ T (Δ , S ⟶ T) →
          Branch 4 Ψ Γ T (Δ , S ⟶ T) →
          Branches Ψ Γ T (Δ , S ⟶ T)

mutual

  data Nf : GCtx → LCtx → Typ → Set where
    zero : gwfs? Ψ → wfs? one Γ → Nf Ψ Γ N
    succ : Nf Ψ Γ N → Nf Ψ Γ N
    Λ    : Nf Ψ (S ∷ Γ) T → Nf Ψ Γ (S ⟶ T)
    box  : types? Γ → Exp zer Ψ Δ T → Nf Ψ Γ (□ Δ T)
    ne   : Ne Ψ Γ T → Nf Ψ Γ T

  data Ne : GCtx → LCtx → Typ → Set where
    var  : gwfs? Ψ → wfs? one Γ → T ∈ Γ → Ne Ψ Γ T
    gvar : NfLSubst Ψ Γ Δ → (Δ , T) ∈ Ψ → Ne Ψ Γ T
    _$_  : Ne Ψ Γ (S ⟶ T) → Nf Ψ Γ S → Ne Ψ Γ T
    mat  : Ne Ψ Γ (□ Δ T′) → NfBranches Ψ Γ T (Δ , T′) → Ne Ψ Γ T

  data NfLSubst : GCtx → LCtx → LCtx → Set where
    []  : gwfs? Ψ → wfs? one Γ → NfLSubst Ψ Γ []
    _∷_ : Nf Ψ Γ T → NfLSubst Ψ Γ Δ → NfLSubst Ψ Γ (T ∷ Δ)

  data NfBranch : ℕ → GCtx → LCtx → Typ → LCtx × Typ → Set where
    bvar  : cores? Δ → Nf Ψ Γ T′ → NfBranch 0 Ψ Γ T′ (Δ , T)
    bzero : cores? Δ → Nf Ψ Γ T′ → NfBranch 1 Ψ Γ T′ (Δ , N)
    bsucc : Nf ((Δ , N) ∷ Ψ) Γ T′ → NfBranch 2 Ψ Γ T′ (Δ , N)
    bΛ    : Nf ((S ∷ Δ , T) ∷ Ψ) Γ T′ → NfBranch 3 Ψ Γ T′ (Δ , S ⟶ T)
    b$    : (∀ {S} → core? S → Nf ((Δ , S) ∷ (Δ , S ⟶ T) ∷ Ψ) Γ T′) → NfBranch 4 Ψ Γ T′ (Δ , T)

  data NfBranches : GCtx → LCtx → Typ → LCtx × Typ → Set where
    bsN : NfBranch 0 Ψ Γ T (Δ , N) →
          NfBranch 1 Ψ Γ T (Δ , N) →
          NfBranch 2 Ψ Γ T (Δ , N) →
          NfBranch 4 Ψ Γ T (Δ , N) →
          NfBranches Ψ Γ T (Δ , N)
    bs⟶ : NfBranch 0 Ψ Γ T (Δ , S ⟶ T) →
          NfBranch 3 Ψ Γ T (Δ , S ⟶ T) →
          NfBranch 4 Ψ Γ T (Δ , S ⟶ T) →
          NfBranches Ψ Γ T (Δ , S ⟶ T)

variable
  t t′ t″ : Exp i Ψ Γ T
  s s′ s″ : Exp i Ψ Γ T
  δ δ′ δ″ : LSubst i Ψ Γ Δ
  n : ℕ
  ϕ ϕ′ ϕ″ : Branch n Ψ Γ T (Δ , T′)
  θ θ′ θ″ : LSubst i Ψ Γ Δ
  w w′ w″ : Nf Ψ Γ T
  v v′ v″ : Ne Ψ Γ T
  ψ ψ′ ψ″ : NfBranch n Ψ Γ T (Δ , T′)

-- Terms from layer 0 can be lifted to layer 1


mutual

  exp-lift : Exp zer Ψ Γ T → Exp one Ψ Γ T
  exp-lift (var Ψwf Γwf T∈Γ) = var Ψwf (wfs-lift Γwf) T∈Γ
  exp-lift (gvar δ T∈Ψ)      = gvar (lsubst-lift δ) T∈Ψ
  exp-lift (zero Ψwf Γwf)    = zero Ψwf (wfs-lift Γwf)
  exp-lift (succ t)          = exp-lift t
  exp-lift (Λ t)             = Λ (exp-lift t)
  exp-lift (t $ s)           = exp-lift t $ exp-lift s

  lsubst-lift : LSubst zer Ψ Γ Δ → LSubst one Ψ Γ Δ
  lsubst-lift ([] Ψwf Γwf)   = [] Ψwf (wfs-lift Γwf)
  lsubst-lift (t ∷ δ) = exp-lift t ∷ lsubst-lift δ


-- Syntactic validity
--
-- A well-typed term (nf, ne, resp.) must have valid contexts and type.
-----------------------------------------------------------------------

mutual

  validity : ∀ i → Exp i Ψ Γ T → gwfs? Ψ × wfs? i Γ × wf? i T
  validity i (var Ψwf Γwf T∈Γ) = Ψwf , Γwf , lookup Γwf T∈Γ
  validity i (gvar δ T∈Ψ)
    with lsubst-validity _ δ
  ...  | Ψwf , Γwf , Δwf       = Ψwf , Γwf , wf-lift′ (proj₂ (lookup Ψwf T∈Ψ))
  validity i (zero Ψwf Γwf)    = Ψwf , Γwf , N
  validity i (succ t)          = validity i t
  validity i (Λ t)
    with validity _ t
  ... | Ψwf , S ∷ Γwf , T      = Ψwf , Γwf , S ⟶ T
  validity i (t $ s)
    with validity _ t
  ... | Ψwf , Γwf , S ⟶ T      = Ψwf , Γwf , T
  validity .one (box Γwf t)
    with validity _ t
  ... | Ψwf , Δwf , T          = Ψwf , Γwf , □ Δwf T
  validity .one (mat t bs)
    with validity _ t | bs
  ... | Ψwf , Δwf , _
      | bsN (bvar _ t′) _ _ _  = Ψwf , Δwf , proj₂ (proj₂ (validity _ t′))
  ... | Ψwf , Δwf , _
      | bs⟶ (bvar _ t′) _ _    = Ψwf , Δwf , proj₂ (proj₂ (validity _ t′))

  lsubst-validity : ∀ i → LSubst i Ψ Γ Δ → gwfs? Ψ × wfs? i Γ × wfs? i Δ
  lsubst-validity i ([] Ψwf Γwf) = Ψwf , Γwf , []
  lsubst-validity i (t ∷ δ)
    with validity _ t | lsubst-validity _ δ
  ...  | Ψwf , Γwf , T | _ , _ , Δwf = Ψwf , Γwf , T ∷ Δwf


mutual
  nf-validity : Nf Ψ Γ T → gwfs? Ψ × types? Γ × type? T
  nf-validity (zero Ψwf Γwf) = Ψwf , Γwf , N
  nf-validity (succ w)       = nf-validity w
  nf-validity (Λ w)
    with nf-validity w
  ...  | Ψwf , S ∷ Γwf , T   = Ψwf , Γwf , S ⟶ T
  nf-validity (box Γwf t)
    with validity _ t
  ...  | Ψwf , Δwf , T       = Ψwf , Γwf , □ Δwf T
  nf-validity (ne v)         = ne-validity v

  ne-validity : Ne Ψ Γ T → gwfs? Ψ × types? Γ × type? T
  ne-validity (var Ψwf Γwf T∈Γ) = Ψwf , Γwf , lookup Γwf T∈Γ
  ne-validity (gvar θ T∈Ψ)
    with nflsubst-validity θ
  ...  | Ψwf , Γwf , Δwf        = Ψwf , Γwf , wf-lift (proj₂ (lookup Ψwf T∈Ψ))
  ne-validity (v $ w)
    with ne-validity v
  ...  | Ψwf , Γwf , _ ⟶ T      = Ψwf , Γwf , T
  ne-validity (mat v bs)
    with ne-validity v | bs
  ...  | Ψwf , Γwf , T
       | bsN (bvar _ w) _ _ _   = Ψwf , Γwf , proj₂ (proj₂ (nf-validity w))
  ...  | Ψwf , Γwf , T
       | bs⟶ (bvar _ w) _ _     = Ψwf , Γwf , proj₂ (proj₂ (nf-validity w))

  nflsubst-validity : NfLSubst Ψ Γ Δ → gwfs? Ψ × types? Γ × types? Δ
  nflsubst-validity ([] Ψwf Γwf) = Ψwf , Γwf , []
  nflsubst-validity (w ∷ θ)
    with nf-validity w | nflsubst-validity θ
  ...  | Ψwf , Γwf , T | _ , _ , Δwf = Ψwf , Γwf , T ∷ Δwf

-- Definition of weakenings
--
-- In simple types, we modularize weakenings for global and local contexts.
---------------------------------------------------------------------------

module _ {A : Set} (P : A → Set) where

  data Wk : List A → List A → Set where
    ε  : Wk [] []
    p  : ∀ {x xs ys} →
         P x →
         Wk xs ys →
         ----------------
         Wk (x ∷ xs) ys
    q  : ∀ {x xs ys} →
         P x →
         Wk xs ys →
         --------------------
         Wk (x ∷ xs) (x ∷ ys)


  -- Validity for weakenings
  --------------------------

  wk-validity : ∀ {xs ys} → Wk xs ys → All P xs × All P ys
  wk-validity ε    = [] , []
  wk-validity (p Px wk)
    with wk-validity wk
  ...  | Pxs , Pys = Px ∷ Pxs , Pys
  wk-validity (q Px wk)
    with wk-validity wk
  ...  | Pxs , Pys = Px ∷ Pxs , Px ∷ Pys


  -- Identity and composition of weakenings
  -----------------------------------------

  idwk : ∀ {xs} → All P xs → Wk xs xs
  idwk []         = ε
  idwk (px ∷ Pxs) = q px (idwk Pxs)


  infixl 3 _∘w_
  _∘w_ : ∀ {xs ys zs} → Wk xs ys → Wk zs xs → Wk zs ys
  ε ∘w wk′           = wk′
  p px wk ∘w q _ wk′ = p px (wk ∘w wk′)
  q px wk ∘w q _ wk′ = q px (wk ∘w wk′)
  wk ∘w p px wk′     = p px (wk ∘w wk′)


GWk = Wk gwf?

LWk = Wk type?


variable
  γ γ′ γ″ : GWk Ψ Φ
  τ τ′ τ″ : LWk Γ Δ


gwk-validity : GWk Ψ Φ → gwfs? Ψ × gwfs? Φ
gwk-validity = wk-validity _

lwk-validity : LWk Γ Δ → types? Γ × types? Δ
lwk-validity = wk-validity _


-- -- Weakening applications
-- -------------------------

-- gwk-∈ : T ∈ Ψ → Wk i Φ Ψ → T ∈ Φ
-- gwk-∈ T∈Ψ (p _ γ)      = 1+ (gwk-∈ T∈Ψ γ)
-- gwk-∈ 0d (q _ γ)       = 0d
-- gwk-∈ (1+ T∈Ψ) (q _ γ) = 1+ (gwk-∈ T∈Ψ γ)

-- instance
--   ∈-gwk-mono : Monotone (λ Ψ → T ∈ Ψ) (Wk i)
--   ∈-gwk-mono = record { _[_] = gwk-∈ }


-- gwk : Exp i Ψ Γ T → GWk Φ Ψ → Exp i Φ Γ T
-- gwk (v0 Ψwf Γwf T∈Γ) γ = v0 (proj₁ (gwk-validity γ)) Γwf T∈Γ
-- gwk (v1 Ψwf Γwf T∈Γ) γ = v1 (proj₁ (gwk-validity γ)) Γwf T∈Γ
-- gwk (u0 Ψwf Γwf T∈Ψ) γ = u0 (proj₁ (gwk-validity γ)) Γwf (T∈Ψ [ γ ])
-- gwk (u1 Ψwf Γwf T∈Ψ) γ = u1 (proj₁ (gwk-validity γ)) Γwf (T∈Ψ [ γ ])
-- gwk (zero0 Ψwf Γwf) γ  = zero0 (proj₁ (gwk-validity γ)) Γwf
-- gwk (zero1 Ψwf Γwf) γ  = zero1 (proj₁ (gwk-validity γ)) Γwf
-- gwk (succ t) γ         = succ (gwk t γ)
-- gwk (Λ t) γ            = Λ (gwk t γ)
-- gwk (t $ s) γ          = gwk t γ $ gwk s γ
-- gwk (box Γwf t) γ      = box Γwf (gwk t γ)
-- gwk (letbox s t) γ
--   with validity _ s
-- ...  | _ , _ , □ S     = letbox (gwk s γ) (gwk t (q S γ))

-- instance
--   gwk-mono : Monotone (λ Ψ → Exp i Ψ Γ T) GWk
--   gwk-mono = record { _[_] = gwk }


-- mutual
--   gwk-nf : Nf Ψ Γ T → GWk Φ Ψ → Nf Φ Γ T
--   gwk-nf (zero1 Ψwf Γwf) γ = zero1 (proj₁ (gwk-validity γ)) Γwf
--   gwk-nf (succ w) γ        = succ (gwk-nf w γ)
--   gwk-nf (Λ w) γ           = Λ (gwk-nf w γ)
--   gwk-nf (box Γwf t) γ     = box Γwf (t [ γ ])
--   gwk-nf (ne v) γ          = ne (gwk-ne v γ)

--   gwk-ne : Ne Ψ Γ T → GWk Φ Ψ → Ne Φ Γ T
--   gwk-ne (v1 Ψwf Γwf T∈Γ) γ = v1 (proj₁ (gwk-validity γ)) Γwf T∈Γ
--   gwk-ne (u1 Ψwf Γwf T∈Ψ) γ = u1 (proj₁ (gwk-validity γ)) Γwf (T∈Ψ [ γ ])
--   gwk-ne (v $ w) γ          = gwk-ne v γ $ gwk-nf w γ
--   gwk-ne (letbox v w) γ
--     with ne-validity v
--   ... | _ , _ , □ S         = letbox (gwk-ne v γ) (gwk-nf w (q S γ))

-- instance
--   gwk-nf-mono : Monotone (λ Ψ → Nf Ψ Γ T) GWk
--   gwk-nf-mono = record { _[_] = gwk-nf }

--   gwk-ne-mono : Monotone (λ Ψ → Ne Ψ Γ T) GWk
--   gwk-ne-mono = record { _[_] = gwk-ne }


-- mutual
--   lwk-nf : Nf Ψ Γ T → LWk Δ Γ → Nf Ψ Δ T
--   lwk-nf (zero1 Ψwf Γwf) τ = zero1 Ψwf (proj₁ (lwk-validity τ))
--   lwk-nf (succ w) τ        = succ (lwk-nf w τ)
--   lwk-nf (Λ w) τ
--     with nf-validity w
--   ...  | _ , S ∷ _ , _     = Λ (lwk-nf w (q S τ))
--   lwk-nf (box _ t) τ       = box (proj₁ (lwk-validity τ)) t
--   lwk-nf (ne v) τ          = ne (lwk-ne v τ)

--   lwk-ne : Ne Ψ Γ T → LWk Δ Γ → Ne Ψ Δ T
--   lwk-ne (v1 Ψwf Γwf T∈Γ) τ = v1 Ψwf (proj₁ (lwk-validity τ)) (T∈Γ [ τ ])
--   lwk-ne (u1 Ψwf Γwf T∈Ψ) τ = u1 Ψwf (proj₁ (lwk-validity τ)) T∈Ψ
--   lwk-ne (v $ w) τ          = lwk-ne v τ $ lwk-nf w τ
--   lwk-ne (letbox v w) τ
--     with ne-validity v
--   ... | _ , _ , □ S         = letbox (lwk-ne v τ) (lwk-nf w τ)


-- -- Weakenings between pairs of global and local contexts
-- --
-- -- This is the base category the presheaf model lives in.
-- ---------------------------------------------------

-- AWk : Ctx × Ctx → Ctx × Ctx → Set
-- AWk (Ψ , Γ) (Φ , Δ) = GWk Ψ Φ × LWk Γ Δ

-- awk-validity : AWk (Ψ , Γ) (Φ , Δ) → (cores? Ψ × types? Γ) × cores? Φ × types? Δ
-- awk-validity (γ , τ) = (proj₁ (gwk-validity γ) , proj₁ (lwk-validity τ)) , proj₂ (gwk-validity γ) , proj₂ (lwk-validity τ)


-- -- Identity and composition of weakenings
-- -----------------------------------------

-- idawk : cores? Ψ → types? Γ → AWk (Ψ , Γ) (Ψ , Γ)
-- idawk Ψwf Γwf = idwk Ψwf , idwk Γwf


-- infixl 3 _∘a_
-- _∘a_ : AWk (Ψ′ , Γ′) (Ψ , Γ) → AWk (Ψ″ , Γ″) (Ψ′ , Γ′) → AWk (Ψ″ , Γ″) (Ψ , Γ)
-- (γ , τ) ∘a (γ′ , τ′) = (γ ∘w γ′) , (τ ∘w τ′)


-- -- Applications of weakenings
-- -----------------------------

-- awk-nf : Nf Ψ Γ T → AWk (Φ , Δ) (Ψ , Γ) → Nf Φ Δ T
-- awk-nf w (γ , τ) = lwk-nf (w [ γ ]) τ

-- awk-ne : Ne Ψ Γ T → AWk (Φ , Δ) (Ψ , Γ) → Ne Φ Δ T
-- awk-ne w (γ , τ) = lwk-ne (w [ γ ]) τ

-- instance
--   awk-nf-mono : Monotone (λ (Ψ , Γ) → Nf Ψ Γ T) AWk
--   awk-nf-mono = record { _[_] = awk-nf }

--   awk-ne-mono : Monotone (λ (Ψ , Γ) → Ne Ψ Γ T) AWk
--   awk-ne-mono = record { _[_] = awk-ne }


-- -- Global substitutions
-- -----------------------

-- data GSubst : Ctx → Ctx → Set where
--   [] : cores? Ψ → GSubst Ψ []
--   _∷_ : Exp zer Ψ [] T → GSubst Ψ Φ → GSubst Ψ (T ∷ Φ)

-- variable
--   σ σ′ σ″ : GSubst Φ Ψ


-- -- Validity of global substitutions
-- -----------------------------------

-- gsubst-validity : GSubst Ψ Φ → cores? Ψ × cores? Φ
-- gsubst-validity ([] Ψwf)     = Ψwf , []
-- gsubst-validity (t ∷ σ)
--   with gsubst-validity σ | validity _ t
-- ...  | Ψwf , Φwf | _ , _ , T = Ψwf , T ∷ Φwf


-- -- (Global) weakening of global substitutions
-- ---------------------------------------------

-- gsubst-lookup : GSubst Ψ Φ → T ∈ Φ → Exp zer Ψ [] T
-- gsubst-lookup (t ∷ σ) 0d       = t
-- gsubst-lookup (t ∷ σ) (1+ T∈Φ) = gsubst-lookup σ T∈Φ

-- gsubst-wk : GSubst Ψ Φ → GWk Ψ′ Ψ → GSubst Ψ′ Φ
-- gsubst-wk ([] _) γ  = [] (proj₁ (gwk-validity γ))
-- gsubst-wk (t ∷ σ) γ = t [ γ ] ∷ gsubst-wk σ γ

-- instance
--   gsubst-wk-mono : Monotone (λ Ψ → GSubst Ψ Φ) GWk
--   gsubst-wk-mono = record { _[_] = gsubst-wk }


-- -- Applying global substitutions
-- ---------------------------------

-- gsubst : Exp i Ψ Γ T → GSubst Φ Ψ → Exp i Φ Γ T
-- gsubst (v0 Ψwf Γwf T∈Γ) σ = v0 (proj₁ (gsubst-validity σ)) Γwf T∈Γ
-- gsubst (v1 Ψwf Γwf T∈Γ) σ = v1 (proj₁ (gsubst-validity σ)) Γwf T∈Γ
-- gsubst (u0 Ψwf Γwf T∈Ψ) σ = lwk! (gsubst-lookup σ T∈Ψ) Γwf
-- gsubst (u1 Ψwf Γwf T∈Ψ) σ = lwk! (layer-lift (gsubst-lookup σ T∈Ψ)) Γwf
-- gsubst (zero0 Ψwf Γwf) σ  = zero0 (proj₁ (gsubst-validity σ)) Γwf
-- gsubst (zero1 Ψwf Γwf) σ  = zero1 (proj₁ (gsubst-validity σ)) Γwf
-- gsubst (succ t) σ         = succ (gsubst t σ)
-- gsubst (Λ t) σ            = Λ (gsubst t σ)
-- gsubst (t $ s) σ          = gsubst t σ $ gsubst s σ
-- gsubst (box Γwf t) σ      = box Γwf (gsubst t σ)
-- gsubst (letbox s t) σ
--   with validity _ s
-- ...  | _ , _ , □ S        = letbox (gsubst s σ) (gsubst t (u0 (S ∷ Φwf) [] 0d ∷ σ [ p S (idwk Φwf) ]))
--   where Φwf = proj₁ (gsubst-validity σ)


-- instance
--   gsubst-mono : Monotone (λ Ψ → Exp i Ψ Γ T) GSubst
--   gsubst-mono = record { _[_] = gsubst }


-- -- Converting a global weakening to a global substitution
-- --------------------------------------------------

-- gwk-gsubst : GWk Ψ Φ → GSubst Ψ Φ
-- gwk-gsubst ε       = [] []
-- gwk-gsubst (p T γ) = gwk-gsubst γ [ p T (idwk (proj₁ (gwk-validity γ))) ]
-- gwk-gsubst (q T γ) = u0 (T ∷ proj₁ (gwk-validity γ)) [] 0d ∷ gwk-gsubst γ [ p T (idwk (proj₁ (gwk-validity γ))) ]

-- -- From this we can extract the identity global substitutions.

-- gid : cores? Ψ → GSubst Ψ Ψ
-- gid Ψwf = gwk-gsubst (idwk Ψwf)


-- -- Interpretations of types and contexts
-- ----------------------------------------

-- ⟦_⟧T : Typ → Ctx → Ctx → Set
-- ⟦ N ⟧T Ψ Γ     = Nf Ψ Γ N
-- ⟦ □ T ⟧T Ψ Γ   = Nf Ψ Γ (□ T)
-- ⟦ S ⟶ T ⟧T Ψ Γ = cores? Ψ × types? Γ × type? (S ⟶ T) × ∀ {Φ Δ} → AWk (Φ , Δ) (Ψ , Γ) → ⟦ S ⟧T Φ Δ → ⟦ T ⟧T Φ Δ

-- ⟦_⟧G : Ctx → Layer → Ctx → Set
-- ⟦ Φ ⟧G zer Ψ = GWk Ψ Φ
-- ⟦ Φ ⟧G one Ψ = GSubst Ψ Φ

-- ⟦_⟧L : Ctx → Ctx → Ctx → Set
-- ⟦ [] ⟧L Ψ Γ    = cores? Ψ × types? Γ
-- ⟦ T ∷ Δ ⟧L Ψ Γ = ⟦ T ⟧T Ψ Γ × ⟦ Δ ⟧L Ψ Γ

-- ⟦_⟧A : Ctx × Ctx → Layer → Ctx → Ctx → Set
-- ⟦ Φ , Δ ⟧A i Ψ Γ = ⟦ Φ ⟧G i Ψ × ⟦ Δ ⟧L Ψ Γ


-- -- validity of interpretations
-- ------------------------------

-- T-validity : ∀ T → ⟦ T ⟧T Ψ Γ → cores? Ψ × types? Γ × type? T
-- T-validity N a                          = nf-validity a
-- T-validity (□ T) a                      = nf-validity a
-- T-validity (S ⟶ T) (Ψwf , Γwf , ST , _) = Ψwf , Γwf , ST

-- G-validity : ∀ i → ⟦ Φ ⟧G i Ψ → cores? Φ × cores? Ψ
-- G-validity zer γ
--   with gwk-validity γ
-- ...  | Ψwf , Φwf = Φwf , Ψwf
-- G-validity one σ
--   with gsubst-validity σ
-- ...  | Ψwf , Φwf = Φwf , Ψwf

-- L-validity : ∀ Δ → ⟦ Δ ⟧L Ψ Γ → types? Δ × cores? Ψ × types? Γ
-- L-validity [] ρ        = [] , ρ
-- L-validity (T ∷ Δ) (a , ρ)
--   with L-validity _ ρ
-- ...  | Δwf , Ψwf , Γwf = proj₂ (proj₂ (T-validity T a)) ∷ Δwf , Ψwf , Γwf

-- A-validity : ⟦ Φ , Δ ⟧A i Ψ Γ → (cores? Φ × types? Δ) × cores? Ψ × types? Γ
-- A-validity (σ , ρ) = (proj₁ (G-validity _ σ) , proj₁ (L-validity _ ρ))
--                    , proj₁ (proj₂ (L-validity _ ρ)) , proj₂ (proj₂ (L-validity _ ρ))


-- -- Monotonicity of interpretations
-- ----------------------------------

-- T-mon : ∀ T → ⟦ T ⟧T Ψ Γ → AWk (Φ , Δ) (Ψ , Γ) → ⟦ T ⟧T Φ Δ
-- T-mon N a ξ                          = a [ ξ ]
-- T-mon (□ T) a ξ                      = a [ ξ ]
-- T-mon (S ⟶ T) (Ψwf , Γwf , ST , f) ξ = proj₁ (proj₁ (awk-validity ξ)) , proj₂ (proj₁ (awk-validity ξ))
--                                      , ST , λ ξ′ a → f (ξ ∘a ξ′) a


-- instance
--   T-mon-mono : Monotone (λ (Ψ , Γ) → ⟦ T ⟧T Ψ Γ) AWk
--   T-mon-mono = record { _[_] = T-mon _ }

-- G-mon : ∀ i → ⟦ Φ ⟧G i Ψ → GWk Ψ′ Ψ → ⟦ Φ ⟧G i Ψ′
-- G-mon zer γ′ γ = γ′ ∘w γ
-- G-mon one σ γ  = σ [ γ ]


-- instance
--   G-mon-mono : Monotone (⟦ Φ ⟧G i) GWk
--   G-mon-mono = record { _[_] = G-mon _ }


-- L-mon : ∀ Γ′ → ⟦ Γ′ ⟧L Ψ Γ → AWk (Φ , Δ) (Ψ , Γ) → ⟦ Γ′ ⟧L Φ Δ
-- L-mon [] ρ ξ             = proj₁ (awk-validity ξ)
-- L-mon (T ∷ Γ′) (a , ρ) ξ = a [ ξ ] , L-mon Γ′ ρ ξ


-- instance
--   L-mon-mono : Monotone (λ (Ψ , Γ) → ⟦ Γ′ ⟧L Ψ Γ) AWk
--   L-mon-mono = record { _[_] = L-mon _ }


-- A-mon : ⟦ Φ , Δ ⟧A i Ψ Γ → AWk (Ψ′ , Γ′) (Ψ , Γ) → ⟦ Φ , Δ ⟧A i Ψ′ Γ′
-- A-mon (σ , ρ) ξ@(γ , _) = σ [ γ ] , ρ [ ξ ]


-- instance
--   A-mon-mono : Monotone (λ (Ψ , Γ) → ⟦ Φ , Δ ⟧A i Ψ Γ) AWk
--   A-mon-mono = record { _[_] = A-mon }


-- -- Interpretation of expressions to natural transformations
-- -----------------------------------------------------------

-- L-lookup : T ∈ Δ → ⟦ Δ ⟧L Ψ Γ → ⟦ T ⟧T Ψ Γ
-- L-lookup 0d (a , _)       = a
-- L-lookup (1+ T∈Δ) (_ , ρ) = L-lookup T∈Δ ρ


-- mutual
--   ↓ : ∀ T → ⟦ T ⟧T Ψ Γ → Nf Ψ Γ T
--   ↓ N a                                 = a
--   ↓ (□ T) a                             = a
--   ↓ (S ⟶ T) (Ψwf , Γwf , Swf ⟶ Twf , a) = Λ (↓ T (a (idwk Ψwf , p Swf (idwk Γwf)) (↑ S (v1 Ψwf (Swf ∷ Γwf) 0d))))

--   ↑ : ∀ T → Ne Ψ Γ T → ⟦ T ⟧T Ψ Γ
--   ↑ N v                        = ne v
--   ↑ (□ T) v                    = ne v
--   ↑ (S ⟶ T) v
--     with ne-validity v
--   ...  | Ψwf , Γwf , Swf ⟶ Twf = Ψwf , Γwf , Swf ⟶ Twf
--                                , λ ξ a → ↑ T ((v [ ξ ]) $ ↓ S a)

-- -- For some reason, when we attempt to implement the following function
-- --
-- --    ⟦_;_⟧ : ∀ i → Exp i Φ Δ T → ⟦ Φ , Δ ⟧A i Ψ Γ → ⟦ T ⟧T Ψ Γ
-- --
-- -- by splitting on i and then Exp, Agda fails to realize that in the u1 case, i
-- -- actually decreases.
-- --
-- -- It seems that Agda considers Exp as the decreasing argument when i is an unifiable
-- -- argument.  For this reason, we are forced to interpret the expressions in two
-- -- separate functions according to their layers.

-- ⟦_⟧0 : Exp zer Φ Δ T → ⟦ Φ , Δ ⟧A zer Ψ Γ → ⟦ T ⟧T Ψ Γ
-- ⟦ v0 Φwf Δwf T∈Δ ⟧0 (γ , ρ)          = L-lookup T∈Δ ρ
-- ⟦ u0 Φwf Δwf T∈Φ ⟧0 (γ , ρ)          = ↑ _ (u1 Φwf (proj₂ (proj₂ (L-validity _ ρ))) T∈Φ [ γ ])
-- ⟦ zero0 Φwf Δwf ⟧0 (γ , ρ)
--   with L-validity _ ρ
-- ...  | _ , Ψwf , Γwf                 = zero1 Ψwf Γwf
-- ⟦ succ t ⟧0 (γ , ρ)                  = succ (⟦ t ⟧0 (γ , ρ))
-- ⟦ Λ t ⟧0 (γ , ρ)
--   with L-validity _ ρ | validity _ t
-- ...  | _ , Ψwf , Γwf | _ , S ∷ _ , T = Ψwf , Γwf , core-type (S ⟶ T)
--                                      , λ ξ@(γ′ , _) a → ⟦ t ⟧0 ((γ ∘w γ′) , a , ρ [ ξ ])
-- ⟦ t $ s ⟧0 (γ , ρ)
--   with ⟦ t ⟧0 (γ , ρ)
-- ...  | Ψwf , Γwf , _ , f             = f (idawk Ψwf Γwf) (⟦ s ⟧0 (γ , ρ))

-- ⟦_⟧1 : Exp one Φ Δ T → ⟦ Φ , Δ ⟧A one Ψ Γ → ⟦ T ⟧T Ψ Γ
-- ⟦ v1 Φwf Δwf T∈Δ ⟧1 (σ , ρ)          = L-lookup T∈Δ ρ
-- ⟦ u1 Φwf Δwf T∈Φ ⟧1 (σ , ρ)
--   with L-validity _ ρ
-- ...  | _ , Ψwf , Γwf                 = ⟦ gsubst-lookup σ T∈Φ ⟧0 (idwk Ψwf , Ψwf , Γwf)
-- ⟦ zero1 Φwf Δwf ⟧1 (σ , ρ)
--   with L-validity _ ρ
-- ...  | _ , Ψwf , Γwf                 = zero1 Ψwf Γwf
-- ⟦ succ t ⟧1 (σ , ρ)                  = succ (⟦ t ⟧1 (σ , ρ))
-- ⟦ Λ t ⟧1 (σ , ρ)
--   with L-validity _ ρ | validity _ t
-- ...  | _ , Ψwf , Γwf | _ , S ∷ _ , T = Ψwf , Γwf , S ⟶ T
--                                      , λ ξ@(γ , _) a → ⟦ t ⟧1 (σ [ γ ] , a , ρ [ ξ ])
-- ⟦ t $ s ⟧1 (σ , ρ)
--   with ⟦ t ⟧1 (σ , ρ)
-- ...  | Ψwf , Γwf , _ , f             = f (idawk Ψwf Γwf) (⟦ s ⟧1 (σ , ρ))
-- ⟦ box Δwf t ⟧1 (σ , ρ)               = box (proj₂ (proj₂ (L-validity _ ρ))) (t [ σ ])
-- ⟦ letbox s t ⟧1 (σ , ρ)
--   with ⟦ s ⟧1 (σ , ρ)
-- ... | box Γwf s′                     = ⟦ t ⟧1 (s′ ∷ σ , ρ)
-- ... | ne v
--     with ne-validity v
-- ...    | Ψwf , Γwf , □ S             = ↑ _ (letbox v (↓ _ (⟦ t ⟧1 (u0 (S ∷ Ψwf) [] 0d ∷ σ [ gp ] , ρ [ gp , idwk Γwf ]))))
--   where gp = p S (idwk Ψwf)


-- -- Then we force a definition of ⟦_;_⟧ decreasing by layer i

-- ⟦_;_⟧ : ∀ i → Exp i Φ Δ T → ⟦ Φ , Δ ⟧A i Ψ Γ → ⟦ T ⟧T Ψ Γ
-- ⟦ zer ; t ⟧ = ⟦ t ⟧0
-- ⟦ one ; t ⟧ = ⟦ t ⟧1


-- -- Definition of NbE
-- --------------------

-- ↑L : cores? Ψ → types? Γ → ⟦ Γ ⟧L Ψ Γ
-- ↑L Ψwf []        = Ψwf , []
-- ↑L Ψwf (T ∷ Γwf) = ↑ _ (v1 Ψwf (T ∷ Γwf) 0d) , ↑L Ψwf Γwf [ idwk Ψwf , (p T (idwk Γwf)) ]

-- nbe : Exp one Ψ Γ T → Nf Ψ Γ T
-- nbe t
--   with validity _ t
-- ...  | Ψwf , Γwf , _ = ↓ _ (⟦ one ; t ⟧ (gid Ψwf , ↑L Ψwf Γwf))
