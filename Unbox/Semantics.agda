{-# OPTIONS --without-K --safe #-}

module Unbox.Semantics where

open import Lib
open import LibNonEmpty
open import Unbox.Statics


mutual
  Ctx : Set
  Ctx = ℕ → D

  Ctxs : Set
  Ctxs = ℕ → ℕ × Ctx

  data D : Set where
    Λ   : (t : Exp) → (ρ : Ctxs) → D
    box : D → D
    ↑   : (T : Typ) → (c : Dn) → D

  data Dn : Set where
    l     : (x : ℕ) → Dn
    _$_   : Dn → (d : Df) → Dn
    unbox : ℕ → Dn → Dn

  data Df : Set where
    ↓ : (T : Typ) → (a : D) → Df

infixl 10 [_]_$′_
pattern l′ T x        = ↑ T (l x)
pattern unbox′ T n c  = ↑ T (unbox n c)
pattern [_]_$′_ T x y = ↑ T (_$_ x y)

MTrans : Set
MTrans = ℕ → ℕ

variable
  a a′ a″    : D
  b b′ b″    : D
  f f′ f″    : D
  c c′ c″    : Dn
  d d′ d″ d‴ : Df
  ρ ρ′ ρ″    : Ctxs
  κ κ′ κ″    : MTrans

emp : Ctx
emp n = ↑ B (l 0)

empty : Ctxs
empty n = 1 , emp

infixl 8 _↦_ _↦′_
_↦′_ : Ctx → D → Ctx
(ρ ↦′ d) zero    = d
(ρ ↦′ d) (suc x) = ρ x

_↦_ : Ctxs → D → Ctxs
(ρ ↦ d) 0       = proj₁ (ρ 0) , proj₂ (ρ 0) ↦′ d
(ρ ↦ d) (suc n) = ρ (suc n)

ext : Ctxs → ℕ → Ctxs
ext ρ n zero = n , emp
ext ρ n (suc m) = ρ m

C-Tr : Ctxs → ℕ → Ctxs
C-Tr ρ n m = ρ (n + m)

drop : Ctxs → Ctxs
drop ρ zero = proj₁ (ρ 0) , λ m → proj₂ (ρ 0) (1 + m)
drop ρ (suc n) = ρ (suc n)

lookup : Ctxs → ℕ → D
lookup ρ n = proj₂ (ρ 0) n

ins : MTrans → ℕ → MTrans
ins κ n zero = n
ins κ n (suc m) = κ m

instance
  MTransHasTr : HasTr MTrans
  MTransHasTr = record { Tr = λ κ n m → κ (n + m) }

M-L : MTrans → ℕ → ℕ
M-L κ zero    = 0
M-L κ (suc n) = κ 0 + M-L (Tr κ 1) n

instance
  MTransHasL : HasL MTrans
  MTransHasL = record { L = M-L }

toMTrans : Ctxs → MTrans
toMTrans ρ n = proj₁ (ρ n)

instance
  CtxsHasL : HasL Ctxs
  CtxsHasL = record { L = λ ρ → M-L (toMTrans ρ) }

  CtxHasTr : HasTr Ctxs
  CtxHasTr = record { Tr = C-Tr }

infixl 3 _ø_
_ø_ : MTrans → MTrans → MTrans
(κ ø κ′) zero    = L κ′ (κ 0)
(κ ø κ′) (suc n) = (Tr κ 1 ø Tr κ′ (κ 0)) n

mutual
  mtran : D → MTrans → D
  mtran (Λ t ρ) κ = Λ t (mtran-Cs ρ κ)
  mtran (box a) κ = box (mtran a (ins κ 1))
  mtran (↑ T e) κ = ↑ T (mtran-c e κ)

  mtran-c : Dn → MTrans → Dn
  mtran-c (l x) κ = l x
  mtran-c (c $ d) κ = (mtran-c c κ) $ mtran-d d κ
  mtran-c (unbox n c) κ = unbox (L κ n) (mtran-c c (Tr κ n))

  mtran-d : Df → MTrans → Df
  mtran-d (↓ T a) κ = ↓ T (mtran a κ)

  mtran-Cs : Ctxs → MTrans → Ctxs
  mtran-Cs ρ κ n = L (Tr κ (L ρ n)) (proj₁ (ρ n)) , λ m → mtran (proj₂ (ρ n) m) (Tr κ (L ρ n))

instance
  DMonotone : Monotone D MTrans
  DMonotone = record { _[_] = mtran }

  DnMonotone : Monotone Dn MTrans
  DnMonotone = record { _[_] = mtran-c }

  DfMonotone : Monotone Df MTrans
  DfMonotone = record { _[_] = mtran-d }

  CtxsMonotone : Monotone Ctxs MTrans
  CtxsMonotone = record { _[_] = mtran-Cs }

vone : MTrans
vone _ = 1

infix 4 _∙_↘_ unbox∙_,_↘_ ⟦_⟧_↘_ ⟦_⟧s_↘_

mutual
  data _∙_↘_ : D → D → D → Set where
    Λ∙ : ⟦ t ⟧ ρ ↦ a ↘ b →
         ------------------
         Λ t ρ ∙ a ↘ b
    $∙ : ∀ S T e a → ↑ (S ⟶ T) e ∙ a ↘ ↑ T (e $ ↓ S a)

  data unbox∙_,_↘_ : ℕ → D → D → Set where
    box↘   : ∀ n →
             unbox∙ n , box a ↘ a [ ins vone n ]
    unbox∙ : ∀ n →
             unbox∙ n , ↑ (□ T) c ↘ ↑ T (unbox n c)

  data ⟦_⟧_↘_ : Exp → Ctxs → D → Set where
    ⟦v⟧     : ∀ n →
              ⟦ v n ⟧ ρ ↘ lookup ρ n
    ⟦Λ⟧     : ∀ t →
              ⟦ Λ t ⟧ ρ ↘ Λ t ρ
    ⟦$⟧     : ⟦ r ⟧ ρ ↘ f →
              ⟦ s ⟧ ρ ↘ a →
              f ∙ a ↘ b →
              ---------------------
              ⟦ r $ s ⟧ ρ ↘ b
    ⟦box⟧   : ⟦ t ⟧ ext ρ 1 ↘ a →
              ---------------------
              ⟦ box t ⟧ ρ ↘ box a
    ⟦unbox⟧ : ∀ n →
              ⟦ t ⟧ Tr ρ n ↘ a →
              unbox∙ L ρ n , a ↘ b →
              ----------------------
              ⟦ unbox n t ⟧ ρ ↘ b
    ⟦[]⟧    : ⟦ σ ⟧s ρ ↘ ρ′ →
              ⟦ t ⟧ ρ′ ↘ a →
              ---------------------
              ⟦ t [ σ ] ⟧ ρ ↘ a

  data ⟦_⟧s_↘_ : Substs → Ctxs → Ctxs → Set where
    ⟦I⟧ : ⟦ I ⟧s ρ ↘ ρ
    ⟦p⟧ : ⟦ σ ⟧s ρ ↘ ρ′ →
          --------------------
          ⟦ p σ ⟧s ρ ↘ drop ρ′
    ⟦,⟧ : ⟦ σ ⟧s ρ ↘ ρ′ →
          ⟦ t ⟧ ρ ↘ a →
          ---------------------
          ⟦ σ , t ⟧s ρ ↘ ρ′ ↦ a
    ⟦；⟧ : ∀ {n} →
          ⟦ σ ⟧s Tr ρ n ↘ ρ′ →
          -----------------------------
          ⟦ σ ； n ⟧s ρ ↘ ext ρ′ (L ρ n)
    ⟦∘⟧ : ⟦ δ ⟧s ρ ↘ ρ′ →
          ⟦ σ ⟧s ρ′ ↘ ρ″ →
          -----------------
          ⟦ σ ∘ δ ⟧s ρ ↘ ρ″


mutual
  ap-det : f ∙ a ↘ b → f ∙ a ↘ b′ → b ≡ b′
  ap-det (Λ∙ ↘b) (Λ∙ ↘b′)             = ⟦⟧-det ↘b ↘b′
  ap-det ($∙ S T e _) ($∙ .S .T .e _) = refl

  unbox-det : ∀ {n} → unbox∙ n , a ↘ b → unbox∙ n , a ↘ b′ → b ≡ b′
  unbox-det (box↘ _) (box↘ _)     = refl
  unbox-det (unbox∙ _) (unbox∙ _) = refl

  ⟦⟧-det : ⟦ t ⟧ ρ ↘ a → ⟦ t ⟧ ρ ↘ b → a ≡ b
  ⟦⟧-det (⟦v⟧ n) (⟦v⟧ .n) = refl
  ⟦⟧-det (⟦Λ⟧ t) (⟦Λ⟧ .t) = refl
  ⟦⟧-det (⟦$⟧ ↘f ↘a ↘b) (⟦$⟧ ↘f′ ↘a′ ↘b′)
    rewrite ⟦⟧-det ↘f ↘f′
          | ⟦⟧-det ↘a ↘a′
          | ap-det ↘b ↘b′ = refl
  ⟦⟧-det (⟦box⟧ ↘a) (⟦box⟧ ↘b)
    rewrite ⟦⟧-det ↘a ↘b  = refl
  ⟦⟧-det (⟦unbox⟧ n ↘a ↘a′) (⟦unbox⟧ .n ↘b ↘b′)
    rewrite ⟦⟧-det ↘a ↘b
          | unbox-det ↘a′ ↘b′ = refl
  ⟦⟧-det (⟦[]⟧ ↘ρ′ ↘a) (⟦[]⟧ ↘ρ″ ↘b)
    rewrite ⟦⟧s-det ↘ρ′ ↘ρ″
          | ⟦⟧-det ↘a ↘b  = refl

  ⟦⟧s-det : ⟦ σ ⟧s ρ ↘ ρ′ → ⟦ σ ⟧s ρ ↘ ρ″ → ρ′ ≡ ρ″
  ⟦⟧s-det ⟦I⟧ ⟦I⟧             = refl
  ⟦⟧s-det (⟦p⟧ ↘ρ′) (⟦p⟧ ↘ρ″)
    rewrite ⟦⟧s-det ↘ρ′ ↘ρ″   = refl
  ⟦⟧s-det (⟦,⟧ ↘ρ′ ↘a) (⟦,⟧ ↘ρ″ ↘b)
    rewrite ⟦⟧s-det ↘ρ′ ↘ρ″
          | ⟦⟧-det ↘a ↘b      = refl
  ⟦⟧s-det (⟦；⟧ ↘ρ′) (⟦；⟧ ↘ρ″)
      rewrite ⟦⟧s-det ↘ρ′ ↘ρ″ = refl
  ⟦⟧s-det (⟦∘⟧ ↘ρ′ ↘ρ″) (⟦∘⟧ ↘ρ‴ ↘ρ⁗)
    rewrite ⟦⟧s-det ↘ρ′ ↘ρ‴
          | ⟦⟧s-det ↘ρ″ ↘ρ⁗   = refl

instance
  ℕsHasTr : HasTr (List⁺ ℕ)
  ℕsHasTr = record { Tr = truncate }

inc : List⁺ ℕ → List⁺ ℕ
inc (n ∷ ns) = (suc n ∷ ns)

-- Readback functions
infix 4 Rf_-_↘_ Re_-_↘_

mutual

  data Rf_-_↘_ : List⁺ ℕ → Df → Nf → Set where
    RΛ  : ∀ ns →
          f ∙ l′ S (sum⁺ ns) ↘ a →
          Rf inc ns - ↓ T a ↘ w →
          ---------------------
          Rf ns - ↓ (S ⟶ T) f ↘ Λ w
    R□  : ∀ ns →
          unbox∙ 1 , a ↘ b →
          Rf ns - ↓ T b ↘ w →
          --------------------------
          Rf ns - ↓ (□ T) a ↘ box w
    Rne : ∀ n →
          Re n - c ↘ u →
          ---------------------
          Rf n - ↓ B (↑ B c) ↘ ne u

  data Re_-_↘_ : List⁺ ℕ → Dn → Ne → Set where
    Rl : ∀ ns x →
         Re ns - l x ↘ v (sum⁺ ns ∸ x ∸ 1)
    R$ : ∀ ns →
         Re ns - c ↘ u →
         Rf ns - d ↘ w →
         ---------------------
         Re ns - c $ d ↘ u $ w
    Ru : ∀ ns k →
         Re Tr ns k - c ↘ u →
         -------------------------
         Re ns - unbox k c ↘ unbox k u

mutual
  Rf-det : ∀ {n} → Rf n - d ↘ w → Rf n - d ↘ w′ → w ≡ w′
  Rf-det (RΛ _ ↘a ↘w) (RΛ _ ↘a′ ↘w′)
    rewrite ap-det ↘a ↘a′       = cong Λ (Rf-det ↘w ↘w′)
  Rf-det (R□ _ ↘a ↘w) (R□ _ ↘b ↘w′)
    rewrite unbox-det ↘a ↘b
          | Rf-det ↘w ↘w′       = refl
  Rf-det (Rne _ ↘u) (Rne _ ↘u′) = cong ne (Re-det ↘u ↘u′)

  Re-det : ∀ {n} → Re n - c ↘ u → Re n - c ↘ u′ → u ≡ u′
  Re-det (Rl _ x) (Rl _ .x) = refl
  Re-det (R$ _ ↘u ↘w) (R$ _ ↘u′ ↘w′)
    rewrite Re-det ↘u ↘u′
          | Rf-det ↘w ↘w′   = refl
  Re-det (Ru _ k ↘u) (Ru _ .k ↘u′) = cong (unbox k) (Re-det ↘u ↘u′)

record Nbe n ρ t T w : Set where
  field
    ⟦t⟧  : D
    ↘⟦t⟧ : ⟦ t ⟧ ρ ↘ ⟦t⟧
    ↓⟦t⟧ : Rf n - ↓ T ⟦t⟧ ↘ w

InitialCtx : Env → Ctx
InitialCtx []      i       = ↑ B (l 0)
InitialCtx (T ∷ Γ) zero    = l′ T (L.length Γ)
InitialCtx (T ∷ Γ) (suc i) = InitialCtx Γ i

InitialCtxs : Envs → Ctxs
InitialCtxs (Γ ∷ Γs) zero           = 1 , InitialCtx Γ
InitialCtxs (Γ ∷ []) (suc n)        = 1 , emp
InitialCtxs (Γ ∷ (Γ′ ∷ Γs)) (suc n) = InitialCtxs (Γ′ ∷ Γs) n
