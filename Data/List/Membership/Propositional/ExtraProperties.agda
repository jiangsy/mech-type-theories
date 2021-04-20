{-# OPTIONS --without-K --safe #-}

module Data.List.Membership.Propositional.ExtraProperties where

open import Level using (Level)

open import Data.List
open import Data.Nat.Properties
open import Data.List.Membership.Propositional

open import Lib

private
  variable
    a : Level
    A : Set a
    l l′ l″ : List A

<-length-∈ : ∀ {n a} l →
             n ∶ a ∈ l ++ l′ →
             n < length l →
             n ∶ a ∈ l
<-length-∈ (x ∷ l) here (s≤s n<)       = here
<-length-∈ (x ∷ l) (there a∈) (s≤s n<) = there (<-length-∈ l a∈ n<)

length-++-∈ : ∀ {n a} l′ →
           n ∶ a ∈ l →
           length l′ + n ∶ a ∈ l′ ++ l
length-++-∈ [] a∈l       = a∈l
length-++-∈ (x ∷ l′) a∈l = there (length-++-∈ l′ a∈l)

∈-++ : ∀ {n a} →
       n ∶ a ∈ l →
       n ∶ a ∈ l ++ l′
∈-++ here        = here
∈-++ (there a∈l) = there (∈-++ a∈l)

-- length-≡-∈ : ∀ {a} l′ →
--              length l′ ∶ a ∈ l′ ++ a ∷ l
-- length-≡-∈ []       = here
-- length-≡-∈ (x ∷ l′) = there (length-≡-∈ l′)

length-≤-∈ : ∀ {n a} l →
             n ∶ a ∈ l ++ l′ →
             length l ≤ n →
             length l″ + n ∶ a ∈ l ++ l″ ++ l′
length-≤-∈ {_} {_} {_} {l″} [] a∈ z≤n = length-++-∈ l″ a∈
length-≤-∈ {_} {_} {_} {l″} {suc n} (x ∷ l) (there a∈) (s≤s ≤n)
  rewrite +-comm (length l″) (suc n)
        | +-comm n (length l″)        = there (length-≤-∈ l a∈ ≤n)
