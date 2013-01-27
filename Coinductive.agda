{-# OPTIONS --copatterns #-}
module Coinductive where

open import Relation.Binary.PropositionalEquality
            using (refl; _≡_; cong; sym; trans; subst)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; _∷_; [])
open import Coinduction
open import Data.Product using (_,_; proj₁; proj₂)

open import Common

record Stream (A : Set) : Set where
  coinductive
  field hd : A
        tl : Stream A
open Stream

zeroes : Stream ℕ
hd zeroes = 0
tl zeroes = zeroes

trues-falses : Stream Bool
hd trues-falses      = true
hd (tl trues-falses) = false
tl (tl trues-falses) = trues-falses

approx : ∀ {A} → Stream A → ℕ → List A
approx s zero    = []
approx s (suc n) = hd s ∷ approx (tl s) n

map : ∀ {A B} → (A → B) → Stream A → Stream B
hd (map f s) = f (hd s)
tl (map f s) = map f (tl s)

interleave : ∀ {A} → Stream A → Stream A → Stream A
hd (interleave xs ys)      = hd xs
hd (tl (interleave xs ys)) = hd ys
tl (tl (interleave xs ys)) = interleave (tl xs) (tl ys)

ones : Stream ℕ
hd ones = 1
tl ones = ones

ones′ : Stream ℕ
ones′ = map suc zeroes

-- -- Not going to work
-- -- ones-= : ones ≡ ones′
-- -- ones-= = {!!}

record Stream-= {A : Set} (xs : Stream A) (ys : Stream A) : Set where
  coinductive
  field
    hd=hd : hd xs ≡ hd ys
    tl=tl : Stream-= (tl xs) (tl ys)
open Stream-=

ones-= : Stream-= ones ones′
hd=hd ones-= = refl
tl=tl ones-= = ones-=

-- Bisimulation
stream-=-coind : ∀ {A} (R : Stream A → Stream A → Set) →
                 (∀ {s₁ s₂} → R s₁ s₂ → hd s₁ ≡ hd s₂) →
                 (∀ {s₁ s₂} → R s₁ s₂ → R (tl s₁) (tl s₂)) →
                 ∀ s₁ s₂ → R s₁ s₂ → Stream-= s₁ s₂
hd=hd (stream-=-coind R f g s₁ s₂ p) = f p
tl=tl (stream-=-coind R f g s₁ s₂ p) = stream-=-coind R f g (tl s₁) (tl s₂) (g p)

ones-=′ : Stream-= ones ones′
ones-=′ = stream-=-coind (λ s₁ s₂ → s₁ ≡ ones ∧ s₂ ≡ ones′)
                         (λ { (r₁ , r₂) → trans (cong hd r₁) (sym (cong hd r₂)) })
                         (λ { (r₁ , r₂) → cong tl r₁ , cong tl r₂})
                         ones ones′ (refl , refl)

stream-=-loop : ∀ {A} (s₁ s₂ : Stream A) →
                hd s₁ ≡ hd s₂ → tl s₁ ≡ s₁ → tl s₂ ≡ s₂ →
                Stream-= s₁ s₂
hd=hd (stream-=-loop s₁ s₂ p q s) = p
tl=tl (stream-=-loop s₁ s₂ p q s) =
  stream-=-loop (tl s₁) (tl s₂)
                (begin hd (tl s₁) ≡⟨ trans (cong hd q) p ⟩
                       hd s₂      ≡⟨ cong hd (sym s) ⟩
                       hd (tl s₂) ∎)
                (cong tl q) (cong tl s)

-- Just using `stream-=-loop' 
stream-=-loop′ : ∀ {A} (s₁ s₂ : Stream A) →
                 hd s₁ ≡ hd s₂ → tl s₁ ≡ s₁ → tl s₂ ≡ s₂ →
                 Stream-= s₁ s₂
stream-=-loop′ s₁ s₂ p q s =
    stream-=-coind R hd-case
                   (λ {(r₁ , r₂) → trans (cong tl r₁) q , trans (cong tl r₂) s})
                   s₁ s₂ (refl , refl)
  where
    R : Stream _ → Stream _ → Set
    R s₁′ s₂′ = s₁′ ≡ s₁ ∧ s₂′ ≡ s₂

    hd-case : ∀ {s₁′ s₂′} → R s₁′ s₂′ → hd s₁′ ≡ hd s₂′
    hd-case  {s₁′} {s₂′} (r₁ , r₂) = begin hd s₁′ ≡⟨ trans (cong hd r₁) p ⟩
                                           hd s₂  ≡⟨ cong hd (sym r₂) ⟩
                                           hd s₂′ ∎

ones-=′′ : Stream-= ones ones′
ones-=′′ = stream-=-loop ones ones′ refl refl refl
