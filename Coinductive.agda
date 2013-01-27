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

data Stream (A : Set) : Set where
  _∷_ : (x : A) (xs : ∞ (Stream A)) → Stream A

zeroes : Stream ℕ
zeroes = 0 ∷ ♯ zeroes

mutual
  trues-falses falses-trues : Stream Bool
  trues-falses = true  ∷ ♯ falses-trues
  falses-trues = false ∷ ♯ trues-falses

approx : ∀ {A} → Stream A → ℕ → List A
approx (_ ∷ _)  zero    = []
approx (x ∷ xs) (suc n) = x ∷ approx (♭ xs) n

map : ∀ {A B} → (A → B) → Stream A → Stream B
map f (x ∷ xs) = f x ∷ ♯ (map f (♭ xs))

interleave : ∀ {A} → Stream A → Stream A → Stream A
interleave (x ∷ xs) (y ∷ ys) = x ∷ ♯ (y ∷ ♯ interleave (♭ xs) (♭ ys))

tl : ∀ {A} → Stream A → Stream A
tl (_ ∷ xs) = ♭ xs

ones : Stream ℕ
ones = 1 ∷ ♯ ones

ones′ : Stream ℕ
ones′ = map suc zeroes

-- Not going to work
-- ones-= : ones ≡ ones′
-- ones-= = {!!}

data Stream-= {A} : Stream A → Stream A → Set where
  stream-= : ∀ h {t₁ t₂} →  ∞ (Stream-= (♭ t₁) (♭ t₂)) → Stream-= (h ∷ t₁) (h ∷ t₂)

ones-= : Stream-= ones ones′
ones-= = stream-= 1 (♯ ones-=)

hd : ∀ {A} → Stream A → A
hd (x ∷ _) = x

-- Bisimulation
stream-=-coind : ∀ {A} (R : Stream A → Stream A → Set) →
                 (∀ {s₁ s₂} → R s₁ s₂ → hd s₁ ≡ hd s₂) →
                 (∀ {s₁ s₂} → R s₁ s₂ → R (tl s₁) (tl s₂)) →
                 ∀ s₁ s₂ → R s₁ s₂ → Stream-= s₁ s₂
stream-=-coind R f g (h₁ ∷ t₁) ( h₂ ∷ t₂) p with f p 
stream-=-coind R f g (h₁ ∷ t₁) (.h₁ ∷ t₂) p  | refl =
    stream-= h₁ (♯ stream-=-coind R f g (♭ t₁) (♭ t₂) (g p))

ones-=′ : Stream-= ones ones′
ones-=′ = stream-=-coind (λ s₁ s₂ → s₁ ≡ ones ∧ s₂ ≡ ones′)
                         (λ {_}  {s₂} p → {!!})
                         (λ {s₁} {s₂} p → {!!} , {!!})
                         ones ones′ (refl , refl)

stream-=-loop : ∀ {A} (s₁ s₂ : Stream A) →
                hd s₁ ≡ hd s₂ → tl s₁ ≡ s₁ → tl s₂ ≡ s₂ →
                Stream-= s₁ s₂
stream-=-loop s₁ s₂ p q s =
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
