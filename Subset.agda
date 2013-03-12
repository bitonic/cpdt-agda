module Subset where

open import Data.Nat using (ℕ; zero; suc; _>_; z≤n; s≤s; pred)
open import Data.Empty
open import Data.List using (List; []; _∷_; [_])
open import Data.Product using (∃; Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_; cong; sym)
open import Relation.Binary
open import Relation.Nullary
open import Function

z>z : 0 > 0 → ⊥
z>z ()

pred-strong₁ : (n : ℕ) → n > 0 → ℕ
pred-strong₁ zero    ()
pred-strong₁ (suc n) _  = n

two-gt₀ : 2 > 0
two-gt₀ = s≤s z≤n

pred-strong₂ : Σ ℕ (λ n → n > 0) → ℕ
pred-strong₂ (zero ,  ())
pred-strong₂ (suc n , _)  = n

pred-strong₃ : (s : Σ ℕ (λ n → n > 0)) → Σ ℕ (λ m → proj₁ s ≡ suc m)
pred-strong₃ (zero  , ())
pred-strong₃ (suc n , p)  = n , refl

pred-strong₄ : (n : ℕ) → n > 0 → Σ ℕ (λ m → n ≡ suc m)
pred-strong₄ zero    ()
pred-strong₄ (suc n) _  = n , refl

≡-ℕ-dec : Decidable {A = ℕ} _≡_
≡-ℕ-dec zero    zero    = yes refl
≡-ℕ-dec zero    (suc m) = no λ()
≡-ℕ-dec (suc n) zero    = no λ()
≡-ℕ-dec (suc n) (suc m) with ≡-ℕ-dec n m
≡-ℕ-dec (suc n) (suc m) | yes p = yes (cong suc p)
≡-ℕ-dec (suc n) (suc m) | no ¬p = no (¬p ∘ cong pred)

data _∈_ {A : Set} (x : A) : List A → Set where
  hd : ∀ {xs}   → x ∈ (x ∷ xs)
  tl : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

module ∈-dec (A : Set) (≡-A-dec : Decidable {A = A} _≡_) where
  ¬≡-¬tl : {x x′ : A} → ∀ {xs} → ¬ (x ≡ x′) → ¬ (x ∈ xs) → ¬ (x ∈ (x′ ∷ xs))
  ¬≡-¬tl ¬≡ ¬tl hd     = ¬≡ refl
  ¬≡-¬tl ¬≡ ¬tl (tl ∈) = ¬tl ∈

  ∈-dec : Decidable {A = A} {B = List A} _∈_
  ∈-dec x []        = no λ()
  ∈-dec x (x′ ∷ xs) with ≡-A-dec x x′
  ∈-dec x (.x ∷ xs) | yes refl = yes hd
  ∈-dec x (x′ ∷ xs) | no ¬≡ with ∈-dec x xs
  ∈-dec x (x′ ∷ xs) | no ¬≡ | yes q  = yes (tl q)
  ∈-dec x (x′ ∷ xs) | no ¬≡ | no ¬tl = no (¬≡-¬tl ¬≡ ¬tl)

data Maybe (A : Set) (P : A → Set) : Set where
  Unknown : Maybe A P
  Found   : {x : A} → P x → Maybe A P

