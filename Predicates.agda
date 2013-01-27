module Predicates where

open import Algebra.Structures
open import Relation.Binary.PropositionalEquality using (refl; _≡_; cong; sym; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Nullary using (¬_)
open import Data.Unit using (⊤; tt)
open import Data.Empty
open import Data.Nat using (ℕ; _+_; _≤_; z≤n; s≤s; zero; suc; pred)
import Data.Nat.Properties
open IsCommutativeSemiring Data.Nat.Properties.isCommutativeSemiring using
     (+-comm; +-assoc)
open import Data.Product using (_,_; ∃)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using (List; []; _∷_; length; _++_; sum; map; [_])
open import Function

open import Common

module Propositional (P Q R : Set) where
  obvious : ⊤
  obvious = tt

  ⊥-imp : ⊥ → 2 + 2 ≡ 5
  ⊥-imp ()

  arith-neq : 2 + 2 ≡ 5 → 9 + 9 ≡ 835
  arith-neq ()

  arith-neq′ : ¬ (2 + 2 ≡ 5)
  arith-neq′ ()

  and-comm : P ∧ Q → Q ∧ P
  and-comm (p , q) = (q , p)

  or-comm : P ∨ Q → Q ∨ P
  or-comm (inj₁ p) = inj₂ p
  or-comm (inj₂ p) = inj₁ p

  contra : P → ¬ P → R
  contra p ¬p = ⊥-elim (¬p p)

  and-assoc : (P ∧ Q) ∧ R → P ∧ (Q ∧ R)
  and-assoc ((p , q) , r) = (p , (q , r))

  or-assoc : (P ∨ Q) ∨ R → P ∨ (Q ∨ R)
  or-assoc (inj₁ (inj₁ p)) = inj₁ p
  or-assoc (inj₁ (inj₂ q)) = inj₂ (inj₁ q)
  or-assoc (inj₂ r)        = inj₂ (inj₂ r)

  arith-comm : (ls₁ ls₂ : List ℕ) →
               length ls₁ ≡ length ls₂ ∨ length ls₁ + length ls₂ ≡ 6 →
               length (ls₁ ++ ls₂) ≡ 6 ∨ length ls₁ ≡ length ls₂
  arith-comm ls₁ ls₂ (inj₁ p) = inj₂ p
  arith-comm ls₁ ls₂ (inj₂ p) = inj₁ (trans (length-++ ls₁) p)
    where open import Data.List.Properties

exists1 : ∃ (λ x → x + 1 ≡ 2)
exists1 = 1 , refl

n+x≡m : ∀ n {x} m → n + x ≡ m → n ≤ m
n+x≡m zero    m       p = z≤n
n+x≡m (suc n) zero    ()
n+x≡m (suc n) (suc m) p = s≤s (n+x≡m n m (cong pred p))

exists2 : ∀ n m → ∃ (λ x → n + x ≡ m) → n ≤ m
exists2 n m (x , p) = n+x≡m n m p

∀-∃-commute : {A B : Set} {P : A → B → Set} →
              ∃ (λ x → ∀ y → P x y) → (∀ y → ∃ (λ x → P x y))
∀-∃-commute (x , f) y = x , f y

data IsZero : ℕ → Set where
  isZero : IsZero 0

isZero-0 : IsZero 0
isZero-0 = isZero

isZero-+ : ∀ n m → IsZero m → n + m ≡ n
isZero-+ n .0 isZero = +-comm n 0

isZero-contra : IsZero 1 → ⊥
isZero-contra ()

isZero-contra′ : IsZero 1 → 2 + 2 ≡ 5
isZero-contra′ ()

-- TODO Needs finishing