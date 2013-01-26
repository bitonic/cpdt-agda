module InductiveTypes where

open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; _+_; zero; suc)
open import Data.Bool using (true; false; not; Bool)
open import Data.List using (List; []; _∷_; length; _++_)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_; cong; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Algebra.Structures
import Data.Nat.Properties
open IsCommutativeSemiring Data.Nat.Properties.isCommutativeSemiring using
     (+-comm; +-assoc)

unit-singleton : ∀ {x} → x ≡ tt
unit-singleton = refl

the-sky-is-falling : (x : ⊥) → 2 + 2 ≡ 5
the-sky-is-falling ()

negb-inverse : ∀ b → not (not b) ≡ b
negb-inverse true  = refl
negb-inverse false = refl

negb-≢ : ∀ b → not b ≢ b
negb-≢ true  () 
negb-≢ false ()

isZero : ∀ n → Bool
isZero zero = true
isZero _    = false

0+n : ∀ {n} → 0 + n ≡ n
0+n = refl

n+0 : ∀ {n} → n + 0 ≡ n
n+0 {zero}  = refl
n+0 {suc n} = cong suc n+0

suc-inj : ∀ {n m} → suc n ≡ suc m → n ≡ m
suc-inj refl = refl

data Listℕ : Set where
  nilℕ : Listℕ
  _∷ℕ_ : ℕ → Listℕ → Listℕ

lengthℕ : Listℕ → ℕ
lengthℕ nilℕ      = 0
lengthℕ (n ∷ℕ ns) = suc (lengthℕ ns)

appℕ : Listℕ → Listℕ → Listℕ
appℕ nilℕ      ns = ns
appℕ (n ∷ℕ ns) ms = n ∷ℕ (appℕ ns ms)

lengthℕ-appℕ : ∀ {ns ms} → lengthℕ (appℕ ns ms) ≡ lengthℕ ns + lengthℕ ms
lengthℕ-appℕ {nilℕ}    = refl
lengthℕ-appℕ {x ∷ℕ ns} = cong suc (lengthℕ-appℕ {ns})

data Treeℕ : Set where
  leafℕ : Treeℕ
  nodeℕ : Treeℕ → ℕ → Treeℕ → Treeℕ

sizeℕ : Treeℕ → ℕ
sizeℕ leafℕ             = 1
sizeℕ (nodeℕ tr₁ n tr₂) = (sizeℕ tr₁) + (sizeℕ tr₂)

spliceℕ : (tr₁ tr₂ : Treeℕ) → Treeℕ
spliceℕ leafℕ             tr₂ = nodeℕ tr₂ 0 leafℕ
spliceℕ (nodeℕ tr₁ n tr₂) tr₃ = nodeℕ (spliceℕ tr₁ tr₃) n tr₂

-- Commented out since IsCommutativeSemiring has exactly the same
-- +-assoc : ∀ {n₁ n₂ n₃} → (n₁ + n₂) + n₃ ≡ n₁ + (n₂ + n₃)
-- +-assoc {zero}   = refl
-- +-assoc {suc n₁} = cong suc (+-assoc {n₁})

foo : ∀ {x y z} → x + y + z ≡ (x + y) + z
foo = refl

sizeℕ-spliceℕ : ∀ tr₁ tr₂ → sizeℕ (spliceℕ tr₁ tr₂) ≡ sizeℕ tr₁ + sizeℕ tr₂
sizeℕ-spliceℕ leafℕ             tr₂ = +-comm (sizeℕ tr₂) 1
sizeℕ-spliceℕ (nodeℕ tr₁ n tr₂) tr₃ = begin
    sizeℕ (spliceℕ tr₁ tr₃) + str₂
       ≡⟨ cong (λ p → p + str₂) (sizeℕ-spliceℕ tr₁ tr₃) ⟩
    str₁ + str₃ + str₂
       ≡⟨ +-assoc str₁ _ _ ⟩
    str₁ + (str₃ + str₂)
       ≡⟨ cong (λ p → str₁ + p) (+-comm str₃ _) ⟩
    str₁ + (str₂ + str₃)
       ≡⟨ sym (+-assoc str₁ _ _) ⟩
    str₁ + str₂ + str₃
       ∎
  where
    str₁ = sizeℕ tr₁
    str₂ = sizeℕ tr₂
    str₃ = sizeℕ tr₃

-- Omitting the `list' stuff since we have everything we need...

-- Even agsy can do this!  Take that crush...
length-++ : {A : Set} (xs₁ xs₂ : List A) →
            length (xs₁ ++ xs₂) ≡ length xs₁ + length xs₂
length-++ []        xs₂ = refl
length-++ (x ∷ xs₁) xs₂ = cong suc (length-++ xs₁ xs₂)

mutual
  data EvenList : Set where
    nilE : EvenList
    _∷E_ : ℕ → OddList → EvenList

  data OddList : Set where
    _∷O_ : ℕ → EvenList → OddList

mutual
  lengthE : EvenList → ℕ
  lengthE nilE      = 0
  lengthE (n ∷E ol) = 1 + lengthO ol

  lengthO : OddList → ℕ
  lengthO (n ∷O el) = 1 + lengthE el

mutual
  appE : EvenList → EvenList → EvenList
  appE nilE      el = el
  appE (n ∷E ol) el = n ∷E (appO ol el)

  appO : OddList → EvenList → OddList
  appO (n ∷O el₁) el₂ = n ∷O (appE el₁ el₂)


