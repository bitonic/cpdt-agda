module Coinductive where

open import Relation.Binary.PropositionalEquality
            using (refl; _≡_; cong; sym; trans; subst; _≢_; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _*_; _+_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _∷_; [])
open import Coinduction
open import Data.Product using (_,_; proj₁; proj₂; ∃)
import Data.Nat.Properties
open Data.Nat.Properties.SemiringSolver
open import Function using (_∘_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Common

-- TODO rewrite the proofs more nicely without the combinators

data Stream (A : Set) : Set where
  _∷_ : (x : A) (xs : ∞ (Stream A)) → Stream A

zeroes : Stream ℕ
zeroes = 0 ∷ ♯ zeroes

trues-falses : Stream Bool
trues-falses      = true ∷ ♯ (false ∷ ♯ trues-falses)

approx : ∀ {A} → Stream A → ℕ → List A
approx s       zero    = []
approx (x ∷ s) (suc n) = x ∷ approx (♭ s) n

map : ∀ {A B} → (A → B) → Stream A → Stream B
map f (x ∷ s) = f x ∷ ♯ map f (♭ s)

interleave : ∀ {A} → Stream A → Stream A → Stream A
interleave (h₁ ∷ s₁) (h₂ ∷ s₂) = h₁ ∷ ♯ (h₂ ∷ ♯ interleave (♭ s₁) (♭ s₂))

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
  stream-= : ∀ h {t₁ t₂} → ∞ (Stream-= (♭ t₁) (♭ t₂)) → Stream-= (h ∷ t₁) (h ∷ t₂)

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
stream-=-coind R f g (h₁ ∷ t₁) (.h₁ ∷ t₂) p | refl =
    stream-= h₁ (♯ stream-=-coind R f g (♭ t₁) (♭ t₂) (g p))

ones-=′ : Stream-= ones ones′
ones-=′ = stream-=-coind (λ s₁ s₂ → s₁ ≡ ones ∧ s₂ ≡ ones′)
                         (λ { (r₁ , r₂) → trans (cong hd r₁) (sym (cong hd r₂)) })
                         (λ { (r₁ , r₂) → cong tl r₁ , cong tl r₂})
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

fact : ℕ → ℕ
fact zero    = 1
fact (suc n) = suc n * fact n

fact-slow′ : ℕ → Stream ℕ
fact-slow′ n = fact n ∷ ♯ fact-slow′ (suc n)

fact-slow : Stream ℕ
fact-slow = fact-slow′ 1

fact-iter′ : ℕ → ℕ → Stream ℕ
fact-iter′ cur acc = acc ∷ ♯ fact-iter′ (suc cur) (acc * cur)

fact-iter : Stream ℕ
fact-iter = fact-iter′ 2 1

fact-suc : ∀ n → fact n * suc n ≡ fact n + n * fact n
fact-suc n = solve 2 (λ n m → n :* :suc m := n :+ m :* n) refl (fact n) n

fact-def : ∀ x n → fact-iter′ x (fact n * suc n) ≡ fact-iter′ x (fact (suc n))
fact-def x n = cong (fact-iter′ x) (fact-suc n)

fact-eq′ : ∀ n → Stream-= (fact-iter′ (suc n) (fact n)) (fact-slow′ n)
fact-eq′ n = stream-=-coind R hd-case tl-case
                            (fact-iter′ (suc n) (fact n)) (fact-slow′ n)
                            (n , refl , refl)
  where
    R : Stream ℕ → Stream ℕ → Set
    R s₁ s₂ = ∃ (λ n → s₁ ≡ fact-iter′ (suc n) (fact n) ∧ s₂ ≡ fact-slow′ n)

    hd-case : ∀ {s₁ s₂} → R s₁ s₂ → hd s₁ ≡ hd s₂
    hd-case {s₁} {s₂} (n , r₁ , r₂) = begin
        hd s₁                            ≡⟨ cong hd r₁ ⟩
        hd (fact-iter′ (suc n) (fact n)) ≡⟨ cong hd (sym r₂) ⟩
        hd s₂                            ∎

    tl-case : ∀ {s₁ s₂} → R s₁ s₂ → R (tl s₁) (tl s₂)
    tl-case {s₁} {s₂} (n , r₁ , r₂) =
        suc n ,
        (begin tl s₁
                   ≡⟨ cong tl r₁ ⟩
               tl (fact-iter′ (suc n) (fact n))
                   ≡⟨ fact-def (suc (suc n)) n ⟩
               fact-iter′ (suc (suc n)) (fact n + n * fact n)
                   ∎) ,
        cong tl r₂

fact-eq : Stream-= fact-iter fact-slow
fact-eq = fact-eq′ 1

stream-=-onequant : (A B : Set)
                    (f g : A → Stream B) →
                    (∀ x → hd (f x) ≡ hd (g x)) →
                    (∀ x → ∃ (λ y → tl (f x) ≡ f y ∧ tl (g x) ≡ g y)) →
                    ∀ x → Stream-= (f x) (g x)
stream-=-onequant A B f g bhd btl x =
    stream-=-coind R hd-case tl-case (f x) (g x) (x , refl , refl)
  where
    R : Stream _ → Stream _ → Set
    R s₁ s₂ = ∃ (λ x → s₁ ≡ f x ∧ s₂ ≡ g x)

    hd-case : ∀ {s₁ s₂} → R s₁ s₂ → hd s₁ ≡ hd s₂
    hd-case {s₁} {s₂} (x , r₁ , r₂) = begin hd s₁    ≡⟨ cong hd r₁ ⟩
                                            hd (f x) ≡⟨ bhd x ⟩
                                            hd (g x) ≡⟨ cong hd (sym r₂) ⟩
                                            hd s₂    ∎

    tl-case : ∀ {s₁ s₂} → R s₁ s₂ → R (tl s₁) (tl s₂)
    tl-case {s₁} {s₂} (x , r₁ , r₂) =
        let (y , p , q) = btl x in
        y , trans (cong tl r₁) p , trans (cong tl r₂) q

Var : Set
Var = ℕ

Vars : Set
Vars = Var → Var

set : Vars → Var → ℕ → Vars
set vs v n v′ = if ⌊ v ≟ v′ ⌋ then n else vs v′ where open Data.Nat

data Exp : Set where
  const : ℕ         → Exp
  var   : Var       → Exp
  plus  : Exp → Exp → Exp

evalExp : Vars → Exp → ℕ
evalExp vs (const n)    = n
evalExp vs (var v)      = vs v
evalExp vs (plus e₁ e₂) = evalExp vs e₁ + evalExp vs e₂

data Cmd : Set where
  assign : Var → Exp → Cmd
  seq    : Cmd → Cmd → Cmd
  while  : Exp → Cmd → Cmd

data EvalCmd (vs : Vars) : Cmd → Vars → Set where
  evalAssign     : ∀ {v e} →
                   EvalCmd vs (assign v e) (set vs v (evalExp vs e))
  evalSeq        : ∀ {vs₁ vs₂ c₁ c₂} →
                   ∞ (EvalCmd vs c₁ vs₁) → ∞ (EvalCmd vs₁ c₂ vs₂) →
                   EvalCmd vs (seq c₁ c₂) vs₂
  evalWhileFalse : ∀ {e c} → evalExp vs e ≡ 0 → EvalCmd vs (while e c) vs
  evalWhileTrue  : ∀ {vs₁ vs₂ e c} →
                   evalExp vs e ≢ 0 →
                   ∞ (EvalCmd vs c vs₂) → ∞ (EvalCmd vs₁ (while e c) vs₂) →
                   EvalCmd vs (while e c) vs₂

evalCmd-coind : (R : Vars → Cmd → Vars → Set) →
                (∀ vs₁ vs₂ v e   → R vs₁ (assign v e) vs₂) →
                (∀ vs₁ vs₃ c₁ c₂ → R vs₁ (seq c₁ c₂) vs₃) →
                (∀ vs₁ vs₃ e c   → R vs₁ (while e c) vs₃) →
                ∀ vs₁ c vs₂ → R vs₁ c vs₂ → EvalCmd vs₁ c vs₂
evalCmd-coind R assc seqc whilec vs₁ (assign v e) vs₂ r = {!!}
evalCmd-coind R assc seqc whilec vs₁ (seq c₁ c₂)  vs₂ r = {!!}
evalCmd-coind R assc seqc whilec vs₁ (while e c)  vs₂ r = {!!}

optExp′ : (e : Exp) → ∃ (λ e′ → ∀ {vs} → evalExp vs e′ ≡ evalExp vs e)
optExp′ (plus (const 0) e) = let (e′ , p ) = optExp′ e in e′ , p
optExp′ (plus e₁ e₂)       = let (e₁′ , p) = optExp′ e₁
                                 (e₂′ , q) = optExp′ e₂
                             in plus e₁′ e₂′ , cong₂ _+_ p q
optExp′ e                  = e , refl

optExp : Exp → Exp
optExp = proj₁ ∘ optExp′

optExp-correct : ∀ e {vs} → evalExp vs (optExp e) ≡ evalExp vs e
optExp-correct = proj₂ ∘ optExp′

optCmd : Cmd → Cmd
optCmd (assign v e) = assign v (optExp e)
optCmd (seq c₁ c₂)  = seq (optCmd c₁) (optCmd c₂)
optCmd (while e c)  = while (optExp e) (optCmd c)
