module StackMachine where

open import Data.Nat using (ℕ; _+_; _*_)
open import Data.List using (List; _∷_; [_]; _++_; [])
import Data.List as List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality using (refl; _≡_; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Algebra
open import Algebra.Structures
open import Data.Product using (proj₂; _×_; _,_)
open import Function using (case_of_)
open import Relation.Nullary.Decidable using (⌊_⌋)

module Untyped where
  data Binop : Set where
    plus times : Binop
  
  data Exp : Set where
    const : ℕ                 → Exp
    binop : Binop → Exp → Exp → Exp
  
  binopDenote : Binop → ℕ → ℕ → ℕ
  binopDenote plus  = _+_
  binopDenote times = _*_
  
  expDenote : Exp → ℕ
  expDenote (const n) = n
  expDenote (binop op e₁ e₂) = binopDenote op (expDenote e₁) (expDenote e₂)
  
  data Instr : Set where
    iConst : ℕ     → Instr
    iBinop : Binop → Instr
  
  Prog : Set
  Prog = List Instr
  
  Stack : Set
  Stack = List ℕ
  
  instrDenote : Instr → Stack → Maybe Stack
  instrDenote (iConst n) s = just (n ∷ s)
  instrDenote (iBinop b) (arg₁ ∷ arg₂ ∷ s) = just (binopDenote b arg₁ arg₂ ∷ s)
  instrDenote (iBinop b) _ = nothing
  
  progDenote : Prog → Stack → Maybe Stack
  progDenote [] s = just s
  progDenote (i ∷ p) s with instrDenote i s
  ... | nothing = nothing
  ... | just s' = progDenote p s'
  
  compile : Exp → Prog
  compile (const n)        = [ iConst n ]
  compile (binop op e₁ e₂) = compile e₂ ++ compile e₁ ++ [ iBinop op ]
  
  compile-correct′ : ∀ e p s →
                    progDenote (compile e ++ p) s ≡ progDenote p (expDenote e ∷ s)
  compile-correct′ (const n) _ _  = refl
  compile-correct′ (binop op e₁ e₂) p s = begin
      progDenote ((compile e₂ ++ (compile e₁ ++ [ iBinop op ])) ++ p) s
          ≡⟨ cong (λ p → progDenote p s)
                  (assoc (compile e₂) (compile e₁ ++ [ iBinop op ]) p) ⟩
      progDenote (compile e₂ ++ (compile e₁ ++ [ iBinop op ]) ++ p) s
          ≡⟨ cong (λ p → progDenote p s) 
                  (cong (λ l → (compile e₂ ++ l))
                        (assoc (compile e₁) [ iBinop op ] p)) ⟩
      progDenote (compile e₂ ++ compile e₁ ++ [ iBinop op ] ++ p) s
          ≡⟨ compile-correct′ e₂ (compile e₁ ++ [ iBinop op ] ++ p) s ⟩
      progDenote (compile e₁ ++ [ iBinop op ] ++ p) (expDenote e₂ ∷ s)
          ≡⟨ compile-correct′ e₁ ([ iBinop op ] ++ p) (expDenote e₂ ∷ s) ⟩
      progDenote p (binopDenote op (expDenote e₁) (expDenote e₂) ∷ s)
          ∎
    where
      open Monoid (List.monoid Instr)
  
  compile-correct : ∀ e → progDenote (compile e) [] ≡ just [ expDenote e ]
  compile-correct e = begin
      progDenote (compile e) []
          ≡⟨ cong (λ p → progDenote p []) (sym (proj₂ identity (compile e))) ⟩
      progDenote (compile e ++ []) []
          ≡⟨ compile-correct′ e [] [] ⟩
      just [ expDenote e ]
          ∎
    where
      open Monoid (List.monoid Instr)

module Typed where  
  data Type : Set where
    nat bool : Type
  
  data Binop : Type → Type → Type → Set where
    plus times :       Binop nat nat nat
    eq         : ∀ t → Binop t   t   bool
    lt         :       Binop nat nat bool
    
  typeDenote : Type → Set
  typeDenote nat  = ℕ
  typeDenote bool = Bool

  data Exp : Type → Set where
    const  : ∀ {t}       → typeDenote t                    → Exp t
    binop  : ∀ {t₁ t₂ t} → Binop t₁ t₂ t → Exp t₁ → Exp t₂ → Exp t
  
  binopDenote : ∀ {arg₁ arg₂ res} → Binop arg₁ arg₂ res →
                typeDenote arg₁ → typeDenote arg₂ → typeDenote res
  binopDenote plus      = _+_
  binopDenote times     = _*_
  binopDenote (eq nat)  = λ n  m  → ⌊ n  ≟  m  ⌋ where open Data.Nat
  binopDenote (eq bool) = λ b₁ b₂ → ⌊ b₁ ≟  b₂ ⌋ where open Data.Bool
  binopDenote lt        = λ n  m  → ⌊ n  ≤? m  ⌋ where open Data.Nat
  
  expDenote : ∀ {t} → Exp t → typeDenote t
  expDenote (const c)        = c
  expDenote (binop op e₁ e₂) = binopDenote op (expDenote e₁) (expDenote e₂)
  
  TyStack : Set
  TyStack = List Type
  
  data Instr : TyStack → TyStack → Set where
    iConst : ∀ {t s} → typeDenote t → Instr s (t ∷ s)
    iBinop : ∀ {arg₁ arg₂ res s} → Binop arg₁ arg₂ res →
             Instr (arg₁ ∷ arg₂ ∷ s) (res ∷ s)
  
  data Prog : TyStack → TyStack → Set where
    nil  : ∀ {ts}                                         → Prog ts ts
    cons : ∀ {ts₁ ts₂ ts₃} → Instr ts₁ ts₂ → Prog ts₂ ts₃ → Prog ts₁ ts₃
  
  VStack : TyStack → Set
  VStack []       = ⊤
  VStack (t ∷ ts) = typeDenote t × VStack ts
  
  instrDenote : ∀ {ts ts′} → Instr ts ts′ → VStack ts → VStack ts′
  instrDenote (iConst c) s                  = c , s
  instrDenote (iBinop op) (arg₁ , arg₂ , s) = binopDenote op arg₁ arg₂ , s
  
  progDenote : ∀ {ts ts′} → Prog ts ts′ → VStack ts → VStack ts′
  progDenote nil        s = s
  progDenote (cons i p) s = progDenote p (instrDenote i s)
  
  concat : ∀ {ts ts′ ts′′} → Prog ts ts′ → Prog ts′ ts′′ → Prog ts ts′′
  concat nil        p′ = p′
  concat (cons i p) p′ = cons i (concat p p′)
  
  compile : ∀ {t} → Exp t → ∀ {ts} → Prog ts (t ∷ ts)
  compile (const c)        = cons (iConst c) nil
  compile (binop op e₁ e₂) =
      concat (compile e₂) (concat (compile e₁) (cons (iBinop op) nil))

  concat-correct : ∀ {ts ts′ ts′′} (p : Prog ts ts′) (p′ : Prog ts′ ts′′)
                   (s : VStack ts) →
                   progDenote (concat p p′) s ≡ progDenote p′ (progDenote p s)
  concat-correct nil        p′ s = refl
  concat-correct (cons {ts₂ = []} () p) p′ s
  concat-correct (cons {ts₂ = t ∷ ts₂} (iConst c) p) p′ s =
      concat-correct p p′ (c , s)
  concat-correct (cons {.(arg₁ ∷ arg₂ ∷ ts₂)} {t ∷ ts₂} (iBinop {arg₁} {arg₂} op) p)
                 p′ (n , m , s) =
      concat-correct p p′ (binopDenote op n m , s)

  compile-correct′ : ∀ t (e : Exp t) ts (s : VStack ts) →
                     progDenote (compile e) s ≡ expDenote e , s
  compile-correct′ t (const c)        ts s = refl
  compile-correct′ t (binop {t₁} {t₂} op e₁ e₂) ts s = begin
      progDenote (concat (compile e₂) (concat (compile e₁) (cons (iBinop op) nil)))
                 s
          ≡⟨ concat-correct (compile e₂) _ s ⟩
      progDenote (concat (compile e₁) (cons (iBinop op) nil))
                 (progDenote (compile e₂) s)
          ≡⟨ cong (λ p → progDenote (concat (compile e₁) (cons (iBinop op) nil)) p)
                  (compile-correct′ t₂ e₂ ts s) ⟩
      progDenote (concat (compile e₁) (cons (iBinop op) nil)) (expDenote e₂ , s)
          ≡⟨ concat-correct (compile e₁) (cons (iBinop op) nil) _ ⟩
      progDenote (cons (iBinop op) nil) (progDenote (compile e₁) (expDenote e₂ , s))
          ≡⟨ cong (λ p → progDenote (cons (iBinop op) nil) p)
                  (compile-correct′ t₁ e₁ _ _) ⟩
      progDenote (cons (iBinop op) nil) (expDenote e₁ , expDenote e₂ , s)
          ∎

  compile-correct : ∀ (t : Type) e →
                    progDenote (compile {t} e) tt ≡ expDenote e , tt
  compile-correct t e = compile-correct′ t e [] tt
