module ProgLang where

import Level
open import Relation.Binary using (Setoid)
open import Data.Nat
open import Data.List hiding ([_])
open import Data.Unit
open import Data.Empty
open import Data.Product
import Data.List.Any
open import Relation.Binary.PropositionalEquality renaming ([_] to [_]≡)
open import Function hiding (const)

data Type : Set where
  nat : Type
  _⇒_ : Type → Type → Type

⟦_⟧ : Type → Set
⟦ nat ⟧   = ℕ
⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ → ⟦ τ ⟧

module FirstOrder where
  data _∈_ {A : Set} : A → List A → Set where
    here  : ∀ {x l}               → x ∈ (x ∷ l)
    there : ∀ {x l} → ∀ y → x ∈ l → x ∈ (y ∷ l)

  data HList {A : Set} (F : A → Set) : List A → Set where
    []  : HList F []
    _∷_ : ∀ {x xs} → F x → HList F xs → HList F (x ∷ xs)

  data Term : List Type → Type → Set where
    var   : ∀ {Γ σ}   → σ ∈ Γ                           → Term Γ σ
    const : ∀ {Γ}     → ℕ                               → Term Γ nat
    plus  : ∀ {Γ}     → Term Γ nat     → Term Γ nat     → Term Γ nat
    abs   : ∀ {Γ σ τ} → Term (σ ∷ Γ) τ                  → Term Γ (σ ⇒ τ)
    app   : ∀ {Γ σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ       → Term Γ τ
    let′  : ∀ {Γ σ τ} → Term Γ σ       → Term (σ ∷ Γ) τ → Term Γ τ

  lookup : ∀ {A} {x : A} → ∀ {xs f} → x ∈ xs → HList f xs → f x
  lookup here            (x ∷ _)       = x
  lookup (there .x x∈xs) (_∷_ {x} y l) = lookup x∈xs l

  hmap : ∀ {A F xs} {G : A → Set} → (∀ {x} → F x → G x) → HList F xs → HList G xs
  hmap f []      = []
  hmap f (x ∷ l) = f x ∷ hmap f l

  _[_] : ∀ {Γ σ} → HList ⟦_⟧ Γ → Term Γ σ → ⟦ σ ⟧
  ctx [ var x      ] = lookup x ctx
  ctx [ const n    ] = n
  ctx [ plus t₁ t₂ ] = ctx [ t₁ ] + ctx [ t₂ ]
  ctx [ abs t      ] = λ x → (x ∷ ctx) [ t ]
  ctx [ app t₁ t₂  ] = (ctx [ t₁ ]) (ctx [ t₂ ])
  ctx [ let′ t₁ t₂ ] = (ctx [ t₁ ] ∷ ctx) [ t₂ ]

  ident : ∀ {Γ σ} → Term Γ σ → Term Γ σ
  ident (var x)      = var x
  ident (const x)    = const x
  ident (plus t₁ t₂) = plus (ident t₁) (ident t₂)
  ident (abs t)      = abs (ident t)
  ident (app t₁ t₂)  = app (ident t₁) (ident t₂)
  ident (let′ t₁ t₂) = let′ (ident t₁) (ident t₂)

  identSound : ∀ {Γ σ} → (t : Term Γ σ) → t ≡ ident t
  identSound (var x)      = refl
  identSound (const x)    = refl
  identSound (plus t₁ t₂) = cong₂ plus (identSound t₁) (identSound t₂)
  identSound (abs t)      = cong  abs  (identSound t )
  identSound (app t₁ t₂)  = cong₂ app  (identSound t₁) (identSound t₂)
  identSound (let′ t₁ t₂) = cong₂ let′ (identSound t₁) (identSound t₂)

  postulate ext : ∀ {A B : Set} {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g

  cfold′ : ∀ {Γ σ} → (t : Term Γ σ) → Σ[ t′ ∈ Term Γ σ ] (∀ {c} → c [ t ] ≡ c [ t′ ])
  cfold′ (var v)      = var v , refl
  cfold′ (const n)    = const n , refl
  cfold′ (app t₁ t₂)  = let t₁′ , p = cfold′ t₁; t₂′ , q = cfold′ t₂
                        in app t₁′ t₂′ , cong₂ _$_ p q
  cfold′ (abs t)      = let t′ , p = cfold′ t in abs t′ , ext (λ x → p)
  cfold′ (let′ t₁ t₂) =
    let t₁′ , p = cfold′ t₁; t₂′ , q = cfold′ t₂
    in let′ t₁′ t₂′ ,
       λ {c} → subst (λ ct₁ → ((c [ t₁ ]) ∷ c) [ t₂ ] ≡ (ct₁ ∷ c) [ t₂′ ]) p q
  cfold′ (plus t₁ t₂) with cfold′ t₁ | cfold′ t₂
  ... | const n₁ , p | const n₂ , q = const (n₁ + n₂) , cong₂ _+_ p q
  ... | t₁′      , p | t₂′      , q = plus t₁′ t₂′    , cong₂ _+_ p q

  cfold : ∀ {Γ σ} → Term Γ σ → Term Γ σ
  cfold = proj₁ ∘ cfold′

  cfoldSound : ∀ {Γ σ} → (t : Term Γ σ) → ∀ {c} → c [ t ] ≡ c [ cfold t ]
  cfoldSound = proj₂ ∘ cfold′ 

  insertAt : Type → List Type → ℕ → List Type
  insertAt σ Γ       zero    = σ ∷ Γ
  insertAt σ []      (suc n) = σ ∷ []
  insertAt σ (τ ∷ Γ) (suc n) = τ ∷ insertAt σ Γ n

  liftVar : ∀ {σ Γ} → σ ∈ Γ → ∀ τ → (n : ℕ) → σ ∈ insertAt τ Γ n
  liftVar here        τ zero    = there τ here
  liftVar here        τ (suc n) = here
  liftVar (there σ x) τ zero    = there τ (there σ x)
  liftVar (there σ x) τ (suc n) = there σ (liftVar x τ n)

  lift′ : ∀ {Γ σ τ} → (n : ℕ) → Term Γ τ → Term (insertAt σ Γ n) τ
  lift′ n (var x)      = var (liftVar x _ n)
  lift′ _ (const n)    = const n
  lift′ n (plus t₁ t₂) = plus (lift′ n t₁) (lift′ n t₂)
  lift′ n (abs t)      = abs (lift′ (suc n) t)
  lift′ n (app t₁ t₂)  = app (lift′ n t₁) (lift′ n t₂)
  lift′ n (let′ t₁ t₂) = let′ (lift′ n t₁) (lift′ (suc n) t₂)

  lift : ∀ {Γ σ τ} → Term Γ τ → Term (σ ∷ Γ) τ
  lift = lift′ 0

  unlet : ∀ {Γ σ} → Term Γ σ → ∀ {Δ} → HList (Term Δ) Γ → Term Δ σ
  unlet (var x) s      = lookup x s
  unlet (const n) _    = const n
  unlet (plus t₁ t₂) s = plus (unlet t₁ s) (unlet t₂ s)
  unlet (abs t) s      = abs (unlet t (var here ∷ hmap lift s))
  unlet (app t₁ t₂) s  = app (unlet t₁ s) (unlet t₂ s)
  unlet (let′ t₁ t₂) s = unlet t₂ (unlet t₁ s ∷ s)

  insertAtS : ∀ {σ Γ} →
              (x : ⟦ σ ⟧) → (n : ℕ) → HList ⟦_⟧ Γ → HList ⟦_⟧ (insertAt σ Γ n)
  insertAtS             x zero    s       = x ∷ s
  insertAtS {Γ = []}    x (suc n) s       = x ∷ s
  insertAtS {Γ = σ ∷ Γ} x (suc n) (y ∷ s) = y ∷ insertAtS x n s
