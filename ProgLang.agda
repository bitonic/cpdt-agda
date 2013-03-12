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

data _∈_ {A : Set} : A → List A → Set where
  here  : ∀ {x l}               → x ∈ (x ∷ l)
  there : ∀ {x l} → ∀ y → x ∈ l → x ∈ (y ∷ l)

data HList {A : Set} (f : A → Set) : List A → Set where
  []  : HList f []
  _∷_ : ∀ {x xs} → f x → HList f xs → HList f (x ∷ xs)

module FirstOrder where
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

  cfold : ∀ {Γ σ} → Term Γ σ → Term Γ σ
  cfold (var v) = var v
  cfold (const n) = const n
  cfold (app t₁ t₂)  = app (cfold t₁) (cfold t₂)
  cfold (abs t) = abs (cfold t)
  cfold (let′ t₁ t₂) = let′ (cfold t₁) (cfold t₂)
  cfold (plus t₁ t₂) with cfold t₁ | cfold t₂
  ... | const n₁ | const n₂ = const (n₁ + n₂)
  ... | t₁′      | t₂′      = plus t₁′ t₂′

  cfoldSound : ∀ {Γ σ c} → (t : Term Γ σ) → c [ t ] ≡ c [ cfold t ]
  cfoldSound = {!!}
