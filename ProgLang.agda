module ProgLang where

import Level
open import Relation.Binary using (Setoid)
open import Data.Nat
open import Data.List hiding ([_]; _++_)
open import Data.Unit
open import Data.Empty
open import Data.String
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

postulate ext : ∀ {A B : Set} {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g

module FirstOrder where
  data _∈_ {A : Set} : A → List A → Set where
    here  : ∀ {x l}               → x ∈ (x ∷ l)
    there : ∀ {x l} → ∀ y → x ∈ l → x ∈ (y ∷ l)

  data HList {A : Set} (F : A → Set) : List A → Set where
    []  : HList F []
    _∷_ : ∀ {x xs} → F x → HList F xs → HList F (x ∷ xs)

  lookup : ∀ {A} {x : A} → ∀ {xs f} → x ∈ xs → HList f xs → f x
  lookup here           (x ∷ _)        = x
  lookup (there x x∈xs) (_∷_ {.x} _ l) = lookup x∈xs l

  hmap : ∀ {A F xs} {G : A → Set} → (∀ {x} → F x → G x) → HList F xs → HList G xs
  hmap f []      = []
  hmap f (x ∷ l) = f x ∷ hmap f l

  hmap-hmap : ∀ {A F xs} {l : HList F xs} {G H : A → Set}
              {f : ∀ {x} → G x → H x} {g : ∀ {x} → F x → G x} →
              hmap f (hmap g l) ≡ hmap (f ∘ g) l
  hmap-hmap {l = []}    = refl
  hmap-hmap {l = x ∷ l} = cong₂ _∷_ refl hmap-hmap

  hmap-≡ : ∀ {A F xs} {l : HList F xs} {G : A → Set}
           {f g : ∀ {x} → F x → G x} → (∀ {x} → (y : F x) → f y ≡ g y) →
           hmap f l ≡ hmap g l
  hmap-≡ {l = []}    _ = refl
  hmap-≡ {l = x ∷ l} p = cong₂ _∷_ (p x) (hmap-≡ p)

  data Term : List Type → Type → Set where
    var   : ∀ {Γ σ}   → σ ∈ Γ                           → Term Γ σ
    const : ∀ {Γ}     → ℕ                               → Term Γ nat
    plus  : ∀ {Γ}     → Term Γ nat     → Term Γ nat     → Term Γ nat
    abs   : ∀ {Γ σ τ} → Term (σ ∷ Γ) τ                  → Term Γ (σ ⇒ τ)
    app   : ∀ {Γ σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ       → Term Γ τ
    let′  : ∀ {Γ σ τ} → Term Γ σ       → Term (σ ∷ Γ) τ → Term Γ τ

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

  liftVarSound : ∀ {τ} (x : ⟦ τ ⟧) {σ Γ} (m : σ ∈ Γ) s n →
                 lookup m s ≡ lookup (liftVar m τ n) (insertAtS x n s)
  liftVarSound x here        _       zero    = refl
  liftVarSound x here        (_ ∷ _) (suc _) = refl
  liftVarSound _ (there _ _) (_ ∷ _) zero    = refl
  liftVarSound x (there y m) (_ ∷ _) (suc n) = liftVarSound x m _ n

  lift′Sound : ∀ {Γ τ} (x : ⟦ τ ⟧) {σ} (t : Term Γ σ) n s →
               s [ t ] ≡ insertAtS x n s [ lift′ n t ]
  lift′Sound x (var v) n s = liftVarSound x v s n
  lift′Sound x (const i) _ _ = refl
  lift′Sound x (plus t₁ t₂) n s =
    cong₂ _+_ (lift′Sound x t₁ n s) (lift′Sound x t₂ n s)
  lift′Sound x (abs t) n s = ext (λ y → lift′Sound x t (suc n) (y ∷ s))
  lift′Sound x (app t₁ t₂) n s = cong₂ _$_ (lift′Sound x t₁ n s) (lift′Sound x t₂ n s)
  lift′Sound x (let′ t₁ t₂) n s =
    subst (λ st₁ → ((s [ t₁ ]) ∷ s) [ t₂ ] ≡
           (st₁ ∷ insertAtS x n s) [ lift′ (suc n) t₂ ])
          (lift′Sound x t₁ n s)
          (lift′Sound x t₂ (suc n) ((s [ t₁ ]) ∷ s))

  liftSound : ∀ {Γ τ} {x : ⟦ τ ⟧} {σ} (t : Term Γ σ) {s} → (x ∷ s) [ lift t ] ≡ s [ t ]
  liftSound t = sym (lift′Sound _ t 0 _)

  unletSound′ : ∀ {Γ σ} (t : Term Γ σ) {Δ} (s : HList (Term Δ) Γ) {s′} →
                s′ [ unlet t s ] ≡ hmap (λ t′ → s′ [ t′ ]) s [ t ]
  unletSound′ (var ()) []
  unletSound′ (var here) (_ ∷ _) = refl
  unletSound′ (var (there _ v)) (_ ∷ s) = unletSound′ (var v) s
  unletSound′ (const n) s = refl
  unletSound′ (plus t₁ t₂) s = cong₂ _+_ (unletSound′ t₁ s) (unletSound′ t₂ s)
  unletSound′ (abs t) s {s′} =
    ext (λ x → trans (unletSound′ t (var here ∷ hmap lift s))
                     (cong (λ l → (x ∷ l) [ t ])
                           (trans hmap-hmap (hmap-≡ (λ t′ → liftSound t′)))))
  unletSound′ (app t₁ t₂) s = cong₂ _$_ (unletSound′ t₁ s) (unletSound′ t₂ s)
  unletSound′ (let′ t₁ t₂) s {s′} =
    subst (λ ht₁ →
           s′ [ unlet t₂ (unlet t₁ s ∷ s) ] ≡ (ht₁ ∷ hmap (λ t′ → s′ [ t′ ]) s) [ t₂ ])
          (unletSound′ t₁ s)
          (unletSound′ t₂ (unlet t₁ s ∷ s))

  unletSound : ∀ {σ} → (t : Term [] σ) → [] [ unlet t [] ] ≡ [] [ t ]
  unletSound t = unletSound′ t []

module HigherOrder where
  data Term (Var : Type → Set) : Type → Set where
    var   : ∀ {σ} → Var σ → Term Var σ
    const : ℕ → Term Var nat
    plus  : Term Var nat → Term Var nat → Term Var nat
    abs   : ∀ {σ τ} → (Var σ → Term Var τ) → Term Var (σ ⇒ τ)
    app   : ∀ {σ τ} → Term Var (σ ⇒ τ) → Term Var σ → Term Var τ
    let′  : ∀ {σ τ} → Term Var σ → (Var σ → Term Var τ) → Term Var τ

  Term₀ : Type → Set₁
  Term₀ σ = ∀ Var → Term Var σ

  countVars : ∀ {σ} → (t : Term (λ _ → ⊤) σ) → ℕ
  countVars (var _) = 1
  countVars (const _) = 0
  countVars (plus t₁ t₂) = countVars t₁ + countVars t₂
  countVars (abs t) = countVars (t tt)
  countVars (app t₁ t₂) = countVars t₁ + countVars t₂
  countVars (let′ t₁ t₂) = countVars t₁ + countVars (t₂ tt)

  countVars₀ : ∀ {σ} → (t : Term₀ σ) → ℕ
  countVars₀ t = countVars (t (λ _ → ⊤))

  pretty : ∀ {σ} → (t : Term (λ _ → String) σ) (x : String) → String
  pretty (var s) _ = s
  pretty (const _) _ = "ℕ"
  pretty (plus t₁ t₂) x = "(" ++ pretty t₁ x ++ " + " ++ pretty t₂ x ++ ")"
  pretty (abs t) x = "(fun " ++ x ++ " => " ++ pretty (t x) (x ++ "'") ++ ")"
  pretty (app t₁ t₂) x = "(" ++ pretty t₁ x ++ " " ++ pretty t₂ x ++ ")"
  pretty (let′ t₁ t₂) x =
    "(let " ++ x ++ " = " ++ pretty t₁ x ++ " in " ++ pretty (t₂ x) (x ++ "'") ++ ")"

  pretty₀ : ∀ {σ} → (t : Term₀ σ) → String
  pretty₀ t = pretty (t (λ _ → String)) "x"

  squash : ∀ {Var σ} → (t : Term (Term Var) σ) → Term Var σ
  squash (var t) = t
  squash (const n) = const n
  squash (plus t₁ t₂) = plus (squash t₁) (squash t₂)
  squash (abs t) = abs (λ x → squash (t (var x)))
  squash (app t₁ t₂) = app (squash t₁) (squash t₂)
  squash (let′ t₁ t₂) = let′ (squash t₁) (λ x → squash (t₂ (var x)))

  Term₁ : (σ τ : Type) → Set₁
  Term₁ σ τ = ∀ Var → Var σ → Term Var τ

  subst′ : ∀ {σ τ} → (t₁ : Term₁ σ τ) (t₂ : Term₀ σ) → Term₀ τ
  subst′ t₁ t₂ Var = squash (t₁ (Term Var) (t₂ Var))

  [_] : ∀ {σ} → Term ⟦_⟧ σ → ⟦ σ ⟧
  [ var v      ] = v
  [ const n    ] = n
  [ plus t₁ t₂ ] = [ t₁ ] + [ t₂ ]
  [ abs t      ] = λ x → [ t x ]
  [ app t₁ t₂  ] = [ t₁ ] [ t₂ ]
  [ let′ t₁ t₂ ] = [ t₂ [ t₁ ] ]

  [_]₀ : ∀ {σ} → Term₀ σ → ⟦ σ ⟧
  [ t ]₀ = [ t ⟦_⟧ ]
