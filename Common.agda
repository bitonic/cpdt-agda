module Common where

open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)

infixr 2 _∧_

_∧_ : Set → Set → Set
_∧_ = _×_

infixr 1 _∨_

_∨_ : Set → Set → Set
_∨_ = _⊎_

module RingSolver where
  open import Data.Nat.Properties
  open SemiringSolver

  :suc : ∀ {n} → Polynomial n → Polynomial n
  :suc x = con 1 :+ x

open RingSolver public using (:suc)
