module Common where

module RingSolver where
  open import Data.Nat.Properties
  open SemiringSolver

  :suc : ∀ {n} → Polynomial n → Polynomial n
  :suc x = con 1 :+ x

open RingSolver public using (:suc)
