{-# OPTIONS --safe --cubical-compatible #-}

module Function.EquiInhabited where

open import Level using (Level; _⊔_; suc)

private
  variable
    a b : Level

infix 3 _↔_

record _↔_ (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    to   : A → B
    from : B → A
