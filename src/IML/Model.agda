{-# OPTIONS --postfix-projections --safe #-}

module IML.Model {a} (Atom : Set a) where

open import Level using (suc; _⊔_)
open import Relation.Binary using (Rel)
open import Relation.Binary.Lattice using (IsHeytingAlgebra)

record ModalHeytingAlgebra c ℓ₁ ℓ₂ : Set (a ⊔ suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁
    _≤_     : Rel Carrier ℓ₂

    ⊤       : Carrier
    _∧_     : Carrier → Carrier → Carrier

    _⇒_     : Carrier → Carrier → Carrier

    ⊥       : Carrier
    _∨_     : Carrier → Carrier → Carrier

    isHeytingAlgebra : IsHeytingAlgebra _≈_ _≤_ _∨_ _∧_ _⇒_ ⊤ ⊥

    ◯       : Carrier → Carrier
    ◯-mono  : ∀ {x y} → x ≤ y → ◯ x ≤ ◯ y

    atom    : Atom → Carrier

  open IsHeytingAlgebra isHeytingAlgebra public
