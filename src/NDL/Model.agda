{-# OPTIONS --postfix-projections --safe #-}

module NDL.Model {a} (Atom : Set a) where

open import Level using (suc; _⊔_)
open import Relation.Binary using (Rel)
open import Relation.Binary.Lattice using (IsBoundedLattice)

record NDLModel c ℓ₁ ℓ₂ : Set (a ⊔ suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁
    _≤_     : Rel Carrier ℓ₂

    ⊤       : Carrier
    _∧_     : Carrier → Carrier → Carrier

    ⊥       : Carrier
    _∨_     : Carrier → Carrier → Carrier

    isBoundedLattice : IsBoundedLattice _≈_ _≤_ _∨_ _∧_ ⊤ ⊥

    atom    : Atom → Carrier

  open IsBoundedLattice isBoundedLattice public
