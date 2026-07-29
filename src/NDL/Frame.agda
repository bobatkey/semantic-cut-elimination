{-# OPTIONS --postfix-projections --safe #-}

module NDL.Frame {a} (Atom : Set a) where

open import Relation.Binary using (Rel)
open import Algebra.Ordered using (Pomagma; IsPomagma)
open import NDL.Model Atom using (NDLModel)

open import Level using (suc; _⊔_)

record Frame c ℓ₁ ℓ₂ : Set (a ⊔ suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁
    _≤_     : Rel Carrier ℓ₂

    _∨_     : Carrier → Carrier → Carrier
    ⊥       : Carrier

    isPomagma : IsPomagma _≈_ _≤_ _∨_

    atom    : Atom → Carrier

  open IsPomagma isPomagma

  ∨-pomagma : Pomagma c ℓ₁ ℓ₂
  ∨-pomagma = record { isPomagma = isPomagma }

module _ {c} {ℓ₁} {ℓ₂} (F : Frame c ℓ₁ ℓ₂) where

  module F = Frame F

  open import Algebra.Ordered.Construction.ZeroPlusIdeal F.∨-pomagma F.⊥

  model : NDLModel (suc (c ⊔ ℓ₂)) (c ⊔ ℓ₂) (c ⊔ ℓ₂)
  model .NDLModel.Carrier = Ideal
  model .NDLModel._≈_ = _≈_
  model .NDLModel._≤_ = _≤_
  model .NDLModel.⊤ = ⊤
  model .NDLModel._∧_ = _∧_
  model .NDLModel.⊥ = ⊥
  model .NDLModel._∨_ = _∨_
  model .NDLModel.isBoundedLattice = isBoundedLattice
  model .NDLModel.atom a = η (F.atom a)
