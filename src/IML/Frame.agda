{-# OPTIONS --postfix-projections --safe #-}

module IML.Frame {a} (Atom : Set a) where

open import Level using (suc; _⊔_)
open import Algebra.Definitions using (_DistributesOver_)
open import Algebra.Ordered using (Pomagma; IsPomagma)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary using (Rel; Minimum)
open import Relation.Binary.Lattice using (IsDistributiveLattice)
open import IML.Model Atom using (ModalHeytingAlgebra)

-- A frame is a distributive lattice with ⊥
record Frame c ℓ₁ ℓ₂ : Set (a ⊔ suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁
    _≤_     : Rel Carrier ℓ₂

    _∧_     : Carrier → Carrier → Carrier
    _∨_     : Carrier → Carrier → Carrier
    ⊥       : Carrier

    ∘       : Carrier → Carrier
    ∘-mono  : ∀ {x y} → x ≤ y → ∘ x ≤ ∘ y

    isDistributiveLattice : IsDistributiveLattice _≈_ _≤_ _∨_ _∧_

    atom    : Atom → Carrier

  open IsDistributiveLattice isDistributiveLattice public

  ∧-swap : ∀ {x y} → (x ∧ y) ≤ (y ∧ x)
  ∧-swap = ∧-greatest (x∧y≤y _ _) (x∧y≤x _ _)

  ∨-mono : ∀ {x y u v} → x ≤ y → u ≤ v → (x ∨ u) ≤ (y ∨ v)
  ∨-mono x≤y u≤v = ∨-least (trans x≤y (x≤x∨y _ _)) (trans u≤v (y≤x∨y _ _))

  ∧-distrib-∨ : _DistributesOver_ _≤_ _∧_ _∨_
  ∧-distrib-∨ =
    (λ x y z → reflexive (∧-distribˡ-∨ x y z)) ,
    λ x y z → trans ∧-swap (trans (reflexive (∧-distribˡ-∨ x y z))
                                  (∨-mono ∧-swap ∧-swap))

  ∨-pomagma : Pomagma c ℓ₁ ℓ₂
  ∨-pomagma .Pomagma.Carrier = Carrier
  ∨-pomagma .Pomagma._≈_ = _≈_
  ∨-pomagma .Pomagma._≤_ = _≤_
  ∨-pomagma .Pomagma._∙_ = _∨_
  ∨-pomagma .Pomagma.isPomagma .IsPomagma.isPartialOrder = isPartialOrder
  ∨-pomagma .Pomagma.isPomagma .IsPomagma.mono = ∨-mono

module _ {c} {ℓ₁} {ℓ₂} (F : Frame c ℓ₁ ℓ₂) where

  module F = Frame F

  open import Algebra.Ordered.Construction.ZeroPlusIdeal F.∨-pomagma F.⊥

  open Distributive F.infimum F.∧-distrib-∨

  open Modality F.∘ F.∘-mono

  model : ModalHeytingAlgebra (suc (c ⊔ ℓ₂)) (c ⊔ ℓ₂) (c ⊔ ℓ₂)
  model .ModalHeytingAlgebra.Carrier = Ideal
  model .ModalHeytingAlgebra._≈_ = _≈_
  model .ModalHeytingAlgebra._≤_ = _≤_
  model .ModalHeytingAlgebra.⊤ = ⊤
  model .ModalHeytingAlgebra._∧_ = _∧_
  model .ModalHeytingAlgebra._⇒_ = _⇒_
  model .ModalHeytingAlgebra.⊥ = ⊥
  model .ModalHeytingAlgebra._∨_ = _∨_
  model .ModalHeytingAlgebra.isHeytingAlgebra = isHeytingAlgebra
  model .ModalHeytingAlgebra.atom a = η (F.atom a)
  model .ModalHeytingAlgebra.◯ = ◯
  model .ModalHeytingAlgebra.◯-mono = ◯-mono
