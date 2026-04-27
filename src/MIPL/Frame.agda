{-# OPTIONS --postfix-projections --safe #-}

module MIPL.Frame {a} (Atom : Set a) where

open import Level using (suc; _⊔_)
open import Algebra.Definitions using (_DistributesOver_)
open import Algebra.Ordered using (Pomagma; IsPomagma)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary using (Rel; Minimum; IsPartialOrder; Poset)
open import Relation.Binary.Lattice using (IsDistributiveLattice)
open import MIPL.Model Atom using (CCPoset)

-- A frame is a distributive lattice with ⊥
record Frame c ℓ₁ ℓ₂ : Set (a ⊔ suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁
    _≤_     : Rel Carrier ℓ₂

    atom    : Atom → Carrier

    isPartialOrder : IsPartialOrder _≈_ _≤_

  poset : Poset c ℓ₁ ℓ₂
  poset = record { isPartialOrder = isPartialOrder }

module _ {c} {ℓ₁} {ℓ₂} (F : Frame c ℓ₁ ℓ₂) where

  module F = Frame F

  open import Algebra.Ordered.Construction.LowerSet F.poset

  model : CCPoset (suc (c ⊔ ℓ₂)) (c ⊔ ℓ₂) (c ⊔ ℓ₂)
  model .CCPoset.Carrier = LowerSet
  model .CCPoset._≈_ = _≈_
  model .CCPoset._≤_ = _≤_
  model .CCPoset.⊤ = ⊤
  model .CCPoset._∧_ = _∧_
  model .CCPoset._⇒_ = _⇒_
  model .CCPoset.isBoundedMeetSemilattice = ∧-⊤-isBoundedMeetSemilattice
  model .CCPoset.exponential w x y = ⇒-residualˡ-to , ⇒-residualˡ-from
  model .CCPoset.atom a = η (F.atom a)
