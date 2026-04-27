{-# OPTIONS --postfix-projections --safe #-}

module MIPL.Model {a} (Atom : Set a) where

open import Level using (suc; _⊔_)
open import Data.Product using (_,_)
open import Relation.Binary using (Rel)
open import Relation.Binary.Lattice using (IsBoundedMeetSemilattice; Exponential)

record CCPoset c ℓ₁ ℓ₂ : Set (a ⊔ suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁
    _≤_     : Rel Carrier ℓ₂

    ⊤       : Carrier
    _∧_     : Carrier → Carrier → Carrier

    _⇒_     : Carrier → Carrier → Carrier

    isBoundedMeetSemilattice : IsBoundedMeetSemilattice _≈_ _≤_ _∧_ ⊤
    exponential              : Exponential _≤_ _∧_ _⇒_

    atom    : Atom → Carrier

  open IsBoundedMeetSemilattice isBoundedMeetSemilattice public

  transpose-⇒ : ∀ {w x y} → (w ∧ x) ≤ y → w ≤ (x ⇒ y)
  transpose-⇒ {w} {x} {y} = let pf , _ = exponential w x y in pf

  transpose-∧ : ∀ {w x y} → w ≤ (x ⇒ y) → (w ∧ x) ≤ y
  transpose-∧ {w} {x} {y} = let _ , pf = exponential w x y in pf
