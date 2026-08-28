{-# OPTIONS --postfix-projections --safe #-}

open import Level renaming (_⊔_ to _⊔ℓ_)
open import Data.Product using (proj₁; proj₂; _,_)
open import Relation.Binary.Lattice
  using (DistributiveLattice; IsDistributiveLattice; IsLattice; Supremum; Infimum)
open import Algebra.Ordered using (IsStrongClosureOp)
import Relation.Binary.Reasoning.PartialOrder as PosetReasoning

module Algebra.Ordered.Construction.Closed.DistributiveLattice
  {c} {ℓ₁} {ℓ₂}
  (L : DistributiveLattice c ℓ₁ ℓ₂)
  {𝐂} (𝐂-isStrongClosureOp : IsStrongClosureOp (L .DistributiveLattice._≈_) (L .DistributiveLattice._≤_) 𝐂 (L .DistributiveLattice._∧_))
  where

private
  module L = DistributiveLattice L
  module C = IsStrongClosureOp 𝐂-isStrongClosureOp

open import Algebra.Ordered.Construction.Closed L.poset C.isClosureOp
  public

open Elt
open _≤_
open _≈_

_∧_ : Elt → Elt → Elt
(x ∧ y) .elt = x .elt L.∧ y .elt
(x ∧ y) .closed =
  let open PosetReasoning L.poset in
  L.∧-greatest
    (begin 𝐂 (x .elt L.∧ y .elt) ≤⟨ C.mono (L.x∧y≤x _ _) ⟩
           𝐂 (x .elt)            ≤⟨ x .closed ⟩
           x .elt                ∎)
    (begin 𝐂 (x .elt L.∧ y .elt) ≤⟨ C.mono (L.x∧y≤y _ _) ⟩
           𝐂 (y .elt)            ≤⟨ y .closed ⟩
           y .elt                ∎)

∧-isInfimum : Infimum _≤_ _∧_
∧-isInfimum x y .proj₁ .*≤* = L.x∧y≤x _ _
∧-isInfimum x y .proj₂ .proj₁ .*≤* = L.x∧y≤y _ _
∧-isInfimum x y .proj₂ .proj₂ z z≤x z≤y .*≤* = L.∧-greatest (z≤x .*≤*) (z≤y .*≤*)

_∨_ : Elt → Elt → Elt
(x ∨ y) .elt = 𝐂 (x .elt L.∨ y .elt)
(x ∨ y) .closed = C.closed _

∨-isSupremum : Supremum _≤_ _∨_
∨-isSupremum x y .proj₁ .*≤* = L.trans (L.x≤x∨y _ _) (C.inflate _)
∨-isSupremum x y .proj₂ .proj₁ .*≤* = L.trans (L.y≤x∨y _ _) (C.inflate _)
∨-isSupremum x y .proj₂ .proj₂ z x≤z y≤z .*≤* =
  L.trans (C.mono (L.∨-least (x≤z .*≤*) (y≤z .*≤*))) (z .closed)

isLattice : IsLattice _≈_ _≤_ _∨_ _∧_
isLattice .IsLattice.isPartialOrder = ≤-isPartialOrder
isLattice .IsLattice.supremum = ∨-isSupremum
isLattice .IsLattice.infimum = ∧-isInfimum

open import Algebra.Definitions _≈_ using (_DistributesOverˡ_)

∧-distribˡ-∨ : _∧_ DistributesOverˡ _∨_
∧-distribˡ-∨ x y z .*≈* = L.antisym
  (begin
    x .elt L.∧ 𝐂 (y .elt L.∨ z .elt)
  ≤⟨ C.strength ⟩
    𝐂 (x .elt L.∧ (y .elt L.∨ z .elt))
  ≤⟨ C.mono (L.reflexive (L.∧-distribˡ-∨ (x .elt) (y .elt) (z .elt))) ⟩
    𝐂 ((x .elt L.∧ y .elt) L.∨ (x .elt L.∧ z .elt))
  ∎)
  (L.∧-greatest
    (L.trans (C.mono (L.∨-least (L.x∧y≤x _ _) (L.x∧y≤x _ _))) (x .closed))
    (C.mono (L.∨-least (L.trans (L.x∧y≤y _ _) (L.x≤x∨y _ _))
                       (L.trans (L.x∧y≤y _ _) (L.y≤x∨y _ _)))))
  where open PosetReasoning L.poset

isDistributiveLattice : IsDistributiveLattice _≈_ _≤_ _∨_ _∧_
isDistributiveLattice .IsDistributiveLattice.isLattice = isLattice
isDistributiveLattice .IsDistributiveLattice.∧-distribˡ-∨ = ∧-distribˡ-∨

distributiveLattice : DistributiveLattice (c ⊔ℓ ℓ₂) ℓ₁ ℓ₂
distributiveLattice = record
                       { isDistributiveLattice = isDistributiveLattice
                       }
