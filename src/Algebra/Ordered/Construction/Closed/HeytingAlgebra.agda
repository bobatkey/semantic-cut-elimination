{-# OPTIONS --postfix-projections --safe #-}

open import Level renaming (_⊔_ to _⊔ℓ_)
open import Data.Product using (proj₁; proj₂; _,_)
open import Relation.Binary using (Maximum; Minimum)
open import Relation.Binary.Lattice
  using (HeytingAlgebra; IsHeytingAlgebra; Supremum; Infimum;
         IsLattice; IsBoundedLattice; Exponential)
open import Algebra.Ordered using (IsStrongClosureOp)
import Relation.Binary.Reasoning.PartialOrder as PosetReasoning

module Algebra.Ordered.Construction.Closed.HeytingAlgebra
  {c} {ℓ₁} {ℓ₂}
  (H : HeytingAlgebra c ℓ₁ ℓ₂)
  {𝐂} (𝐂-isStrongClosureOp : IsStrongClosureOp (H .HeytingAlgebra._≈_) (H .HeytingAlgebra._≤_) 𝐂 (H .HeytingAlgebra._∧_))
  where

private
  module H = HeytingAlgebra H
  module C = IsStrongClosureOp 𝐂-isStrongClosureOp

open import Algebra.Ordered.Construction.Closed H.poset C.isClosureOp
  public

open Elt
open _≤_
open _≈_

------------------------------------------------------------------------------
-- Bounded Lattice. FIXME: move this to another file
_∧_ : Elt → Elt → Elt
(x ∧ y) .elt = x .elt H.∧ y .elt
(x ∧ y) .closed =
  let open PosetReasoning H.poset in
  H.∧-greatest
    (begin 𝐂 (x .elt H.∧ y .elt) ≤⟨ C.mono (H.x∧y≤x _ _) ⟩
           𝐂 (x .elt)            ≤⟨ x .closed ⟩
           x .elt                ∎)
    (begin 𝐂 (x .elt H.∧ y .elt) ≤⟨ C.mono (H.x∧y≤y _ _) ⟩
           𝐂 (y .elt)            ≤⟨ y .closed ⟩
           y .elt                ∎)

∧-isInfimum : Infimum _≤_ _∧_
∧-isInfimum x y .proj₁ .*≤* = H.x∧y≤x _ _
∧-isInfimum x y .proj₂ .proj₁ .*≤* = H.x∧y≤y _ _
∧-isInfimum x y .proj₂ .proj₂ z z≤x z≤y .*≤* = H.∧-greatest (z≤x .*≤*) (z≤y .*≤*)

⊤ : Elt
⊤ .elt = H.⊤
⊤ .closed = H.maximum _

⊤-maximum : Maximum _≤_ ⊤
⊤-maximum x .*≤* = H.maximum _

_∨_ : Elt → Elt → Elt
(x ∨ y) .elt = 𝐂 (x .elt H.∨ y .elt)
(x ∨ y) .closed = C.closed _

∨-isSupremum : Supremum _≤_ _∨_
∨-isSupremum x y .proj₁ .*≤* = H.trans (H.x≤x∨y _ _) (C.inflate _)
∨-isSupremum x y .proj₂ .proj₁ .*≤* = H.trans (H.y≤x∨y _ _) (C.inflate _)
∨-isSupremum x y .proj₂ .proj₂ z x≤z y≤z .*≤* =
  H.trans (C.mono (H.∨-least (x≤z .*≤*) (y≤z .*≤*))) (z .closed)

⊥ : Elt
⊥ .elt = 𝐂 H.⊥
⊥ .closed = C.closed _

⊥-minimum : Minimum _≤_ ⊥
⊥-minimum x .*≤* = H.trans (C.mono (H.minimum _)) (x .closed)

isLattice : IsLattice _≈_ _≤_ _∨_ _∧_
isLattice .IsLattice.isPartialOrder = ≤-isPartialOrder
isLattice .IsLattice.supremum = ∨-isSupremum
isLattice .IsLattice.infimum = ∧-isInfimum

isBoundedLattice : IsBoundedLattice _≈_ _≤_ _∨_ _∧_ ⊤ ⊥
isBoundedLattice .IsBoundedLattice.isLattice = isLattice
isBoundedLattice .IsBoundedLattice.maximum = ⊤-maximum
isBoundedLattice .IsBoundedLattice.minimum = ⊥-minimum

------------------------------------------------------------------------------
-- Residual

_⇒_ : Elt → Elt → Elt
(x ⇒ y) .elt = x .elt H.⇨ y .elt
(x ⇒ y) .closed = H.transpose-⇨ (begin
    𝐂 (x .elt H.⇨ y .elt) H.∧ x .elt    ≤⟨ H.∧-greatest (H.x∧y≤y _ _) (H.x∧y≤x _ _) ⟩
    x .elt H.∧ 𝐂 (x .elt H.⇨ y .elt)    ≤⟨ C.strength ⟩
    𝐂 (x .elt H.∧ (x .elt H.⇨ y .elt))  ≤⟨ C.mono (H.∧-greatest (H.x∧y≤y _ _) (H.x∧y≤x _ _)) ⟩
    𝐂 ((x .elt H.⇨ y .elt) H.∧ x .elt)  ≤⟨ C.mono (H.transpose-∧ H.refl) ⟩
    𝐂 (y .elt)                           ≤⟨ y .closed ⟩
    y .elt                               ∎)
  where open PosetReasoning H.poset

⇒-exponential : Exponential _≤_ _∧_ _⇒_
⇒-exponential w x y .proj₁ w∧x≤y .*≤* = H.transpose-⇨ (w∧x≤y .*≤*)
⇒-exponential w x y .proj₂ w≤x⇒y .*≤* = H.transpose-∧ (w≤x⇒y .*≤*)

isHeytingAlgebra : IsHeytingAlgebra _≈_ _≤_ _∨_ _∧_ _⇒_ ⊤ ⊥
isHeytingAlgebra .IsHeytingAlgebra.isBoundedLattice = isBoundedLattice
isHeytingAlgebra .IsHeytingAlgebra.exponential = ⇒-exponential
