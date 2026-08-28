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

open BoundedLattice H.isBoundedLattice
  using (isLattice; isBoundedLattice; η-⊤)
  renaming (_⊔_ to _∨_; _⊓_ to _∧_; ⟙ to ⊤; 𝟘 to ⊥)
  public

η-∧ : ∀ {X Y} → η X ∧ η Y ≤ η (X H.∧ Y)
η-∧ {X} {Y} .*≤* = begin
    𝐂 X H.∧ 𝐂 Y
  ≤⟨ C.strength ⟩
    𝐂 (𝐂 X H.∧ Y)
  ≤⟨ C.mono (H.∧-greatest (H.x∧y≤y _ _) (H.x∧y≤x _ _)) ⟩
    𝐂 (Y H.∧ 𝐂 X)
  ≤⟨ C.mono C.strength ⟩
    𝐂 (𝐂 (Y H.∧ X))
  ≤⟨ C.mono (C.mono (H.∧-greatest (H.x∧y≤y _ _) (H.x∧y≤x _ _))) ⟩
    𝐂 (𝐂 (X H.∧ Y))
  ≤⟨ C.closed _ ⟩
    𝐂 (X H.∧ Y)
  ∎
  where open PosetReasoning H.poset

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
