{-# OPTIONS --postfix-projections --safe #-}

module NDL.Frame2 {a} (Atom : Set a) where

open import Relation.Binary using (Rel; IsPartialOrder; Poset)
open import NDL.Model Atom using (NDLModel)

open import Level using (suc; _⊔_)

record Frame c ℓ₁ ℓ₂ : Set (a ⊔ suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁
    _≤_     : Rel Carrier ℓ₂

    isPartialOrder : IsPartialOrder _≈_ _≤_

    atom : Atom → Carrier → Set (c ⊔ ℓ₂)
    atom-≤ : ∀ {at x y} → x ≤ y → atom at y → atom at x

    -- the “coverage”
    Cover   : Carrier → Set (c ⊔ ℓ₂)
    Cover-≤ : ∀ {x y} → x ≤ y → Cover y → Cover x        -- 'Cover' is a lower set
    Elem    : ∀ x → Cover x → Carrier → Set (c ⊔ ℓ₂)
    Elem-≤  : ∀ {x y z} c (x≤y : x ≤ y) → Elem x (Cover-≤ x≤y c) z → Elem y c z

  open IsPartialOrder isPartialOrder

  poset : Poset c ℓ₁ ℓ₂
  poset = record { isPartialOrder = isPartialOrder }

module _ {c} {ℓ₁} {ℓ₂} (F : Frame c ℓ₁ ℓ₂) where

  module F = Frame F

  import Algebra.Ordered.Construction.LowerSet F.poset as L
  import Algebra.Ordered.Construction.Covered F.poset F.Cover F.Cover-≤ F.Elem F.Elem-≤ as Cl
  import Algebra.Ordered.Construction.Closed L.≤-poset Cl.𝐂-isClosureOp as M
  open M.BoundedLattice L.isBoundedLattice using (isBoundedLattice)

  atom₀ : Atom → L.LowerSet
  atom₀ at .L.LowerSet.ICarrier = F.atom at
  atom₀ at .L.LowerSet.≤-closed = F.atom-≤

  atom : Atom → M.Elt
  atom at = M.η (atom₀ at)

  model : NDLModel (suc (c ⊔ ℓ₂)) (c ⊔ ℓ₂) (c ⊔ ℓ₂)
  model = record
           { isBoundedLattice = isBoundedLattice
           ; atom = atom
           }
