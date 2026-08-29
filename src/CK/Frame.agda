{-# OPTIONS --postfix-projections --safe #-}

module CK.Frame {a} (Atom : Set a) where

open import Level using (suc; _⊔_)
open import Algebra.Definitions using (_DistributesOver_)
open import Algebra.Ordered using (Pomagma; IsPomagma)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary using (Rel; Minimum; Maximum; Poset)
open import Relation.Binary.Lattice using (IsDistributiveLattice)
open import CK.Model Atom using (ModalHeytingAlgebra)

-- A frame is a distributive lattice with ⊥
record Frame c ℓ₁ ℓ₂ : Set (a ⊔ suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁
    _≤_     : Rel Carrier ℓ₂

    _∧_     : Carrier → Carrier → Carrier
    _∨_     : Carrier → Carrier → Carrier
    ⊤       : Carrier
    ⊥       : Carrier

    □       : Carrier → Carrier
    □-mono  : ∀ {x y} → x ≤ y → □ x ≤ □ y
    □-⊤     : ⊤ ≤ □ ⊤
    □-∧     : ∀ {x y} → (□ x ∧ □ y) ≤ □ (x ∧ y)

    ◇       : Carrier → Carrier
    ◇-mono  : ∀ {x y} → x ≤ y → ◇ x ≤ ◇ y
    K-◇     : ∀ {x y} → (□ x ∧ ◇ y) ≤ ◇ (x ∧ y)

    -- Relationally, without mentioning _∧_ or ⊤
    --
    -- R : Carrier → Carrier → Set ℓ₂
    -- R is op × co -> co
    -- Σ[ y ∈ Carrier ] ∀ x → R x y
    -- ∀ x y z → R x y → R x z → (Σ[ w ∈ Carrier ] R x w × w ≤ x × w ≤ y)

    isDistributiveLattice : IsDistributiveLattice _≈_ _≤_ _∨_ _∧_
    isMaximum             : Maximum _≤_ ⊤

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

  poset : Poset c ℓ₁ ℓ₂
  poset .Poset.Carrier = Carrier
  poset .Poset._≈_ = _≈_
  poset .Poset._≤_ = _≤_
  poset .Poset.isPartialOrder = isPartialOrder

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

  open Modality F.□ F.□-mono
    renaming (◯ to □; ◯-mono to □-mono)

  open Monoidal (record { isMeetSemilattice = F.isMeetSemilattice ; maximum = F.isMaximum }) F.□-⊤ F.□-∧ F.∧-distrib-∨
    renaming (◯-monoidal-unit to □-monoidal-unit; ◯-monoidal to □-monoidal)

  open Modality F.◇ F.◇-mono
    renaming (◯ to ◇; ◯-mono to ◇-mono)

  K-◇ : ∀ I J → (□ I ∧ ◇ J) ≤ ◇ (I ∧ J)
  K-◇ I J = begin
      □ I ∧ ◇ J
    ≡⟨⟩
      α (L□.Ff (U I)) ∧ α (L◇.Ff (U J))
    ≤⟨ α-preserve-∧ .proj₁ ⟩
      α (L□.Ff (U I) L.∧ L◇.Ff (U J))
    ≤⟨ α-mono lem ⟩
      α (L◇.Ff (U I L.∧ U J))
    ≤⟨ α-mono (L◇.Ff-mono U-∧) ⟩
      α (L◇.Ff (U (I ∧ J)))
    ≡⟨⟩
      ◇ (I ∧ J)
    ∎
    where open import Relation.Binary.Reasoning.PartialOrder ≤-poset
          import Algebra.Ordered.Construction.LowerSet
          module L = Algebra.Ordered.Construction.LowerSet F.poset
          module L□ = L.Modality F.□ F.□-mono
          module L◇ = L.Modality F.◇ F.◇-mono

          lem : ∀ {F G} → (L□.Ff F L.∧ L◇.Ff G) L.≤ L◇.Ff (F L.∧ G)
          lem {F} {G} .L.*≤* {x} ((y , x≤□y , Fy) , (z , x≤◇z , Gz)) =
            y F.∧ z , F.trans (F.∧-greatest x≤□y x≤◇z) F.K-◇ ,
            F .L.≤-closed (F.x∧y≤x _ _) Fy ,
            G .L.≤-closed (F.x∧y≤y _ _) Gz

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
  model .ModalHeytingAlgebra.□ = □
  model .ModalHeytingAlgebra.□-mono = □-mono
  model .ModalHeytingAlgebra.□-⊤ = □-monoidal-unit
  model .ModalHeytingAlgebra.□-∧ = □-monoidal
  model .ModalHeytingAlgebra.◇ = ◇
  model .ModalHeytingAlgebra.◇-mono = ◇-mono
  model .ModalHeytingAlgebra.K-◇ = K-◇
