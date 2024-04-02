{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level using (suc; _⊔_)
open import Algebra using (_DistributesOver_)
open import Algebra.Ordered using (IsCommutativePomonoid)
open import Algebra.Ordered.Consequences
  using (supremum∧residuated⇒distrib) -- supremum∧residualʳ⇒distribˡ; supremum∧residualˡ⇒distribʳ)
open import Algebra.Ordered.Structures.Duoidal using (IsDuoidal)
open import Algebra.Ordered.Structures.StarAuto using (IsStarAuto)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary using (IsEquivalence; IsPartialOrder)
open import Relation.Binary.Lattice using (IsMeetSemilattice; IsJoinSemilattice)

module BV.Model where

record Model c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Carrier : Set c
    _≈_     : Carrier → Carrier → Set ℓ₁
    _≲_     : Carrier → Carrier → Set ℓ₂

    ¬       : Carrier → Carrier
    I       : Carrier
    J       : Carrier
    _◁_     : Carrier → Carrier → Carrier
    _⊗_     : Carrier → Carrier → Carrier

    ⊗-isCommutativePomonoid : IsCommutativePomonoid _≈_ _≲_ _⊗_ I
    ⊗-isStarAutonomous      : IsStarAuto _≈_ _≲_ ⊗-isCommutativePomonoid ¬
    mix                     : I ≈ ¬ I

    ⊗-◁-isDuoidal           : IsDuoidal _≈_ _≲_ _⊗_ _◁_ I J
    I-eq-J                  : I ≈ J
    ◁-self-dual             : ∀ {x y} → (¬ (x ◁ y)) ≈ ((¬ x) ◁ (¬ y))

  open IsStarAuto ⊗-isStarAutonomous public
  open IsDuoidal ⊗-◁-isDuoidal
    using (◁-cong; ◁-mono; ◁-assoc; ◁-identityʳ; ◁-identityˡ)
    renaming (∙-◁-entropy to ⊗-◁-entropy) public

  sequence : ∀ {w x y z} → ((w ⅋ x) ◁ (y ⅋ z)) ≲ ((w ◁ y) ⅋ (x ◁ z))
  sequence =
    trans (reflexive involution)
          (¬-mono (trans (⊗-mono (reflexive ◁-self-dual) (reflexive ◁-self-dual))
                  (trans (⊗-◁-entropy _ _ _ _)
                  (trans (◁-mono (reflexive involution) (reflexive involution))
                         (reflexive (Eq.sym ◁-self-dual))))))
