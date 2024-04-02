{-# OPTIONS --postfix-projections --safe --without-K #-}

module BV.Model where

open import Level using (suc; _⊔_)
open import Algebra using (_DistributesOver_)
open import Algebra.Ordered using (IsCommutativePomonoid)
open import Algebra.Ordered.Consequences using (supremum∧residuated⇒distrib)
open import Algebra.Ordered.Structures.Duoidal
open import Algebra.Ordered.Structures.StarAutonomous
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary using (IsEquivalence; IsPartialOrder)
open import Relation.Binary.Lattice using (IsMeetSemilattice; IsJoinSemilattice)

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

    ⊗-◁-isCommutativeDuoidal : IsCommutativeDuoidal _≈_ _≲_ _⊗_ _◁_ I J
    ⊗-isStarAutonomous       : IsStarAutonomous _≈_ _≲_ _⊗_ I ¬
    mix                      : I ≈ ¬ I

    I-eq-J                   : I ≈ J
    ◁-self-dual              : ∀ {x y} → (¬ (x ◁ y)) ≈ ((¬ x) ◁ (¬ y))

  open IsCommutativeDuoidal ⊗-◁-isCommutativeDuoidal public
    using
      ( isPreorder
      ; isPartialOrder
      ; refl
      ; reflexive
      ; trans
      ; antisym
      ; isEquivalence
      ; setoid
      ; module Eq
      ; ◁-isMagma
      ; ◁-isSemigroup
      ; ◁-isMonoid
      ; ◁-isPromagma
      ; ◁-isProsemigroup
      ; ◁-isPromonoid
      ; ◁-isPomagma
      ; ◁-isPosemigroup
      ; ◁-cong
      ; ◁-congˡ
      ; ◁-congʳ
      ; ◁-mono
      ; ◁-monoˡ
      ; ◁-monoʳ
      ; ◁-assoc
      ; ◁-identity
      ; ◁-identityˡ
      ; ◁-identityʳ
      ; ◁-isPomonoid
      ; ◁-idem-ε
      ; ε≲ι
      )
    renaming
      ( ∙-isMagma               to ⊗-isMagma
      ; ∙-isSemigroup           to ⊗-isSemigroup
      ; ∙-isMonoid              to ⊗-isMonoid
      ; ∙-isPromagma            to ⊗-isPromagma
      ; ∙-isProsemigroup        to ⊗-isProsemigroup
      ; ∙-isPromonoid           to ⊗-isPromonoid
      ; ∙-isPomagma             to ⊗-isPomagma
      ; ∙-isPosemigroup         to ⊗-isPosemigroup
      ; ∙-isPomonoid            to ⊗-isPomonoid
      ; ∙-isCommutativePomonoid to ⊗-isCommutativePomonoid
      ; isDuoidal               to ⊗-◁-isDuoidal
      ; ∙-◁-entropy             to ⊗-◁-entropy
      ; ∙-idem-ι                to ⊗-idem-ι
      ; ∙-cong                  to ⊗-cong
      ; ∙-congˡ                 to ⊗-congˡ
      ; ∙-congʳ                 to ⊗-congʳ
      ; ∙-mono                  to ⊗-mono
      ; ∙-monoˡ                 to ⊗-monoˡ
      ; ∙-monoʳ                 to ⊗-monoʳ
      ; ∙-assoc                 to ⊗-assoc
      ; ∙-identity              to ⊗-identity
      ; ∙-identityˡ             to ⊗-identityˡ
      ; ∙-identityʳ             to ⊗-identityʳ
      ; ∙-comm                  to ⊗-comm
      )

  open IsStarAutonomous ⊗-isStarAutonomous public
    using
      ( ¬-involutive
      ; ¬-mono
      ; ¬-cong
      ; _⅋_
      ; ⅋-mono
      ; ⅋-monoˡ
      ; ⅋-monoʳ
      ; ⅋-cong
      ; ⅋-congˡ
      ; ⅋-congʳ
      ; ⅋-assoc
      ; ⅋-comm
      ; ⅋-identity
      ; ⅋-identityˡ
      ; ⅋-identityʳ
      ; ⊗-⊸-residuated
      ; ev
      ; coev
      ; linear-distrib
      )

  sequence : ∀ {w x y z} → ((w ⅋ x) ◁ (y ⅋ z)) ≲ ((w ◁ y) ⅋ (x ◁ z))
  sequence =
    trans (reflexive (Eq.sym (¬-involutive _)))
          (¬-mono (trans (⊗-mono (reflexive ◁-self-dual) (reflexive ◁-self-dual))
                  (trans (⊗-◁-entropy _ _ _ _)
                  (trans (◁-mono (reflexive (Eq.sym (¬-involutive _))) (reflexive (Eq.sym (¬-involutive _))))
                         (reflexive (Eq.sym ◁-self-dual))))))
