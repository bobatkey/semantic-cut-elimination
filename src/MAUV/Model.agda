{-# OPTIONS --postfix-projections --safe --without-K #-}

module MAUV.Model where

open import Level using (suc; _⊔_)
open import Algebra using (_DistributesOver_)
open import Algebra.Ordered using (IsCommutativePomonoid)
open import Algebra.Ordered.Consequences using (supremum∧residuated⇒distrib)
open import Algebra.Ordered.Structures.Duoidal
open import Algebra.Ordered.Structures.StarAutonomous
open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (Equivalence)
open import Relation.Binary using (IsEquivalence; IsPartialOrder; Minimum)
open import Relation.Binary.Lattice using (IsBoundedMeetSemilattice; IsBoundedJoinSemilattice)

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
    _&_     : Carrier → Carrier → Carrier
    ⊤       : Carrier

    ⊗-◁-isCommutativeDuoidal : IsCommutativeDuoidal _≈_ _≲_ _⊗_ _◁_ I J
    ⊗-isStarAutonomous       : IsStarAutonomous _≈_ _≲_ _⊗_ I ¬
    &-⊤-isBoundedMeet        : IsBoundedMeetSemilattice _≈_ _≲_ _&_ ⊤

    I-eq-J                   : I ≈ J
    ◁-self-dual              : ∀ {x y} → (¬ (x ◁ y)) ≈ ((¬ x) ◁ (¬ y))
    mix                      : I ≈ ¬ I

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

  open IsBoundedMeetSemilattice &-⊤-isBoundedMeet public
    using
      ( infimum
      )
    renaming
      ( x∧y≤x      to x&y≲x
      ; x∧y≤y      to x&y≲y
      ; ∧-greatest to &-greatest
      ; maximum    to ⊤-maximum
      )

  _⊕_ : Carrier → Carrier → Carrier
  x ⊕ y = ¬ (¬ x & ¬ y)

  𝟘 : Carrier
  𝟘 = ¬ ⊤

  x≲x⊕y : ∀ x y → x ≲ (x ⊕ y)
  x≲x⊕y x y =
    trans (reflexive (Eq.sym (¬-involutive _))) (¬-mono (x&y≲x _ _))

  y≲x⊕y : ∀ x y → y ≲ (x ⊕ y)
  y≲x⊕y x y =
    trans (reflexive (Eq.sym (¬-involutive _))) (¬-mono (x&y≲y _ _))

  ⊕-least : ∀ {x y z} → x ≲ z → y ≲ z → (x ⊕ y) ≲ z
  ⊕-least x≲z y≲z =
    trans (¬-mono (&-greatest (¬-mono x≲z) (¬-mono y≲z))) (reflexive (¬-involutive _))

  𝟘-minimum : Minimum _≲_ 𝟘
  𝟘-minimum x = trans (¬-mono (⊤-maximum (¬ x))) (reflexive (¬-involutive _))

  ⊕-𝟘-isBoundedJoinSemilattice : IsBoundedJoinSemilattice _≈_ _≲_ _⊕_ 𝟘
  ⊕-𝟘-isBoundedJoinSemilattice = record
    { isJoinSemilattice = record
      { isPartialOrder = isPartialOrder
      ; supremum       = λ x y →  x≲x⊕y x y , y≲x⊕y x y , λ z → ⊕-least
      }
    ; minimum = 𝟘-minimum
    }

  open IsBoundedJoinSemilattice ⊕-𝟘-isBoundedJoinSemilattice
    using
      ( supremum
      )

  ⊕-mono : ∀ {x₁ y₁ x₂ y₂} → x₁ ≲ x₂ → y₁ ≲ y₂ → (x₁ ⊕ y₁) ≲ (x₂ ⊕ y₂)
  ⊕-mono x₁≲x₂ y₁≲y₂ = ⊕-least (trans x₁≲x₂ (x≲x⊕y _ _)) (trans y₁≲y₂ (y≲x⊕y _ _))

  &-mono : ∀ {x₁ y₁ x₂ y₂} → x₁ ≲ x₂ → y₁ ≲ y₂ → (x₁ & y₁) ≲ (x₂ & y₂)
  &-mono x₁≲x₂ y₁≲y₂ = &-greatest (trans (x&y≲x _ _) x₁≲x₂) (trans (x&y≲y _ _) y₁≲y₂)

  ⊕-cong : ∀ {x₁ y₁ x₂ y₂} → x₁ ≈ x₂ → y₁ ≈ y₂ → (x₁ ⊕ y₁) ≈ (x₂ ⊕ y₂)
  ⊕-cong x₁≈x₂ y₁≈y₂ =
    antisym (⊕-mono (reflexive x₁≈x₂) (reflexive y₁≈y₂)) (⊕-mono (reflexive (Eq.sym x₁≈x₂)) (reflexive (Eq.sym y₁≈y₂)))

  &-cong : ∀ {x₁ y₁ x₂ y₂} → x₁ ≈ x₂ → y₁ ≈ y₂ → (x₁ & y₁) ≈ (x₂ & y₂)
  &-cong x₁≈x₂ y₁≈y₂ =
    antisym (&-mono (reflexive x₁≈x₂) (reflexive y₁≈y₂)) (&-mono (reflexive (Eq.sym x₁≈x₂)) (reflexive (Eq.sym y₁≈y₂)))

  sequence : ∀ {w x y z} → ((w ⅋ x) ◁ (y ⅋ z)) ≲ ((w ◁ y) ⅋ (x ◁ z))
  sequence =
    trans (reflexive (Eq.sym (¬-involutive _)))
          (¬-mono (trans (⊗-mono (reflexive ◁-self-dual) (reflexive ◁-self-dual))
                  (trans (⊗-◁-entropy _ _ _ _)
                  (trans (◁-mono (reflexive (Eq.sym (¬-involutive _))) (reflexive (Eq.sym (¬-involutive _))))
                         (reflexive (Eq.sym ◁-self-dual))))))

  ⊥-⊗-distrib : ∀ {x} → (𝟘 ⊗ x) ≲ 𝟘
  ⊥-⊗-distrib = ⊗-⊸-residuated .proj₁ .Equivalence.from (𝟘-minimum _)

  ⊕-⊗-distrib : _DistributesOver_ _≲_ _⊗_ _⊕_
  ⊕-⊗-distrib =
    supremum∧residuated⇒distrib isPreorder supremum ⊗-⊸-residuated

  ⊤-⅋-distrib : ∀ {x} → ⊤ ≲ (⊤ ⅋ x)
  ⊤-⅋-distrib = trans (reflexive (Eq.sym (¬-involutive _))) (¬-mono ⊥-⊗-distrib)

  &-⅋-distrib : ∀ {x y z} → ((x ⅋ z) & (y ⅋ z)) ≲ ((x & y) ⅋ z)
  &-⅋-distrib =
    trans (reflexive (Eq.sym (¬-involutive _)))
          (¬-mono (trans (⊗-mono (¬-mono (&-mono (reflexive (¬-involutive _))
                                                 (reflexive (¬-involutive _))))
                                 refl)
                         (⊕-⊗-distrib .proj₂ _ _ _)))
