{-# OPTIONS --postfix-projections --safe --without-K #-}

module MAV.Model where

open import Level using (suc; _⊔_)
open import Algebra.Ordered using (IsCommutativePomonoid)
open import Algebra.Ordered.Consequences using (supremum∧residualʳ⇒distribˡ)
open import Algebra.Ordered.Structures.Duoidal using (IsDuoidal)
open import Algebra.Ordered.Structures.StarAuto using (IsStarAuto)
open import Data.Product using (proj₁; proj₂)
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
    _⊗_     : Carrier → Carrier → Carrier
    _▷_     : Carrier → Carrier → Carrier
    _&_     : Carrier → Carrier → Carrier

    ⊗-isCommutativePomonoid : IsCommutativePomonoid _≈_ _≲_ _⊗_ I
    ⊗-isStarAutonomous      : IsStarAuto _≈_ _≲_ ⊗-isCommutativePomonoid ¬
    mix                     : I ≈ ¬ I

    &-isMeet                : IsMeetSemilattice _≈_ _≲_ _&_
    ⊗-▷-isDuoidal          : IsDuoidal _≈_ _≲_ _⊗_ _▷_ I J
    I-eq-J                 : I ≈ J
    ▷-self-dual            : ∀ {x y} → (¬ (x ▷ y)) ≈ ((¬ x) ▷ (¬ y))

  open IsStarAuto ⊗-isStarAutonomous public
  open IsMeetSemilattice &-isMeet public
    using ()
    renaming (x∧y≤x to x&y≲x ; x∧y≤y to x&y≲y ; ∧-greatest to &-greatest)
  open IsDuoidal ⊗-▷-isDuoidal
    using (▷-cong; ▷-mono; ▷-assoc; ▷-identityʳ; ▷-identityˡ)
    renaming (∙-▷-entropy to ⊗-▷-entropy) public

  _⊕_ : Carrier → Carrier → Carrier
  x ⊕ y = ¬ (¬ x & ¬ y)

  ⊕-isJoin : IsJoinSemilattice _≈_ _≲_ _⊕_
  ⊕-isJoin .IsJoinSemilattice.isPartialOrder = isPartialOrder
  ⊕-isJoin .IsJoinSemilattice.supremum x y .proj₁ =
    trans (reflexive involution) (¬-mono (x&y≲x _ _))
  ⊕-isJoin .IsJoinSemilattice.supremum x y .proj₂ .proj₁ =
    trans (reflexive involution) (¬-mono (x&y≲y _ _))
  ⊕-isJoin .IsJoinSemilattice.supremum x y .proj₂ .proj₂ z x≲z y≲z =
    trans (¬-mono (&-greatest (¬-mono x≲z) (¬-mono y≲z))) (reflexive (Eq.sym involution))

  open IsJoinSemilattice ⊕-isJoin public
    using ()
    renaming (x≤x∨y to x≲x⊕y ; y≤x∨y to y≲x⊕y; ∨-least to ⊕-least)

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

  sequence : ∀ {w x y z} → ((w ⅋ x) ▷ (y ⅋ z)) ≲ ((w ▷ y) ⅋ (x ▷ z))
  sequence =
    trans (reflexive involution)
          (¬-mono (trans (⊗-mono (reflexive ▷-self-dual) (reflexive ▷-self-dual))
                  (trans (⊗-▷-entropy _ _ _ _)
                  (trans (▷-mono (reflexive involution) (reflexive involution))
                         (reflexive (Eq.sym ▷-self-dual))))))

  ⊕-⊗-distrib : ∀ {x y z} → (x ⊗ (y ⊕ z)) ≲ ((x ⊗ y) ⊕ (x ⊗ z))
  ⊕-⊗-distrib =
   supremum∧residualʳ⇒distribˡ (isPartialOrder .IsPartialOrder.isPreorder)
                                {_⊕_} {_⊗_} {_⊸_}
                                (⊕-isJoin .IsJoinSemilattice.supremum)
                                ⊸-residualʳ _ _ _

  &-⅋-distrib : ∀ {x y z} → ((x ⅋ z) & (y ⅋ z)) ≲ ((x & y) ⅋ z)
  &-⅋-distrib =
    trans (reflexive involution)
          (¬-mono (trans (reflexive (⊗-comm _ _))
                  (trans (⊗-mono refl (¬-mono (&-mono (reflexive (Eq.sym involution))
                                                      (reflexive (Eq.sym involution)))))
                  (trans ⊕-⊗-distrib
                         (¬-mono (&-mono (reflexive (⅋-comm _ _)) (reflexive (⅋-comm _ _))))))))
