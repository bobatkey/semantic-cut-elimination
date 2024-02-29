{-# OPTIONS --postfix-projections --safe --without-K #-}

module basics where

open import Level
open import Data.Product
open import Relation.Binary using (Setoid; IsEquivalence)

module _ {a} {A : Set a} where

  record IsPreorder {b} (_≤_ : A → A → Set b) : Set (a ⊔ b) where
    field
      refl  : ∀ {x} → x ≤ x
      trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z

  SymmetricClosure : ∀ {b} → (A → A → Set b) → (A → A → Set b)
  SymmetricClosure R x y = R x y × R y x

  module _ {b} {_≤_ : A → A → Set b} (≤-isPreorder : IsPreorder _≤_) where

    module _ where
      open IsPreorder ≤-isPreorder

      isEquivalenceOf : IsEquivalence (SymmetricClosure _≤_)
      isEquivalenceOf .IsEquivalence.refl = refl , refl
      isEquivalenceOf .IsEquivalence.sym (x≤y , y≤x) = y≤x , x≤y
      isEquivalenceOf .IsEquivalence.trans (x≤y , y≤x) (y≤z , z≤y) =
        (trans x≤y y≤z) , (trans z≤y y≤x)

      setoidOf : Setoid a b
      setoidOf .Setoid.Carrier = A
      setoidOf .Setoid._≈_ = SymmetricClosure _≤_
      setoidOf .Setoid.isEquivalence = isEquivalenceOf

    -- Order monoids
    record IsMonoid (_∙_ : A → A → A) (ε : A) : Set (a ⊔ b) where
      _≃_ = SymmetricClosure _≤_

      infix 4 _≃_

      field
        mono  : ∀ {x₁ y₁ x₂ y₂} → x₁ ≤ x₂ → y₁ ≤ y₂ → (x₁ ∙ y₁) ≤ (x₂ ∙ y₂)
        assoc : ∀ {x y z} → (x ∙ y) ∙ z ≃ x ∙ (y ∙ z)
        lunit : ∀ {x} → ε ∙ x ≃ x
        runit : ∀ {x} → x ∙ ε ≃ x

      cong : ∀ {x₁ y₁ x₂ y₂} → x₁ ≃ x₂ → y₁ ≃ y₂ → (x₁ ∙ y₁) ≃ (x₂ ∙ y₂)
      cong eq₁ eq₂ =
        mono (eq₁ .proj₁) (eq₂ .proj₁) ,
        mono (eq₁ .proj₂) (eq₂ .proj₂)

    record IsClosure {_∙_ : A → A → A} {ε : A}
                     (∙-isMonoid : IsMonoid _∙_ ε)
                     (_-∙_ : A → A → A) : Set (a ⊔ b) where
      field
        lambda : ∀ {x y z} → (x ∙ y) ≤ z → x ≤ (y -∙ z)
        eval   : ∀ {x y} → ((x -∙ y) ∙ x) ≤ y

      open IsPreorder ≤-isPreorder
      open IsMonoid ∙-isMonoid

      -∙-mono : ∀ {x₁ y₁ x₂ y₂} → x₂ ≤ x₁ → y₁ ≤ y₂ → (x₁ -∙ y₁) ≤ (x₂ -∙ y₂)
      -∙-mono x₂≤x₁ y₁≤y₂ = lambda (trans (mono refl x₂≤x₁) (trans eval y₁≤y₂))

      lambda⁻¹ : ∀ {x y z} → x ≤ (y -∙ z) → (x ∙ y) ≤ z
      lambda⁻¹ x≤y-z = trans (mono x≤y-z refl) eval

    record IsMeet (_∧_ : A → A → A) : Set (a ⊔ b) where
      field
        π₁ : ∀ {x y} → (x ∧ y) ≤ x
        π₂ : ∀ {x y} → (x ∧ y) ≤ y
        ⟨_,_⟩ : ∀ {x y z} → x ≤ y → x ≤ z → x ≤ (y ∧ z)

      open IsPreorder ≤-isPreorder

      mono : ∀ {x₁ y₁ x₂ y₂} → x₁ ≤ x₂ → y₁ ≤ y₂ → (x₁ ∧ y₁) ≤ (x₂ ∧ y₂)
      mono x₁≤x₂ y₁≤y₂ = ⟨ trans π₁ x₁≤x₂ , trans π₂ y₁≤y₂ ⟩

    record IsJoin (_∨_ : A → A → A) : Set (a ⊔ b) where
      field
        inl : ∀ {x y} → x ≤ (x ∨ y)
        inr : ∀ {x y} → y ≤ (x ∨ y)
        [_,_] : ∀ {x y z} → x ≤ z → y ≤ z → (x ∨ y) ≤ z

      open IsPreorder ≤-isPreorder

      mono : ∀ {x₁ y₁ x₂ y₂} → x₁ ≤ x₂ → y₁ ≤ y₂ → (x₁ ∨ y₁) ≤ (x₂ ∨ y₂)
      mono x₁≤x₂ y₁≤y₂ = [ trans x₁≤x₂ inl , trans y₁≤y₂ inr ]
