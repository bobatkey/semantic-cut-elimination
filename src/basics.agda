{-# OPTIONS --postfix-projections --safe --without-K #-}

module basics where

open import Level using (_⊔_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary using (Setoid; IsEquivalence)

module _ {a} {A : Set a} where

  record IsPreorder {b} (_≤_ : A → A → Set b) : Set (a ⊔ b) where
    field
      refl  : ∀ {x} → x ≤ x
      trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z

  SymmetricClosure : ∀ {b} → (A → A → Set b) → (A → A → Set b)
  SymmetricClosure R x y = R x y × R y x

  module _ {b} {_≤_ : A → A → Set b} (≤-isPreorder : IsPreorder _≤_) where

    _≃_ = SymmetricClosure _≤_
    infix 4 _≃_

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

    -- FIXME: closure + join = distributivity

    -- *-autonomous categories and all their structure
    record IsStarAuto {_⊗_ : A → A → A} {ε : A}
                      (⊗-isMonoid : IsMonoid _⊗_ ε)
                      (⊗-sym : ∀ {x y} → (x ⊗ y) ≤ (y ⊗ x))
                      (¬ : A → A) : Set (a ⊔ b) where
      field
        ¬-mono     : ∀ {x y} → x ≤ y → ¬ y ≤ ¬ x
        involution : ∀ {x} → x ≃ ¬ (¬ x)

        *-aut   : ∀ {x y z} → (x ⊗ y) ≤ ¬ z → x ≤ ¬ (y ⊗ z)
        *-aut⁻¹ : ∀ {x y z} → x ≤ ¬ (y ⊗ z) → (x ⊗ y) ≤ ¬ z

      open IsPreorder ≤-isPreorder
      open IsMonoid ⊗-isMonoid

      ¬-cong : ∀ {x y} → x ≃ y → ¬ x ≃ ¬ y
      ¬-cong (ϕ , ψ) .proj₁ = ¬-mono ψ
      ¬-cong (ϕ , ψ) .proj₂ = ¬-mono ϕ

      ⊥ : A
      ⊥ = ¬ ε

      _⅋_ : A → A → A
      x ⅋ y = ¬ (¬ x ⊗ ¬ y)

      ⅋-mono : ∀ {x₁ y₁ x₂ y₂} → x₁ ≤ x₂ → y₁ ≤ y₂ → (x₁ ⅋ y₁) ≤ (x₂ ⅋ y₂)
      ⅋-mono m₁ m₂ = ¬-mono (mono (¬-mono m₁) (¬-mono m₂))

      ⅋-sym : ∀ {x y} → (x ⅋ y) ≤ (y ⅋ x)
      ⅋-sym = ¬-mono ⊗-sym

      ⅋-isMonoid : IsMonoid _⅋_ ⊥
      ⅋-isMonoid .IsMonoid.mono = ⅋-mono
      ⅋-isMonoid .IsMonoid.assoc {x}{y}{z} =
        begin
          (x ⅋ y) ⅋ z            ≡⟨⟩
          ¬ (¬ (x ⅋ y) ⊗ ¬ z)     ≈˘⟨ ¬-cong (cong involution (refl , refl)) ⟩
          ¬ ((¬ x ⊗ ¬ y) ⊗ ¬ z)   ≈⟨ ¬-cong assoc ⟩
          ¬ (¬ x ⊗ (¬ y ⊗ ¬ z))   ≈⟨ ¬-cong (cong (refl , refl) involution) ⟩
          ¬ (¬ x ⊗ ¬ (y ⅋ z))     ≡⟨⟩
          x ⅋ (y ⅋ z)            ∎
        where open import Relation.Binary.Reasoning.Setoid setoidOf
      ⅋-isMonoid .IsMonoid.lunit {x} =
        begin
          ⊥ ⅋ x             ≡⟨⟩
          ¬ (¬ (¬ ε) ⊗ ¬ x)  ≈˘⟨ ¬-cong (cong involution (refl , refl)) ⟩
          ¬ (ε ⊗ ¬ x)        ≈⟨ ¬-cong lunit ⟩
          ¬ (¬ x)            ≈˘⟨ involution ⟩
          x                  ∎
        where open import Relation.Binary.Reasoning.Setoid setoidOf
      ⅋-isMonoid .IsMonoid.runit {x} =
        begin
          x ⅋ ⊥             ≡⟨⟩
          ¬ (¬ x ⊗ ¬ (¬ ε))  ≈˘⟨ ¬-cong (cong (refl , refl) involution) ⟩
          ¬ (¬ x ⊗ ε)        ≈⟨ ¬-cong runit ⟩
          ¬ (¬ x)            ≈˘⟨ involution ⟩
          x                  ∎
        where open import Relation.Binary.Reasoning.Setoid setoidOf

      _⊸_ : A → A → A
      x ⊸ y = ¬ x ⅋ y

      ⊸-isClosure : IsClosure ⊗-isMonoid _⊸_
      ⊸-isClosure .IsClosure.lambda m =
        *-aut (trans (mono refl (involution .proj₂)) (trans m (involution .proj₁)))
      ⊸-isClosure .IsClosure.eval =
        trans (*-aut⁻¹ (¬-mono (mono (involution .proj₁) refl))) (involution .proj₂)

      linear-distrib : ∀ {x y z} → (x ⊗ (y ⅋ z)) ≤ ((x ⊗ y) ⅋ z)
      linear-distrib =
        trans (*-aut (trans (assoc .proj₁)
                     (trans (mono refl (trans (mono (trans (⅋-mono refl (involution .proj₁)) ⅋-sym) refl) (⊸-isClosure .IsClosure.eval)))
                            (involution .proj₁))))
              ⅋-sym