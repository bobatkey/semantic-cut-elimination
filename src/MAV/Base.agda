{-# OPTIONS --postfix-projections --safe --without-K #-}

module MAV.Base (Atom : Set) where

open import Level
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.Construct.Core.Symmetric using (SymCore)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)
import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties as Star
      
open import Prelude

open import MAV.Formula Atom

private
  variable
    A A′ : Atom
    P P′ : Formula
    Q Q′ : Formula
    R R′ : Formula
    S S′ : Formula

infix 5 _⟶_

data _⟶_ : Formula → Formula → Set where
  `axiom    : ∀ P → P `⅋ `¬ P ⟶ `I
  `cut      : ∀ P → `I ⟶ P `⊗ `¬ P

  `tidy     : `I `& `I ⟶ `I
  `switch   : (P `⊗ Q) `⅋ R ⟶ P `⊗ (Q `⅋ R)
  `sequence : (P `▷ Q) `⅋ (R `▷ S) ⟶ (P `⅋ R) `▷ (Q `⅋ S)
  `left     : P `⊕ Q ⟶ P
  `right    : P `⊕ Q ⟶ Q
  `external : (P `& Q) `⅋ R ⟶ (P `⅋ R) `& (Q `⅋ R)
  `medial   : (P `▷ Q) `& (R `▷ S) ⟶ (P `& R) `▷ (Q `& S)

  _`⟨⊗_      : P ⟶ P′ → (Q : Formula) → P `⊗ Q ⟶ P′ `⊗ Q
  _`⊗⟩_      : (P : Formula) → Q ⟶ Q′ → P `⊗ Q ⟶ P `⊗ Q′
  `⊗-assoc   : P `⊗ (Q `⊗ R) ⟶ (P `⊗ Q) `⊗ R
  `⊗-assoc⁻¹ : (P `⊗ Q) `⊗ R ⟶ P `⊗ (Q `⊗ R)
  `⊗-comm    : P `⊗ Q ⟶ Q `⊗ P
  `⊗-unit    : P `⊗ `I ⟶ P
  `⊗-unit⁻¹  : P ⟶ P `⊗ `I

  _`⟨⅋_      : P ⟶ P′ → (Q : Formula) → P `⅋ Q ⟶ P′ `⅋ Q
  _`⅋⟩_      : (P : Formula) → Q ⟶ Q′ → P `⅋ Q ⟶ P `⅋ Q′
  `⅋-assoc   : P `⅋ (Q `⅋ R) ⟶ (P `⅋ Q) `⅋ R
  `⅋-assoc⁻¹ : (P `⅋ Q) `⅋ R ⟶ P `⅋ (Q `⅋ R)
  `⅋-comm    : P `⅋ Q ⟶ Q `⅋ P
  `⅋-unit    : P `⅋ `I ⟶ P
  `⅋-unit⁻¹  : P ⟶ P `⅋ `I

  _`⟨▷_      : P ⟶ P′ → (Q : Formula) → P `▷ Q ⟶ P′ `▷ Q
  _`▷⟩_      : (P : Formula) → Q ⟶ Q′ → P `▷ Q ⟶ P `▷ Q′
  `▷-assoc   : P `▷ (Q `▷ R) ⟶ (P `▷ Q) `▷ R
  `▷-assoc⁻¹ : (P `▷ Q) `▷ R ⟶ P `▷ (Q `▷ R)
  `▷-runit   : P `▷ `I ⟶ P
  `▷-runit⁻¹ : P ⟶ P `▷ `I
  `▷-lunit   : `I `▷ P ⟶ P
  `▷-lunit⁻¹ : P ⟶ `I `▷ P

  _`⟨&_      : P ⟶ P′ → (Q : Formula) → P `& Q ⟶ P′ `& Q
  _`&⟩_      : (P : Formula) → Q ⟶ Q′ → P `& Q ⟶ P `& Q′

  _`⟨⊕_      : P ⟶ P′ → (Q : Formula) → P `⊕ Q ⟶ P′ `⊕ Q
  _`⊕⟩_      : (P : Formula) → Q ⟶ Q′ → P `⊕ Q ⟶ P `⊕ Q′

infix  5 _⟶*_

_⟶*_ : Formula → Formula → Set
_⟶*_ = Star _⟶_

test : Formula
test = (`I `⊕ `I) `▷ (`I `& `I)

test-id : (test `⅋ `¬ test) ⟶* `I
test-id = `axiom test ◅ ε

record Model (a ℓ : Level) : Set (suc (a ⊔ ℓ)) where
  field
    Carrier : Set a
    _≤_     : Carrier → Carrier → Set ℓ

  infixr 15 ¬_
  infixr 10 _⊗_
  infixr 10 _&_
  infixr 10 _▷_
  
  field
    ¬_      : Carrier → Carrier
    I       : Carrier
    J       : Carrier
    _⊗_     : Carrier → Carrier → Carrier
    _▷_     : Carrier → Carrier → Carrier
    _&_     : Carrier → Carrier → Carrier

  field
    ≤-isPreorder  : IsPreorder _≤_

  open IsPreorder ≤-isPreorder public
  
  field
    ⊗-isMonoid    : IsMonoid ≤-isPreorder _⊗_ I
    ⊗-sym         : ∀ {x y} → (x ⊗ y) ≤ (y ⊗ x)
    ⊗-*aut        : IsStarAuto ≤-isPreorder ⊗-isMonoid ⊗-sym ¬_
    mix           : I ≃ (¬ I)

    &-isMeet      : IsMeet ≤-isPreorder _&_

    ▷-isMonoid    : IsMonoid ≤-isPreorder _▷_ J
    I-eq-J        : I ≃ J
    ▷-self-dual   : ∀ {x y} → (¬ (x ▷ y)) ≃ ((¬ x) ▷ (¬ y))
    ⊗-▷-isDuoidal : IsDuoidal ≤-isPreorder ⊗-isMonoid ▷-isMonoid

  open IsEquivalence ≃-isEquivalence public
    renaming (refl to ≃-refl; sym to ≃-sym; trans to ≃-trans)
  open IsMonoid ⊗-isMonoid public
    renaming (mono to ⊗-mono; assoc to ⊗-assoc; lunit to ⊗-lunit; runit to ⊗-runit; cong to ⊗-cong)
  open IsMonoid ▷-isMonoid public
    renaming (mono to ▷-mono; assoc to ▷-assoc; lunit to ▷-lunit; runit to ▷-runit; cong to ▷-cong)
  open IsStarAuto ⊗-*aut public
  open IsMeet &-isMeet public
    renaming (mono to &-mono; cong to &-cong)
    hiding (assoc; idem)
  open IsDuoidal ⊗-▷-isDuoidal

  -- Some derived facts, used in the interpretation
  _⊕_ : Carrier → Carrier → Carrier
  x ⊕ y = ¬ (¬ x & ¬ y)

  ⊕-isJoin : IsJoin ≤-isPreorder _⊕_
  ⊕-isJoin .IsJoin.inl = trans (involution .proj₁) (¬-mono π₁)
  ⊕-isJoin .IsJoin.inr = trans (involution .proj₁) (¬-mono π₂)
  ⊕-isJoin .IsJoin.[_,_] m₁ m₂ = trans (¬-mono ⟨ ¬-mono m₁ , ¬-mono m₂ ⟩) (involution .proj₂)

  open IsJoin ⊕-isJoin public
    renaming (mono to ⊕-mono; cong to ⊕-cong)
    hiding (assoc; idem)

  sequence : ∀ {w x y z} → ((w ⅋ x) ▷ (y ⅋ z)) ≤ ((w ▷ y) ⅋ (x ▷ z))
  sequence =
    trans (involution .proj₁)
          (¬-mono (trans (⊗-mono (▷-self-dual .proj₁) (▷-self-dual .proj₁))
                  (trans exchange
                  (trans (▷-mono (involution .proj₁) (involution .proj₁))
                  (▷-self-dual .proj₂)))))

  ⊕-⊗-distrib : ∀ {x y z} → (x ⊗ (y ⊕ z)) ≤ ((x ⊗ y) ⊕ (x ⊗ z))
  ⊕-⊗-distrib = ∙-∨-distrib ≤-isPreorder ⊗-isMonoid ⊗-sym ⊸-isClosure ⊕-isJoin

  &-⅋-distrib : ∀ {x y z} → ((x ⅋ z) & (y ⅋ z)) ≤ ((x & y) ⅋ z)
  &-⅋-distrib =
    trans (involution .proj₁)
          (¬-mono (trans ⊗-sym
                  (trans (⊗-mono refl (¬-mono (&-mono (involution .proj₂) (involution .proj₂))))
                  (trans ⊕-⊗-distrib
                         (¬-mono (&-mono ⅋-sym ⅋-sym))))))

module Interpretation {a ℓ : Level} (M : Model a ℓ) (V : Atom → M .Model.Carrier) where

  open Model M

  ⟦_⟧ : Formula → Carrier
  ⟦ `I     ⟧ = I
  ⟦ `+ x   ⟧ = V x
  ⟦ `- x   ⟧ = ¬ (V x)
  ⟦ P `⅋ Q ⟧ = ⟦ P ⟧ ⅋ ⟦ Q ⟧
  ⟦ P `⊗ Q ⟧ = ⟦ P ⟧ ⊗ ⟦ Q ⟧
  ⟦ P `& Q ⟧ = ⟦ P ⟧ & ⟦ Q ⟧
  ⟦ P `⊕ Q ⟧ = ⟦ P ⟧ ⊕ ⟦ Q ⟧
  ⟦ P `▷ Q ⟧ = ⟦ P ⟧ ▷ ⟦ Q ⟧

  dual-ok : ∀ P → ⟦ `¬ P ⟧ ≃ ¬ ⟦ P ⟧
  dual-ok `I = mix
  dual-ok (`+ x) = ≃-refl
  dual-ok (`- x) = involution
  dual-ok (P `⅋ Q) = ≃-trans (⊗-cong (dual-ok P) (dual-ok Q)) involution
  dual-ok (P `⊗ Q) =
    ≃-trans (⅋-cong (dual-ok P) (dual-ok Q)) (¬-cong (⊗-cong (≃-sym involution) (≃-sym involution)))
  dual-ok (P `& Q) = ≃-trans (⊕-cong (dual-ok P) (dual-ok Q)) (¬-cong (&-cong (≃-sym involution) (≃-sym involution)))
  dual-ok (P `⊕ Q) = ≃-trans (&-cong (dual-ok P) (dual-ok Q)) involution
  dual-ok (P `▷ Q) = ≃-trans (▷-cong (dual-ok P) (dual-ok Q)) (≃-sym ▷-self-dual)

  ⟦_⟧step : P ⟶ Q → ⟦ Q ⟧ ≤ ⟦ P ⟧
  ⟦ `axiom P   ⟧step = trans coev (⅋-mono refl (dual-ok P .proj₂))
  ⟦ `cut P     ⟧step = trans (⊗-mono refl (dual-ok P .proj₁)) (trans ev (mix .proj₂))
  ⟦ `tidy      ⟧step = ⟨ refl , refl ⟩
  ⟦ `switch    ⟧step = linear-distrib
  ⟦ `sequence  ⟧step = sequence
  ⟦ `left      ⟧step = inl
  ⟦ `right     ⟧step = inr
  ⟦ `external  ⟧step = &-⅋-distrib
  ⟦ `medial    ⟧step = ⟨ ▷-mono π₁ π₁ , ▷-mono π₂ π₂ ⟩
  ⟦ S `⟨⊗ Q    ⟧step = ⊗-mono ⟦ S ⟧step refl
  ⟦ P `⊗⟩ S    ⟧step = ⊗-mono refl ⟦ S ⟧step
  ⟦ `⊗-assoc   ⟧step = ⊗-assoc .proj₁
  ⟦ `⊗-assoc⁻¹ ⟧step = ⊗-assoc .proj₂
  ⟦ `⊗-comm    ⟧step = ⊗-sym
  ⟦ `⊗-unit    ⟧step = ⊗-runit .proj₂
  ⟦ `⊗-unit⁻¹  ⟧step = ⊗-runit .proj₁
  ⟦ S `⟨⅋ Q    ⟧step = ⅋-mono ⟦ S ⟧step refl
  ⟦ P `⅋⟩ S    ⟧step = ⅋-mono refl ⟦ S ⟧step
  ⟦ `⅋-assoc   ⟧step = ⅋-assoc .proj₁
  ⟦ `⅋-assoc⁻¹ ⟧step = ⅋-assoc .proj₂
  ⟦ `⅋-comm    ⟧step = ⅋-sym
  ⟦ `⅋-unit    ⟧step = trans (⅋-runit .proj₂) (⅋-mono refl (mix .proj₂))
  ⟦ `⅋-unit⁻¹  ⟧step = trans (⅋-mono refl (mix .proj₁)) (⅋-runit .proj₁)
  ⟦ S `⟨▷ Q    ⟧step = ▷-mono ⟦ S ⟧step refl
  ⟦ P `▷⟩ S    ⟧step = ▷-mono refl ⟦ S ⟧step
  ⟦ `▷-assoc   ⟧step = ▷-assoc .proj₁
  ⟦ `▷-assoc⁻¹ ⟧step = ▷-assoc .proj₂
  ⟦ `▷-runit   ⟧step = trans (▷-runit .proj₂) (▷-mono refl (I-eq-J .proj₂))
  ⟦ `▷-runit⁻¹ ⟧step = trans (▷-mono refl (I-eq-J .proj₁)) (▷-runit .proj₁)
  ⟦ `▷-lunit   ⟧step = trans (▷-lunit .proj₂) (▷-mono (I-eq-J .proj₂) refl)
  ⟦ `▷-lunit⁻¹ ⟧step = trans  (▷-mono (I-eq-J .proj₁) refl) (▷-lunit .proj₁)
  ⟦ S `⟨& Q    ⟧step = &-mono ⟦ S ⟧step refl
  ⟦ P `&⟩ S    ⟧step = &-mono refl ⟦ S ⟧step
  ⟦ S `⟨⊕ Q    ⟧step = ⊕-mono ⟦ S ⟧step refl
  ⟦ P `⊕⟩ S    ⟧step = ⊕-mono refl ⟦ S ⟧step

  ⟦_⟧steps : P ⟶* Q → ⟦ Q ⟧ ≤ ⟦ P ⟧
  ⟦ ε     ⟧steps = refl
  ⟦ x ◅ S ⟧steps = trans ⟦ S ⟧steps ⟦ x ⟧step
