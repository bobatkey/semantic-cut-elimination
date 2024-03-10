{-# OPTIONS --postfix-projections --safe --without-K #-}

module MAV.Base (At : Set) where

open import Level
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.Construct.Core.Symmetric using (SymCore)
open import Prelude

open import MAV.Formula At

private
  variable
    a a′ : At
    p p′ : Formula
    q q′ : Formula
    r r′ : Formula
    s s′ : Formula

infix 5 _⟶_

data _⟶_ : Formula → Formula → Set where
  `axiom    : ∀ p → p `⅋ `¬ p ⟶ `I
  `cut      : ∀ p → `I ⟶ p `⊗ `¬ p

  `tidy     : `I `& `I ⟶ `I
  `switch   : (p `⊗ q) `⅋ r ⟶ p `⊗ (q `⅋ r)
  `sequence : (p `▷ q) `⅋ (r `▷ s) ⟶ (p `⅋ r) `▷ (q `⅋ s)
  `left     : p `⊕ q ⟶ p
  `right    : p `⊕ q ⟶ q
  `external : (p `& q) `⅋ r ⟶ (p `⅋ r) `& (q `⅋ r)
  `medial   : (p `▷ q) `& (r `▷ s) ⟶ (p `& r) `▷ (q `& s)

  _⟨`⊗_      : p ⟶ p′ → (q : Formula) → p `⊗ q ⟶ p′ `⊗ q
  _`⊗⟩_      : (p : Formula) → q ⟶ q′ → p `⊗ q ⟶ p `⊗ q′
  `⊗-assoc   : p `⊗ (q `⊗ r) ⟶ (p `⊗ q) `⊗ r
  `⊗-assoc⁻¹ : (p `⊗ q) `⊗ r ⟶ p `⊗ (q `⊗ r)
  `⊗-comm    : p `⊗ q ⟶ q `⊗ p
  `⊗-unit    : p `⊗ `I ⟶ p
  `⊗-unit⁻¹  : p ⟶ p `⊗ `I

  _⟨`⅋_      : p ⟶ p′ → (q : Formula) → p `⅋ q ⟶ p′ `⅋ q
  _`⅋⟩_      : (p : Formula) → q ⟶ q′ → p `⅋ q ⟶ p `⅋ q′
  `⅋-assoc   : p `⅋ (q `⅋ r) ⟶ (p `⅋ q) `⅋ r
  `⅋-assoc⁻¹ : (p `⅋ q) `⅋ r ⟶ p `⅋ (q `⅋ r)
  `⅋-comm    : p `⅋ q ⟶ q `⅋ p
  `⅋-unit    : p `⅋ `I ⟶ p
  `⅋-unit⁻¹  : p ⟶ p `⅋ `I

  _⟨`▷_      : p ⟶ p′ → (q : Formula) → p `▷ q ⟶ p′ `▷ q
  _`▷⟩_      : (p : Formula) → q ⟶ q′ → p `▷ q ⟶ p `▷ q′
  `▷-assoc   : p `▷ (q `▷ r) ⟶ (p `▷ q) `▷ r
  `▷-assoc⁻¹ : (p `▷ q) `▷ r ⟶ p `▷ (q `▷ r)
  `▷-runit   : p `▷ `I ⟶ p
  `▷-runit⁻¹ : p ⟶ p `▷ `I
  `▷-lunit   : `I `▷ p ⟶ p
  `▷-lunit⁻¹ : p ⟶ `I `▷ p

  _⟨`&_      : p ⟶ p′ → (q : Formula) → p `& q ⟶ p′ `& q
  _`&⟩_      : (p : Formula) → q ⟶ q′ → p `& q ⟶ p `& q′

  _⟨`⊕_      : p ⟶ p′ → (q : Formula) → p `⊕ q ⟶ p′ `⊕ q
  _`⊕⟩_      : (p : Formula) → q ⟶ q′ → p `⊕ q ⟶ p `⊕ q′

infix  5 _⟶*_
infixr 6 _∷_

data _⟶*_ : Formula → Formula → Set where
  ε : ∀ {p} → p ⟶* p
  _∷_ : p ⟶ q → q ⟶* r → p ⟶* r

test : Formula
test = (`I `⊕ `I) `▷ (`I `& `I)

test-id : (test `⅋ `¬ test) ⟶* `I
test-id = `axiom test ∷ ε




record Model a b : Set (suc (a ⊔ b)) where
  field
    Carrier : Set a
    _≤_     : Carrier → Carrier → Set b

  field
    ¬       : Carrier → Carrier
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
    ⊗-*aut        : IsStarAuto ≤-isPreorder ⊗-isMonoid ⊗-sym ¬
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

module Interpretation {a b} (M : Model a b) (V : At → M .Model.Carrier) where

  open Model M

  ⟦_⟧ : Formula → Carrier
  ⟦ `I     ⟧ = I
  ⟦ `+ x   ⟧ = V x
  ⟦ `- x   ⟧ = ¬ (V x)
  ⟦ p `⅋ q ⟧ = ⟦ p ⟧ ⅋ ⟦ q ⟧
  ⟦ p `⊗ q ⟧ = ⟦ p ⟧ ⊗ ⟦ q ⟧
  ⟦ p `& q ⟧ = ⟦ p ⟧ & ⟦ q ⟧
  ⟦ p `⊕ q ⟧ = ⟦ p ⟧ ⊕ ⟦ q ⟧
  ⟦ p `▷ q ⟧ = ⟦ p ⟧ ▷ ⟦ q ⟧

  dual-ok : ∀ p → ⟦ `¬ p ⟧ ≃ ¬ ⟦ p ⟧
  dual-ok `I = mix
  dual-ok (`+ x) = ≃-refl
  dual-ok (`- x) = involution
  dual-ok (p `⅋ q) = ≃-trans (⊗-cong (dual-ok p) (dual-ok q)) involution
  dual-ok (p `⊗ q) =
    ≃-trans (⅋-cong (dual-ok p) (dual-ok q)) (¬-cong (⊗-cong (≃-sym involution) (≃-sym involution)))
  dual-ok (p `& q) = ≃-trans (⊕-cong (dual-ok p) (dual-ok q)) (¬-cong (&-cong (≃-sym involution) (≃-sym involution)))
  dual-ok (p `⊕ q) = ≃-trans (&-cong (dual-ok p) (dual-ok q)) involution
  dual-ok (p `▷ q) = ≃-trans (▷-cong (dual-ok p) (dual-ok q)) (≃-sym ▷-self-dual)

  ⟦_⟧step : p ⟶ q → ⟦ q ⟧ ≤ ⟦ p ⟧
  ⟦ `axiom p   ⟧step = trans coev (⅋-mono refl (dual-ok p .proj₂))
  ⟦ `cut p     ⟧step = trans (⊗-mono refl (dual-ok p .proj₁)) (trans ev (mix .proj₂))
  ⟦ `tidy      ⟧step = ⟨ refl , refl ⟩
  ⟦ `switch    ⟧step = linear-distrib
  ⟦ `sequence  ⟧step = sequence
  ⟦ `left      ⟧step = inl
  ⟦ `right     ⟧step = inr
  ⟦ `external  ⟧step = &-⅋-distrib
  ⟦ `medial    ⟧step = ⟨ ▷-mono π₁ π₁ , ▷-mono π₂ π₂ ⟩
  ⟦ s ⟨`⊗ q    ⟧step = ⊗-mono ⟦ s ⟧step refl
  ⟦ p `⊗⟩ s    ⟧step = ⊗-mono refl ⟦ s ⟧step
  ⟦ `⊗-assoc   ⟧step = ⊗-assoc .proj₁
  ⟦ `⊗-assoc⁻¹ ⟧step = ⊗-assoc .proj₂
  ⟦ `⊗-comm    ⟧step = ⊗-sym
  ⟦ `⊗-unit    ⟧step = ⊗-runit .proj₂
  ⟦ `⊗-unit⁻¹  ⟧step = ⊗-runit .proj₁
  ⟦ s ⟨`⅋ q    ⟧step = ⅋-mono ⟦ s ⟧step refl
  ⟦ p `⅋⟩ s    ⟧step = ⅋-mono refl ⟦ s ⟧step
  ⟦ `⅋-assoc   ⟧step = ⅋-assoc .proj₁
  ⟦ `⅋-assoc⁻¹ ⟧step = ⅋-assoc .proj₂
  ⟦ `⅋-comm    ⟧step = ⅋-sym
  ⟦ `⅋-unit    ⟧step = trans (⅋-runit .proj₂) (⅋-mono refl (mix .proj₂))
  ⟦ `⅋-unit⁻¹  ⟧step = trans (⅋-mono refl (mix .proj₁)) (⅋-runit .proj₁)
  ⟦ s ⟨`▷ q    ⟧step = ▷-mono ⟦ s ⟧step refl
  ⟦ p `▷⟩ s    ⟧step = ▷-mono refl ⟦ s ⟧step
  ⟦ `▷-assoc   ⟧step = ▷-assoc .proj₁
  ⟦ `▷-assoc⁻¹ ⟧step = ▷-assoc .proj₂
  ⟦ `▷-runit   ⟧step = trans (▷-runit .proj₂) (▷-mono refl (I-eq-J .proj₂))
  ⟦ `▷-runit⁻¹ ⟧step = trans (▷-mono refl (I-eq-J .proj₁)) (▷-runit .proj₁)
  ⟦ `▷-lunit   ⟧step = trans (▷-lunit .proj₂) (▷-mono (I-eq-J .proj₂) refl)
  ⟦ `▷-lunit⁻¹ ⟧step = trans  (▷-mono (I-eq-J .proj₁) refl) (▷-lunit .proj₁)
  ⟦ s ⟨`& q    ⟧step = &-mono ⟦ s ⟧step refl
  ⟦ p `&⟩ s    ⟧step = &-mono refl ⟦ s ⟧step
  ⟦ s ⟨`⊕ q    ⟧step = ⊕-mono ⟦ s ⟧step refl
  ⟦ p `⊕⟩ s    ⟧step = ⊕-mono refl ⟦ s ⟧step

  ⟦_⟧steps : p ⟶* q → ⟦ q ⟧ ≤ ⟦ p ⟧
  ⟦ ε     ⟧steps = refl
  ⟦ x ∷ s ⟧steps = trans ⟦ s ⟧steps ⟦ x ⟧step
