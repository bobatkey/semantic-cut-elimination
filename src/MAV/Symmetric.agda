{-# OPTIONS --postfix-projections --safe --without-K #-}

module MAV.Symmetric (Atom : Set) where

open import Level
open import Data.Product using (proj₁; proj₂)
open import Algebra.Ordered
open import Algebra.Ordered.Consequences using (supremum∧residualʳ⇒distribˡ)
open import Algebra.Ordered.Structures.Duoidal using (IsDuoidal)
open import Relation.Binary using (IsEquivalence; IsPartialOrder)
open import Relation.Binary.Construct.Core.Symmetric using (SymCore)
import Relation.Binary.Construct.Core.Symmetric as SymCore
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties as Star
open import Relation.Binary.Lattice using (IsMeetSemilattice; IsJoinSemilattice)

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

record Model (a ℓ₁ ℓ₂ : Level) : Set (suc (a ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Carrier : Set a
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

module Interpretation {a ℓ₁ ℓ₂ : Level} (M : Model a ℓ₁ ℓ₂) (V : Atom → M .Model.Carrier) where

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

  dual-ok : ∀ P → ⟦ `¬ P ⟧ ≈ ¬ ⟦ P ⟧
  dual-ok `I = mix
  dual-ok (`+ x) = Eq.refl
  dual-ok (`- x) = involution
  dual-ok (P `⅋ Q) = Eq.trans (⊗-cong (dual-ok P) (dual-ok Q)) involution
  dual-ok (P `⊗ Q) =
    Eq.trans (⅋-cong (dual-ok P) (dual-ok Q)) (¬-cong (⊗-cong (Eq.sym involution) (Eq.sym involution)))
  dual-ok (P `& Q) = Eq.trans (⊕-cong (dual-ok P) (dual-ok Q)) (¬-cong (&-cong (Eq.sym involution) (Eq.sym involution)))
  dual-ok (P `⊕ Q) = Eq.trans (&-cong (dual-ok P) (dual-ok Q)) involution
  dual-ok (P `▷ Q) = Eq.trans (▷-cong (dual-ok P) (dual-ok Q)) (Eq.sym ▷-self-dual)

  ⟦_⟧step : P ⟶ Q → ⟦ Q ⟧ ≲ ⟦ P ⟧
  ⟦ `axiom P   ⟧step = trans coev (⅋-mono refl (reflexive (Eq.sym (dual-ok P))))
  ⟦ `cut P     ⟧step = trans (⊗-mono refl (reflexive (dual-ok P))) (trans ev (reflexive (Eq.sym mix)))
  ⟦ `tidy      ⟧step = &-greatest refl refl
  ⟦ `switch    ⟧step = linear-distrib
  ⟦ `sequence  ⟧step = sequence
  ⟦ `left      ⟧step = x≲x⊕y _ _
  ⟦ `right     ⟧step = y≲x⊕y _ _
  ⟦ `external  ⟧step = &-⅋-distrib
  ⟦ `medial    ⟧step = &-greatest (▷-mono (x&y≲x _ _) (x&y≲x _ _)) (▷-mono (x&y≲y _ _) (x&y≲y _ _))
  ⟦ S `⟨⊗ Q    ⟧step = ⊗-mono ⟦ S ⟧step refl
  ⟦ P `⊗⟩ S    ⟧step = ⊗-mono refl ⟦ S ⟧step
  ⟦ `⊗-assoc   ⟧step = reflexive (⊗-assoc _ _ _)
  ⟦ `⊗-assoc⁻¹ ⟧step = reflexive (Eq.sym (⊗-assoc _ _ _))
  ⟦ `⊗-comm    ⟧step = reflexive (⊗-comm _ _)
  ⟦ `⊗-unit    ⟧step = reflexive (Eq.sym (⊗-identityʳ _))
  ⟦ `⊗-unit⁻¹  ⟧step = reflexive (⊗-identityʳ _)
  ⟦ S `⟨⅋ Q    ⟧step = ⅋-mono ⟦ S ⟧step refl
  ⟦ P `⅋⟩ S    ⟧step = ⅋-mono refl ⟦ S ⟧step
  ⟦ `⅋-assoc   ⟧step = reflexive (⅋-assoc _ _ _)
  ⟦ `⅋-assoc⁻¹ ⟧step = reflexive (Eq.sym (⅋-assoc _ _ _))
  ⟦ `⅋-comm    ⟧step = reflexive (⅋-comm _ _)
  ⟦ `⅋-unit    ⟧step = reflexive (Eq.trans (Eq.sym (⅋-identityʳ _)) (⅋-cong Eq.refl (Eq.sym mix)))
  ⟦ `⅋-unit⁻¹  ⟧step = reflexive (Eq.trans (⅋-cong Eq.refl mix) (⅋-identityʳ _))
  ⟦ S `⟨▷ Q    ⟧step = ▷-mono ⟦ S ⟧step refl
  ⟦ P `▷⟩ S    ⟧step = ▷-mono refl ⟦ S ⟧step
  ⟦ `▷-assoc   ⟧step = reflexive (▷-assoc _ _ _)
  ⟦ `▷-assoc⁻¹ ⟧step = reflexive (Eq.sym (▷-assoc _ _ _))
  ⟦ `▷-runit   ⟧step = reflexive (Eq.sym (Eq.trans (▷-cong Eq.refl I-eq-J) (▷-identityʳ _)))
  ⟦ `▷-runit⁻¹ ⟧step = reflexive (Eq.trans (▷-cong Eq.refl I-eq-J) (▷-identityʳ _))
  ⟦ `▷-lunit   ⟧step = reflexive (Eq.sym (Eq.trans (▷-cong I-eq-J Eq.refl) (▷-identityˡ _)))
  ⟦ `▷-lunit⁻¹ ⟧step = reflexive (Eq.trans (▷-cong I-eq-J Eq.refl) (▷-identityˡ _))
  ⟦ S `⟨& Q    ⟧step = &-mono ⟦ S ⟧step refl
  ⟦ P `&⟩ S    ⟧step = &-mono refl ⟦ S ⟧step
  ⟦ S `⟨⊕ Q    ⟧step = ⊕-mono ⟦ S ⟧step refl
  ⟦ P `⊕⟩ S    ⟧step = ⊕-mono refl ⟦ S ⟧step

  ⟦_⟧steps : P ⟶* Q → ⟦ Q ⟧ ≲ ⟦ P ⟧
  ⟦ ε     ⟧steps = refl
  ⟦ x ◅ S ⟧steps = trans ⟦ S ⟧steps ⟦ x ⟧step
