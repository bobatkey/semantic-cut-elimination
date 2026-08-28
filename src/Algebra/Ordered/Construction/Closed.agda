{-# OPTIONS --postfix-projections --safe #-}

open import Level renaming (_⊔_ to _⊔ℓ_)
open import Algebra using (Associative; Op₂; Commutative; LeftIdentity; RightIdentity)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary
  using (Poset; Rel; IsEquivalence; IsPreorder; IsPartialOrder; Monotonic₂; Maximum; Minimum)
open import Algebra.Ordered
  using (IsClosureOp)
open import Relation.Binary.Lattice.Definitions using (Infimum; Supremum)
open import Relation.Binary.Lattice.Structures using (IsBoundedMeetSemilattice; IsBoundedJoinSemilattice; IsMeetSemilattice; IsJoinSemilattice; IsBoundedLattice)
import Relation.Binary.Reasoning.PartialOrder as PosetReasoning
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

module Algebra.Ordered.Construction.Closed
   {c} {ℓ₁} {ℓ₂}
   (P : Poset c ℓ₁ ℓ₂)
   {𝐂} (𝐂-isClosureOp : IsClosureOp (P .Poset._≈_) (P .Poset._≤_) 𝐂)
{-
   {A : Set c} {_≈_ : Rel A ℓ₁} {_≤_ : Rel A ℓ₂}
   {ε} {_∙_} (∙-ε-isPomonoid : IsCommutativePomonoid _≈_ _≤_ _∙_ ε)
   {𝐂} (𝐂-isStrongClosureOp : IsStrongClosureOp _≈_ _≤_ 𝐂 _∙_)
-}
  where

private
  module P = Poset P
  module C = IsClosureOp 𝐂-isClosureOp

-- private
--   module A = IsCommutativePomonoid ∙-ε-isPomonoid
--   module C = IsStrongClosureOp 𝐂-isStrongClosureOp

record Elt : Set (c ⊔ℓ ℓ₂) where
  field
    elt    : P.Carrier
    closed : 𝐂 elt P.≤ elt
  ≈-closed : 𝐂 elt P.≈ elt
  ≈-closed = P.antisym closed (C.inflate _)
open Elt

record _≈_ (X Y : Elt) : Set ℓ₁ where
  field
    *≈* : X .elt P.≈ Y .elt
open _≈_

≈-isEquivalence : IsEquivalence _≈_
≈-isEquivalence .IsEquivalence.refl .*≈* = P.Eq.refl
≈-isEquivalence .IsEquivalence.sym ϕ .*≈* = P.Eq.sym (ϕ .*≈*)
≈-isEquivalence .IsEquivalence.trans ϕ ψ .*≈* = P.Eq.trans (ϕ .*≈*) (ψ .*≈*)


record _≤_ (X Y : Elt) : Set ℓ₂ where
  field
    *≤* : X .elt P.≤ Y .elt
open _≤_

≤-isPreorder : IsPreorder _≈_ _≤_
≤-isPreorder .IsPreorder.isEquivalence = ≈-isEquivalence
≤-isPreorder .IsPreorder.reflexive ϕ .*≤* = P.reflexive (ϕ .*≈*)
≤-isPreorder .IsPreorder.trans ϕ ψ .*≤* = P.trans (ϕ .*≤*) (ψ .*≤*)

≤-isPartialOrder : IsPartialOrder _≈_ _≤_
≤-isPartialOrder .IsPartialOrder.isPreorder = ≤-isPreorder
≤-isPartialOrder .IsPartialOrder.antisym ϕ ψ .*≈* = P.antisym (ϕ .*≤*) (ψ .*≤*)

infix 4 _≈_ _≤_

poset : Poset (c ⊔ℓ ℓ₂) ℓ₁ ℓ₂
poset .Poset.Carrier = Elt
poset .Poset._≈_ = _≈_
poset .Poset._≤_ = _≤_
poset .Poset.isPartialOrder = ≤-isPartialOrder

------------------------------------------------------------------------------
η : P.Carrier → Elt
η x .elt = 𝐂 x
η x .closed = C.closed _

η-mono : ∀ {x y} → x P.≤ y → η x ≤ η y
η-mono ϕ .*≤* = C.mono ϕ

η-cong : ∀ {x y} → x P.≈ y → η x ≈ η y
η-cong ϕ .*≈* = P.antisym (C.mono (P.reflexive ϕ)) (C.mono (P.reflexive (P.Eq.sym ϕ)))


{-
------------------------------------------------------------------------------
-- Monoidal Structure, given a strength.

-- Alternatively, we can have 𝐂 (x ∙ y) ≤ 𝐂 x ∙ 𝐂 y, which also yields
-- a closed structure.

𝐂-cong : ∀ {x₁ x₂} → x₁ ≈ x₂ → 𝐂 x₁ ≈ 𝐂 x₂
𝐂-cong ϕ = A.antisym (C.mono (A.reflexive ϕ)) (C.mono (A.reflexive (A.Eq.sym ϕ)))

𝐂-strength' : ∀ {x y} → (𝐂 x ∙ y) ≤ 𝐂 (x ∙ y)
𝐂-strength' {x} {y} = begin
    𝐂 x ∙ y   ≈⟨ A.comm _ _ ⟩
    y ∙ 𝐂 x   ≤⟨ C.strength ⟩
    𝐂 (y ∙ x) ≤⟨ C.mono (A.reflexive (A.comm _ _)) ⟩
    𝐂 (x ∙ y) ∎
  where open PosetReasoning (record { isPartialOrder = A.isPartialOrder })

𝐂-monoidal : ∀ {x y} → (𝐂 x ∙ 𝐂 y) ≤ 𝐂 (x ∙ y)
𝐂-monoidal {x} {y} = begin
    𝐂 x ∙ 𝐂 y     ≤⟨ 𝐂-strength' ⟩
    𝐂 (x ∙ 𝐂 y)   ≤⟨ C.mono C.strength ⟩
    𝐂 (𝐂 (x ∙ y)) ≤⟨ C.closed _ ⟩
    𝐂 (x ∙ y)     ∎
  where open PosetReasoning (record { isPartialOrder = A.isPartialOrder })

_⊗_ : Elt → Elt → Elt
(X ⊗ Y) .elt = 𝐂 (X .elt ∙ Y .elt)
(X ⊗ Y) .closed = C.closed _

𝟙 : Elt
𝟙 = η ε

⊗-mono : Monotonic₂ _≤_ _≤_ _≤_ _⊗_
⊗-mono x₁≤x₂ y₁≤y₂ .*≤* = C.mono (A.mono (x₁≤x₂ .*≤*) (y₁≤y₂ .*≤*))

⊗-assoc : Associative _≃_ _⊗_
⊗-assoc x y z .*≃* = A.antisym
  (begin
    𝐂 (𝐂 (x .elt ∙ y .elt) ∙ z .elt)    ≤⟨ C.mono 𝐂-strength' ⟩
    𝐂 (𝐂 ((x .elt ∙ y .elt) ∙ z .elt))  ≤⟨ C.mono (C.mono (A.reflexive (A.assoc _ _ _))) ⟩
    𝐂 (𝐂 (x .elt ∙ (y .elt ∙ z .elt)))  ≤⟨ C.closed _ ⟩
    𝐂 (x .elt ∙ (y .elt ∙ z .elt))       ≤⟨ C.mono (A.mono A.refl (C.inflate _)) ⟩
    𝐂 (x .elt ∙ 𝐂 (y .elt ∙ z .elt))    ∎)
  (begin
    𝐂 (x .elt ∙ 𝐂 (y .elt ∙ z .elt))    ≤⟨ C.mono C.strength ⟩
    𝐂 (𝐂 (x .elt ∙ (y .elt ∙ z .elt)))  ≤⟨ C.closed _ ⟩
    𝐂 (x .elt ∙ (y .elt ∙ z .elt))       ≤⟨ C.mono (A.reflexive (A.Eq.sym (A.assoc _ _ _))) ⟩
    𝐂 ((x .elt ∙ y .elt) ∙ z .elt)       ≤⟨ C.mono (A.mono (C.inflate _) A.refl) ⟩
    𝐂 (𝐂 (x .elt ∙ y .elt) ∙ z .elt)    ∎)
  where open PosetReasoning (record { isPartialOrder = A.isPartialOrder })

{-
⊗-identityˡ : LeftIdentity _≃_ 𝟙 _⊗_
⊗-identityˡ X .*≃* = begin
    𝐂 (𝐂 ε ∙ X .elt) ≈⟨ {!!} ⟩
    𝐂 (ε ∙ X .elt)   ≈⟨ 𝐂-cong (A.identityˡ _) ⟩
    𝐂 (X .elt)        ≈⟨ ≈-closed X ⟩
    X .elt
  ∎
  where open SetoidReasoning (record { isEquivalence = A.isEquivalence })

⊗-identityʳ : RightIdentity _≃_ 𝟙 _⊗_
⊗-identityʳ X .*≃* = begin
    𝐂 (X .elt ∙ 𝐂 ε) ≈⟨ {!!} ⟩
    𝐂 (X .elt ∙ ε)   ≈⟨ 𝐂-cong (A.identityʳ _) ⟩
    𝐂 (X .elt)        ≈⟨ ≈-closed X ⟩
    X .elt
  ∎
  where open SetoidReasoning (record { isEquivalence = A.isEquivalence })
-}

⊗-comm : Commutative _≃_ _⊗_
⊗-comm X Y .*≃* = 𝐂-cong (A.comm _ _)

⊗-isPomagma : IsPomagma _≃_ _≤_ _⊗_
⊗-isPomagma = record { isPartialOrder = ≤-isPartialOrder ; mono = ⊗-mono }

⊗-isPosemigroup : IsPosemigroup _≃_ _≤_ _⊗_
⊗-isPosemigroup = record { isPomagma = ⊗-isPomagma ; assoc = ⊗-assoc }


module _ {_-∙_} (-∙-residual : RightResidual _≤_ _∙_ _-∙_) where

  open import Function.EquiInhabited using (_↔_)
  open _↔_

  _⊸_ : Elt → Elt → Elt
  (X ⊸ Y) .elt = X .elt -∙ Y .elt
  (X ⊸ Y) .closed =
    -∙-residual .to (A.trans C.strength
                    (A.trans (C.mono (-∙-residual .from A.refl))
                             (Y .closed)))

  ⊸-residual : RightResidual _≤_ _⊗_ _⊸_
  ⊸-residual .to ϕ .*≤* = -∙-residual .to (A.trans (C.inflate _) (ϕ .*≤*))
  ⊸-residual {X} {Y} {Z} .from ϕ .*≤* =
    A.trans (C.mono (-∙-residual .from (ϕ .*≤*))) (Z .closed)

------------------------------------------------------------------------------
-- Meets and Joins

module bounded-lattice
    {_∨_ _∧_ : Op₂ A} {⊤ ⊥ : A}
    (isBoundedLattice : IsBoundedLattice _≈_ _≤_ _∨_ _∧_ ⊤ ⊥)
  where

  open IsBoundedLattice isBoundedLattice

  _⊓_ : Elt → Elt → Elt
  (X ⊓ Y) .elt = X .elt ∧ Y .elt
  (X ⊓ Y) .closed =
    ∧-greatest
      (A.trans (C.mono (x∧y≤x _ _)) (X .closed))
      (A.trans (C.mono (x∧y≤y _ _)) (Y .closed))

  x⊓y≤x : ∀ X Y → (X ⊓ Y) ≤ X
  x⊓y≤x X Y .*≤* = x∧y≤x (X .elt) (Y .elt)

  x⊓y≤y : ∀ X Y → (X ⊓ Y) ≤ Y
  x⊓y≤y X Y .*≤* = x∧y≤y (X .elt) (Y .elt)

  ⊓-greatest : ∀ X Y Z → Z ≤ X → Z ≤ Y → Z ≤ (X ⊓ Y)
  ⊓-greatest X Y Z Z≤X Z≤Y .*≤* = ∧-greatest (Z≤X .*≤*) (Z≤Y .*≤*)

  ⊓-infimum : Infimum _≤_ _⊓_
  ⊓-infimum x y = x⊓y≤x x y , x⊓y≤y x y , ⊓-greatest x y

  _⊔_ : Elt → Elt → Elt
  (X ⊔ Y) .elt = 𝐂 (X .elt ∨ Y .elt)
  (X ⊔ Y) .closed = C.closed _

  x≤x⊔y : ∀ X Y → X ≤ (X ⊔ Y)
  x≤x⊔y X Y .*≤* = begin
      X .elt                  ≤⟨ x≤x∨y _ _ ⟩
      X .elt ∨ Y .elt         ≤⟨ C.inflate _ ⟩
      𝐂 (X .elt ∨ Y .elt)    ∎
    where open PosetReasoning (record { isPartialOrder = A.isPartialOrder })

  y≤x⊔y : ∀ X Y → Y ≤ (X ⊔ Y)
  y≤x⊔y X Y .*≤* = begin
      Y .elt                  ≤⟨ y≤x∨y _ _ ⟩
      X .elt ∨ Y .elt         ≤⟨ C.inflate _ ⟩
      𝐂 (X .elt ∨ Y .elt)    ∎
    where open PosetReasoning (record { isPartialOrder = A.isPartialOrder })

  ⊔-least : ∀ x y z → x ≤ z → y ≤ z → (x ⊔ y) ≤ z
  ⊔-least X Y Z X≤Z Y≤Z .*≤* = begin
      𝐂 (X .elt ∨ Y .elt)    ≤⟨ C.mono (∨-least (X≤Z .*≤*) (Y≤Z .*≤*)) ⟩
      𝐂 (Z .elt)             ≤⟨ Z .closed ⟩
      Z .elt                  ∎
    where open PosetReasoning (record { isPartialOrder = A.isPartialOrder })

  ⊔-supremum : Supremum _≤_ _⊔_
  ⊔-supremum X Y = x≤x⊔y X Y , y≤x⊔y X Y , ⊔-least X Y

  -- If we have strength wrt _∧_, then we have distribution

  ⟙ : Elt
  ⟙ .elt = ⊤
  ⟙ .closed = maximum _

  ⟙-maximum : Maximum _≤_ ⟙
  ⟙-maximum x .*≤* = maximum _

  𝟘 : Elt
  𝟘 .elt = 𝐂 ⊥
  𝟘 .closed = C.closed _

  𝟘-minimum : Minimum _≤_ 𝟘
  𝟘-minimum X .*≤* = A.trans (C.mono (minimum _)) (X .closed)

------------------------------------------------------------------------------
-- Unary operators, aka “modalities”

-- Options:
--   1. No interaction with 𝐂
--   2. Absorbing    : 𝐂 (F x) ≤ F x
--   3. Distributing : 𝐂 (F x) ≤ F (𝐂 x)

------------------------------------------------------------------------------
-- Binary operators, beyond modalities

-}
