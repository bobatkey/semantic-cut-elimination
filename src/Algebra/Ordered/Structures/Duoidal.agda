------------------------------------------------------------------------
-- The Agda standard library
--
-- Ordered algebraic structures (not packed up with sets, orders,
-- operations, etc.)
------------------------------------------------------------------------

-- The contents of this module should be accessed via
-- `Algebra.Ordered`.

{-# OPTIONS --postfix-projections --without-K --safe #-}

open import Relation.Binary.Core using (Rel; _⇒_)

module Algebra.Ordered.Structures.Duoidal
  {a ℓ₁ ℓ₂} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ₁)       -- The underlying equality relation
  (_≲_ : Rel A ℓ₂)       -- The underlying order relation
  where

open import Algebra.Core
open import Algebra.Definitions _≈_
open import Algebra.Structures _≈_
open import Algebra.Ordered.Definitions _≲_
open import Algebra.Ordered.Structures _≈_ _≲_
open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (flip; _$_)
open import Level using (_⊔_)
open import Relation.Binary.Consequences using (mono₂⇒cong₂)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)

------------------------------------------------------------------------------
-- Duoidal structures

record IsDuoidal (∙ ◁ : Op₂ A) (ε ι : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    ∙-isPomonoid : IsPomonoid ∙ ε
    ◁-isPomonoid : IsPomonoid ◁ ι
    ∙-◁-entropy  : Entropy ∙ ◁
    ∙-idem-ι     : ∙ SubidempotentOn ι
    ◁-idem-ε     : ◁ SuperidempotentOn ε
    ε≲ι          : ε ≲ ι

  open IsPomonoid ∙-isPomonoid public
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
      ; ∙-cong
      ; ∙-congˡ
      ; ∙-congʳ
      )
    renaming
      ( isMagma        to ∙-isMagma
      ; isSemigroup    to ∙-isSemigroup
      ; isMonoid       to ∙-isMonoid
      ; isPromagma     to ∙-isPromagma
      ; isProsemigroup to ∙-isProsemigroup
      ; isPromonoid    to ∙-isPromonoid
      ; isPomagma      to ∙-isPomagma
      ; isPosemigroup  to ∙-isPosemigroup
      ; assoc          to ∙-assoc
      ; identity       to ∙-identity
      ; identityˡ      to ∙-identityˡ
      ; identityʳ      to ∙-identityʳ
      ; mono           to ∙-mono
      ; monoˡ          to ∙-monoˡ
      ; monoʳ          to ∙-monoʳ
      )
  open IsPomonoid ◁-isPomonoid public
    hiding
      ( isPreorder
      ; isPartialOrder
      ; refl
      ; reflexive
      ; trans
      ; antisym
      ; isEquivalence
      ; setoid
      ; module Eq
      )
    renaming
      ( isMagma        to ◁-isMagma
      ; isSemigroup    to ◁-isSemigroup
      ; isMonoid       to ◁-isMonoid
      ; isPromagma     to ◁-isPromagma
      ; isProsemigroup to ◁-isProsemigroup
      ; isPromonoid    to ◁-isPromonoid
      ; isPomagma      to ◁-isPomagma
      ; isPosemigroup  to ◁-isPosemigroup
      ; assoc          to ◁-assoc
      ; identity       to ◁-identity
      ; identityˡ      to ◁-identityˡ
      ; identityʳ      to ◁-identityʳ
      ; mono           to ◁-mono
      ; monoˡ          to ◁-monoˡ
      ; monoʳ          to ◁-monoʳ
      ; ∙-cong         to ◁-cong
      ; ∙-congˡ        to ◁-congˡ
      ; ∙-congʳ        to ◁-congʳ
      )

record IsCommutativeDuoidal (∙ ◁ : Op₂ A) (ε ι : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isDuoidal : IsDuoidal ∙ ◁ ε ι
    ∙-comm    : Commutative ∙

  open IsDuoidal isDuoidal public

  ∙-isCommutativePomonoid : IsCommutativePomonoid ∙ ε
  ∙-isCommutativePomonoid = record
    { isPomonoid = ∙-isPomonoid
    ; comm       = ∙-comm
    }
