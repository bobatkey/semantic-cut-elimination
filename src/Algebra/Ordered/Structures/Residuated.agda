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

module Algebra.Ordered.Structures.Residuated
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
open import Relation.Binary
open import Relation.Binary.Consequences using (mono₂⇒cong₂)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)

------------------------------------------------------------------------------
-- Residuated monoids

record IsResiduatedPromagma (∙ ⇦ ⇨ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPromagma : IsPromagma ∙
    residuated : Residuated ∙ ⇦ ⇨

  open IsPromagma isPromagma public

  residualˡ : LeftResidual ∙ ⇦
  residualˡ = proj₁ residuated

  residualʳ : RightResidual ∙ ⇨
  residualʳ = proj₂ residuated

  evalˡ : LeftEval ∙ ⇦
  evalˡ = residualˡ .Function.Equivalence.from refl

  evalʳ : RightEval ∙ ⇨
  evalʳ = residualʳ .Function.Equivalence.from refl

  mono-antiˡ : MonotonicAntitonic _≲_ _≲_ _≲_ ⇦
  mono-antiˡ w≲x z≲y
    = residualˡ .to
    $ flip trans w≲x
    $ residualʳ .from
    $ trans z≲y
    $ residualʳ .to
    $ residualˡ .from refl
    where open Function.Equivalence using (to; from)

  anti-monoʳ : AntitonicMonotonic _≲_ _≲_ _≲_ ⇨
  anti-monoʳ {w} {x} {y} {z} x≲w y≲z
    = residualʳ .to
    $ flip trans y≲z
    $ residualˡ .from
    $ trans x≲w
    $ residualˡ .to
    $ residualʳ .from refl
    where open Function.Equivalence using (to; from)

record IsResiduatedProsemigroup (∙ ⇦ ⇨ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isProsemigroup : IsProsemigroup ∙
    residuated : Residuated ∙ ⇦ ⇨

  open IsProsemigroup isProsemigroup public

  isResiduatedPromagma : IsResiduatedPromagma ∙ ⇦ ⇨
  isResiduatedPromagma = record { isPromagma = isPromagma ; residuated = residuated }

  open IsResiduatedPromagma isResiduatedPromagma public
    using ( residualˡ
          ; residualʳ
          ; evalˡ
          ; evalʳ
          ; mono-antiˡ
          ; anti-monoʳ
          )

record IsResiduatedPromonoid (∙ ⇦ ⇨ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPromonoid : IsPromonoid ∙ ε
    residuated : Residuated ∙ ⇦ ⇨

  open IsPromonoid isPromonoid public

  isResiduatedProsemigroup : IsResiduatedProsemigroup ∙ ⇦ ⇨
  isResiduatedProsemigroup = record { isProsemigroup = isProsemigroup ; residuated = residuated }

  open IsResiduatedProsemigroup isResiduatedProsemigroup public
    using ( residualˡ
          ; residualʳ
          ; evalˡ
          ; evalʳ
          ; mono-antiˡ
          ; anti-monoʳ
          )

record IsResiduatedCommutativePromonoid (∙ ⇨ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isCommutativePromonoid : IsCommutativePromonoid ∙ ε
    residuated             : Residuated ∙ (flip ⇨) ⇨

  open IsCommutativePromonoid isCommutativePromonoid public

  isResiduatedPromonoid : IsResiduatedPromonoid ∙ (flip ⇨) ⇨ ε
  isResiduatedPromonoid = record { isPromonoid = isPromonoid ; residuated = residuated }

  open IsResiduatedPromonoid isResiduatedPromonoid public
    using ( residualˡ
          ; residualʳ
          ; evalˡ
          ; evalʳ
          ; mono-antiˡ
          ; anti-monoʳ
          )

record IsResiduatedPomagma (∙ ⇦ ⇨ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPomagma  : IsPomagma ∙
    residuated : Residuated ∙ ⇦ ⇨

  open IsPomagma isPomagma public

  isResiduatedPromagma : IsResiduatedPromagma ∙ ⇦ ⇨
  isResiduatedPromagma = record { isPromagma = isPromagma ; residuated = residuated }

  open IsResiduatedPromagma isResiduatedPromagma public
    using ( residualˡ
          ; residualʳ
          ; evalˡ
          ; evalʳ
          ; mono-antiˡ
          ; anti-monoʳ
          )

record IsResiduatedPosemigroup (∙ ⇦ ⇨ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPosemigroup : IsPosemigroup ∙
    residuated : Residuated ∙ ⇦ ⇨

  open IsPosemigroup isPosemigroup public

  isResiduatedProsemigroup : IsResiduatedProsemigroup ∙ ⇦ ⇨
  isResiduatedProsemigroup = record { isProsemigroup = isProsemigroup ; residuated = residuated }

  open IsResiduatedProsemigroup isResiduatedProsemigroup public
    using ( residualˡ
          ; residualʳ
          ; evalˡ
          ; evalʳ
          ; mono-antiˡ
          ; anti-monoʳ
          )

record IsResiduatedPomonoid (∙ ⇦ ⇨ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPomonoid : IsPomonoid ∙ ε
    residuated : Residuated ∙ ⇦ ⇨

  open IsPomonoid isPomonoid public

  isResiduatedPromonoid : IsResiduatedPromonoid ∙ ⇦ ⇨ ε
  isResiduatedPromonoid = record { isPromonoid = isPromonoid ; residuated = residuated }

  open IsResiduatedPromonoid isResiduatedPromonoid public
    using ( residualˡ
          ; residualʳ
          ; evalˡ
          ; evalʳ
          ; mono-antiˡ
          ; anti-monoʳ
          )

record IsResiduatedCommutativePomonoid (∙ ⇨ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isCommutativePomonoid : IsCommutativePomonoid ∙ ε
    residuated : Residuated ∙ (flip ⇨) ⇨

  open IsCommutativePomonoid isCommutativePomonoid public

  isResiduatedCommutativePromonoid : IsResiduatedCommutativePromonoid ∙ ⇨ ε
  isResiduatedCommutativePromonoid = record { isCommutativePromonoid = isCommutativePromonoid ; residuated = residuated }

  open IsResiduatedCommutativePromonoid isResiduatedCommutativePromonoid public
    using ( residualˡ
          ; residualʳ
          ; evalˡ
          ; evalʳ
          ; mono-antiˡ
          ; anti-monoʳ
          )
