------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of functions, such as associativity and commutativity
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra`, unless
-- you want to parameterise it via the equality relation.

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)
open import Relation.Nullary using (¬_)

module Algebra.Ordered.Definitions 
    {a ℓ} {A : Set a} -- The underlying set
    (_≲_ : Rel A ℓ)   -- The underlying order relation
  where

open import Algebra.Core
open import Data.Product
open import Function using (flip)
open import Function.Bundles using (_⇔_)

------------------------------------------------------------------------
-- Properties of operations

LeftResidual : Op₂ A → Op₂ A → Set _
LeftResidual _∙_ _⇦_ = ∀ {x y z} → (x ∙ y) ≲ z ⇔ x ≲ (z ⇦ y)

LeftEval : Op₂ A → Op₂ A → Set _
LeftEval _∙_ _⇦_ = ∀ {x y} → ((y ⇦ x) ∙ x) ≲ y

RightResidual : Op₂ A → Op₂ A → Set _
RightResidual _∙_ _⇨_ = ∀ {x y z} → (x ∙ y) ≲ z ⇔ y ≲ (x ⇨ z)

RightEval : Op₂ A → Op₂ A → Set _
RightEval _∙_ _⇨_ = ∀ {x y} → (x ∙ (x ⇨ y)) ≲ y

Residuated : Op₂ A → Op₂ A → Op₂ A → Set _
Residuated ∙ ⇦ ⇨ = LeftResidual ∙ ⇦ × RightResidual ∙ ⇨

Entropy : Op₂ A → Op₂ A → Set _
Entropy _∙_ _▷_ = ∀ w x y z → ((w ▷ x) ∙ (y ▷ z)) ≲ ((w ∙ y) ▷ (x ∙ z))

LeftContract : Op₂ A → A → Op₁ A → Set _
LeftContract _∙_ ε _ˡ = ∀ x → ((x ˡ) ∙ x) ≲ ε

LeftExpand : Op₂ A → A → Op₁ A → Set _
LeftExpand _∙_ ε _ˡ = ∀ x → ε ≲ (x ∙ (x ˡ))

RightContract : Op₂ A → A → Op₁ A → Set _
RightContract _∙_ ε _ʳ = ∀ x → (x ∙ (x ʳ)) ≲ ε

RightExpand : Op₂ A → A → Op₁ A → Set _
RightExpand _∙_ ε _ʳ = ∀ x → ε ≲ ((x ʳ) ∙ x)

_SubidempotentOn_ : Op₂ A → A → Set _
∙ SubidempotentOn x = ∙ IdempotentOn x
  where open import Algebra.Definitions _≲_

_SuperidempotentOn_ : Op₂ A → A → Set _
∙ SuperidempotentOn x = ∙ IdempotentOn x
  where open import Algebra.Definitions (flip _≲_)

Subidempotent : Op₂ A → Set _
Subidempotent ∙ = ∀ x → ∙ SubidempotentOn x

Superidempotent : Op₂ A → Set _
Superidempotent ∙ = ∀ x → ∙ SuperidempotentOn x
