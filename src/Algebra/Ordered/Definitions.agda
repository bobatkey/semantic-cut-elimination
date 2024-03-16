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
open import Function.Bundles using (_⇔_)

------------------------------------------------------------------------
-- Properties of operations

LeftResidual : Op₂ A → Op₂ A → Set _
LeftResidual _∙_ _⇦_ = ∀ x y z → (x ∙ y) ≲ z ⇔ y ≲ (z ⇦ x)

RightResidual : Op₂ A → Op₂ A → Set _
RightResidual _∙_ _⇨_ = ∀ x y z → (x ∙ y) ≲ z ⇔ x ≲ (y ⇨ z)

Residuated : Op₂ A → Op₂ A → Op₂ A → Set _
Residuated ∙ ⇦ ⇨ = LeftResidual ∙ ⇦ × RightResidual ∙ ⇨

Exchange : Op₂ A → Op₂ A → Set _
Exchange _∙_ _▷_ = ∀ w x y z → ((w ▷ x) ∙ (y ▷ z)) ≲ ((w ∙ y) ▷ (x ∙ z))
 