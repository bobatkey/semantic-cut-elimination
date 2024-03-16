------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of functions, such as associativity and commutativity
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra`, unless
-- you want to parameterise it via the equality relation.

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core
open import Relation.Nullary using (¬_)

module Algebra.Ordered.Definitions
  {a ℓ} {A : Set a}   -- The underlying set
  (_≈_ : Rel A ℓ)     -- The underlying equality
  where

open import Algebra.Core
open import Data.Product
open import Data.Sum.Base

------------------------------------------------------------------------
-- Properties of operations

LeftResidual : Op₂ A → Op₂ A → Set _
LeftResidual _∙_ _⇐_ = ∀ {x y z} → (x ∙ y) ≈ z → x ≈ (z ⇐ y)

RightResidual : Op₂ A → Op₂ A → Set _
RightResidual _∙_ _⇒_ = ∀ {x y z} → (x ∙ y) ≈ z → x ≈ (y ⇒ z)
