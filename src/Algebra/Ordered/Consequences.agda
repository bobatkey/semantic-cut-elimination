------------------------------------------------------------------------
-- The Agda standard library
--
-- Relations between properties of ordered algebraic structures
------------------------------------------------------------------------

{-# OPTIONS --postfix-projections --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel; _⇒_)

module Algebra.Ordered.Consequences where

open import Algebra.Core
open import Data.Product using (proj₁; proj₂)
open import Function using (flip)
open import Function.Bundles using (_⇔_)
open import Relation.Binary using (IsPreorder)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)


module _ 
  {a ℓ₁ ℓ₂} {A : Set a}  -- The underlying set
  {_≈_ : Rel A ℓ₁}       -- The underlying equality relation
  {_≲_ : Rel A ℓ₂}       -- The underlying order relation
  (isPreorder : IsPreorder _≈_ _≲_)
  where

  open import Algebra.Definitions _≈_
  open import Algebra.Ordered.Definitions _≲_
  open IsPreorder isPreorder
  open Function.Equivalence
  
  comm,residual⇒residuated : ∀ {∙ ⇨} → Commutative ∙ → RightResidual ∙ ⇨ → Residuated ∙ (flip ⇨) ⇨
  comm,residual⇒residuated comm residual .proj₁ x y z .to x∙y≲z = 
    residual y x z .to (trans (≲-respˡ-≈ (comm x y) refl) x∙y≲z)
  comm,residual⇒residuated comm residual .proj₁ x y z .from x≲z⇦y = 
    trans (≲-respˡ-≈ (comm y x) refl) (residual y x z .from x≲z⇦y)
  comm,residual⇒residuated comm residual .proj₁ x y z .to-cong PropEq.refl = PropEq.refl
  comm,residual⇒residuated comm residual .proj₁ x y z .from-cong PropEq.refl = PropEq.refl
  comm,residual⇒residuated comm residual .proj₂ = residual 