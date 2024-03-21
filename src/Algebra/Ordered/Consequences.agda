------------------------------------------------------------------------
-- The Agda standard library
--
-- Relations between properties of ordered algebraic structures
------------------------------------------------------------------------

{-# OPTIONS --postfix-projections --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel; _⇒_)

module Algebra.Ordered.Consequences where

open import Algebra.Core
open import Data.Product using (_,_; proj₁; proj₂)
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

  open import Algebra.Definitions
  open import Algebra.Ordered.Definitions _≲_
  open import Relation.Binary.Lattice.Definitions
  open IsPreorder isPreorder
  open Function.Equivalence

  comm∧residual⇒residuated : ∀ {∙ ⇨} → Commutative _≈_ ∙ → RightResidual ∙ ⇨ → Residuated ∙ (flip ⇨) ⇨
  comm∧residual⇒residuated comm residual .proj₁ .to x∙y≲z =
    residual .to (trans (≲-respˡ-≈ (comm _ _) refl) x∙y≲z)
  comm∧residual⇒residuated comm residual .proj₁ .from x≲z⇦y =
    trans (≲-respˡ-≈ (comm _ _) refl) (residual .from x≲z⇦y)
  comm∧residual⇒residuated comm residual .proj₁ .to-cong PropEq.refl = PropEq.refl
  comm∧residual⇒residuated comm residual .proj₁ .from-cong PropEq.refl = PropEq.refl
  comm∧residual⇒residuated comm residual .proj₂ = residual

  supremum∧residualʳ⇒distribˡ : ∀ {∨ ∙ ⇨} → Supremum _≲_ ∨ → RightResidual ∙ ⇨ → _DistributesOverˡ_ _≲_ ∙ ∨
  supremum∧residualʳ⇒distribˡ supremum residual x y z = residual .from [ residual .to inj₁ , residual .to inj₂ ]
    where
      inj₁  = λ {x y}   → let f , _ , _ = supremum x y in f
      inj₂  = λ {x y}   → let _ , g , _ = supremum x y in g
      [_,_] = λ {x y z} → let _ , _ , h = supremum x y in h z

  supremum∧residualˡ⇒distribʳ : ∀ {∨ ∙ ⇨} → Supremum _≲_ ∨ → LeftResidual ∙ ⇨ → _DistributesOverʳ_ _≲_ ∙ ∨
  supremum∧residualˡ⇒distribʳ supremum residual x y z = residual .from [ residual .to inj₁ , residual .to inj₂ ]
    where
      inj₁  = λ {x y}   → let f , _ , _ = supremum x y in f
      inj₂  = λ {x y}   → let _ , g , _ = supremum x y in g
      [_,_] = λ {x y z} → let _ , _ , h = supremum x y in h z

  supremum∧residuated⇒distrib : ∀ {∨ ∙ ⇦ ⇨} → Supremum _≲_ ∨ → Residuated ∙ ⇦ ⇨ → _DistributesOver_ _≲_ ∙ ∨
  supremum∧residuated⇒distrib supremum (residualˡ , residualʳ) = 
    (supremum∧residualʳ⇒distribˡ supremum residualʳ , supremum∧residualˡ⇒distribʳ supremum residualˡ)
