{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Consequences.Ordered where

open import Data.Maybe.Base using (just; nothing; decToMaybe)
open import Data.Sum.Base as Sum using (inj₁; inj₂; [_,_]′)
open import Data.Product using (_,_)
open import Data.Empty.Irrelevant using (⊥-elim)
open import Function.Base using (_∘_; _∘₂_; _$_; flip)
open import Level using (Level)
open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Nullary using (yes; no; recompute; ¬_)
open import Relation.Nullary.Decidable.Core using (map′)
open import Relation.Unary using (∁; Pred)

private
  variable
    a ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ p : Level
    A B : Set a

------------------------------------------------------------------------
-- Substitutive properties

module _ (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂) {≤₁ : Rel A ℓ₃} {≤₂ : Rel B ℓ₄} where

  mono⇒cong : Symmetric ≈₁ → ≈₁ ⇒ ≤₁ → Antisymmetric ≈₂ ≤₂ →
              ∀ {f} → f Preserves ≤₁ ⟶ ≤₂ → f Preserves ≈₁ ⟶ ≈₂
  mono⇒cong sym reflexive antisym mono x≈y = antisym
    (mono (reflexive x≈y))
    (mono (reflexive (sym x≈y)))

  antimono⇒cong : Symmetric ≈₁ → ≈₁ ⇒ ≤₁ → Antisymmetric ≈₂ ≤₂ →
                  ∀ {f} → f Preserves ≤₁ ⟶ (flip ≤₂) → f Preserves ≈₁ ⟶ ≈₂
  antimono⇒cong sym reflexive antisym antimono p≈q = antisym
    (antimono (reflexive (sym p≈q)))
    (antimono (reflexive p≈q))

  mono₂⇒cong₂ : Symmetric ≈₁ → ≈₁ ⇒ ≤₁ → Antisymmetric ≈₂ ≤₂ → ∀ {f} →
                f Preserves₂ ≤₁ ⟶ ≤₁ ⟶ ≤₂ →
                f Preserves₂ ≈₁ ⟶ ≈₁ ⟶ ≈₂
  mono₂⇒cong₂ sym reflexive antisym mono x≈y u≈v = antisym
    (mono (reflexive x≈y) (reflexive u≈v))
    (mono (reflexive (sym x≈y)) (reflexive (sym u≈v)))
