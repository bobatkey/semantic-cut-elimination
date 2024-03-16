{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Definitions.Ordered where

open import Agda.Builtin.Equality using (_≡_)

open import Data.Maybe.Base using (Maybe)
open import Data.Product using (_×_)
open import Data.Sum.Base using (_⊎_)
open import Function.Base using (_on_; flip)
open import Level
open import Relation.Binary.Core
open import Relation.Nullary using (Dec; ¬_)

private
  variable
    a b c ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set a
    B : Set b
    C : Set c

-- Properties of order morphisms, aka order-preserving maps

Monotonic₁ : Rel A ℓ₁ → Rel B ℓ₂ → (A → B) → Set _
Monotonic₁ _≤_ _⊑_ f = f Preserves _≤_ ⟶ _⊑_

Antitonic₁ : Rel A ℓ₁ → Rel B ℓ₂ → (A → B) → Set _
Antitonic₁ _≤_ _⊑_ f = f Preserves (flip _≤_) ⟶ _⊑_

Monotonic₂ : Rel A ℓ₁ → Rel B ℓ₂ → Rel C ℓ₃ → (A → B → C) → Set _
Monotonic₂ _≤_ _⊑_ _≼_ ∙ = ∙ Preserves₂ _≤_ ⟶ _⊑_ ⟶ _≼_

MonotonicAntitonic : Rel A ℓ₁ → Rel B ℓ₂ → Rel C ℓ₃ → (A → B → C) → Set _
MonotonicAntitonic _≤_ _⊑_ _≼_ ∙ = ∙ Preserves₂ _≤_ ⟶ (flip _⊑_) ⟶ _≼_

AntitonicMonotonic : Rel A ℓ₁ → Rel B ℓ₂ → Rel C ℓ₃ → (A → B → C) → Set _
AntitonicMonotonic _≤_ _⊑_ _≼_ ∙ = ∙ Preserves₂ (flip _≤_) ⟶ _⊑_ ⟶ _≼_

Antitonic₂ : Rel A ℓ₁ → Rel B ℓ₂ → Rel C ℓ₃ → (A → B → C) → Set _
Antitonic₂ _≤_ _⊑_ _≼_ ∙ = ∙ Preserves₂ (flip _≤_) ⟶ (flip _⊑_) ⟶ _≼_

Adjoint : Rel A ℓ₁ → Rel B ℓ₂ → (A → B) → (B → A) → Set _
Adjoint _≤_ _⊑_ f g = ∀ {x y} → (f x ⊑ y → x ≤ g y) × (x ≤ g y → f x ⊑ y)
