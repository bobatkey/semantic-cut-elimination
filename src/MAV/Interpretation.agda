{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level using (suc)
open import MAV.Model
open import Function using (flip; id; _∘_; _on_)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum using (_⊎_; [_,_])
open import Relation.Binary
open import Relation.Binary.Construct.Union using (_∪_)
import Relation.Binary.Construct.Union as Union
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _▻_)
import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
open import Relation.Binary.Construct.Closure.Equivalence using (EqClosure)
import Relation.Binary.Construct.Closure.Equivalence as EqClosure
open import Relation.Binary.Construct.Closure.Symmetric using (SymClosure; fwd; bwd)
import Relation.Binary.Construct.Closure.Symmetric as SymClosure
import Relation.Binary.Construct.Flip.EqAndOrd as Flip

module MAV.Interpretation
    {a c ℓ₁ ℓ₂}
    (Atom : Set a)
    (M : Model c ℓ₁ ℓ₂)
    (V : Atom → M .Model.Carrier)
  where

open import MAV.Structure Atom
open import MAV.Symmetric Atom

private
  variable
    P P′ : Structure
    Q Q′ : Structure

open Model M

⟦_⟧ : Structure → Carrier
⟦ `I     ⟧ = I
⟦ `+ x   ⟧ = V x
⟦ `- x   ⟧ = ¬ (V x)
⟦ P `⅋ Q ⟧ = ⟦ P ⟧ ⅋ ⟦ Q ⟧
⟦ P `⊗ Q ⟧ = ⟦ P ⟧ ⊗ ⟦ Q ⟧
⟦ P `& Q ⟧ = ⟦ P ⟧ & ⟦ Q ⟧
⟦ P `⊕ Q ⟧ = ⟦ P ⟧ ⊕ ⟦ Q ⟧
⟦ P `◁ Q ⟧ = ⟦ P ⟧ ◁ ⟦ Q ⟧

dual-ok : ∀ P → ⟦ `¬ P ⟧ ≈ ¬ ⟦ P ⟧
dual-ok `I = mix
dual-ok (`+ x) = Eq.refl
dual-ok (`- x) = Eq.sym (¬-involutive _)
dual-ok (P `⅋ Q) = Eq.trans (⊗-cong (dual-ok P) (dual-ok Q)) (Eq.sym (¬-involutive _))
dual-ok (P `⊗ Q) =
  Eq.trans (⅋-cong (dual-ok P) (dual-ok Q)) (¬-cong (⊗-cong (¬-involutive _) (¬-involutive _)))
dual-ok (P `& Q) = Eq.trans (⊕-cong (dual-ok P) (dual-ok Q)) (¬-cong (&-cong (¬-involutive _) (¬-involutive _)))
dual-ok (P `⊕ Q) = Eq.trans (&-cong (dual-ok P) (dual-ok Q)) (Eq.sym (¬-involutive _))
dual-ok (P `◁ Q) = Eq.trans (◁-cong (dual-ok P) (dual-ok Q)) (Eq.sym ◁-self-dual)

-- Interpret the equivalence axioms
⟦_⟧eq-ax : P ∼ Q → ⟦ P ⟧ ≈ ⟦ Q ⟧
⟦ `⊗-assoc     ⟧eq-ax = ⊗-assoc _ _ _
⟦ `⊗-comm      ⟧eq-ax = ⊗-comm _ _
⟦ `⊗-identityʳ ⟧eq-ax = ⊗-identityʳ _
⟦ `⅋-assoc     ⟧eq-ax = ⅋-assoc _ _ _
⟦ `⅋-comm      ⟧eq-ax = ⅋-comm _ _
⟦ `⅋-identityʳ ⟧eq-ax = Eq.trans (⅋-cong Eq.refl mix) (⅋-identityʳ _)
⟦ `◁-assoc     ⟧eq-ax = ◁-assoc _ _ _
⟦ `◁-identityʳ ⟧eq-ax = Eq.trans (◁-cong Eq.refl I-eq-J) (◁-identityʳ _)
⟦ `◁-identityˡ ⟧eq-ax = Eq.trans (◁-cong I-eq-J Eq.refl) (◁-identityˡ _)

-- The interpretation is closed under congruence
module _ {ℓ} {_𝓡_ : Rel Structure ℓ} where

  cong : (f : ∀ {P Q} → P 𝓡 Q → ⟦ P ⟧ ≈ ⟦ Q ⟧) → CongClosure _𝓡_ P Q → ⟦ P ⟧ ≈ ⟦ Q ⟧
  cong f (emb φ)   = f φ
  cong f (φ `⟨⊗) = ⊗-cong (cong f φ) Eq.refl
  cong f (`⊗⟩ φ) = ⊗-cong Eq.refl (cong f φ)
  cong f (φ `⟨⅋) = ⅋-cong (cong f φ) Eq.refl
  cong f (`⅋⟩ φ) = ⅋-cong Eq.refl (cong f φ)
  cong f (φ `⟨◁) = ◁-cong (cong f φ) Eq.refl
  cong f (`◁⟩ φ) = ◁-cong Eq.refl (cong f φ)
  cong f (φ `⟨&) = &-cong (cong f φ) Eq.refl
  cong f (`&⟩ φ) = &-cong Eq.refl (cong f φ)
  cong f (φ `⟨⊕) = ⊕-cong (cong f φ) Eq.refl
  cong f (`⊕⟩ φ) = ⊕-cong Eq.refl (cong f φ)

-- -- Interpret the equivalence
⟦_⟧eq : P ≃ Q → ⟦ P ⟧ ≈ ⟦ Q ⟧
⟦_⟧eq = EqClosure.gfold isEquivalence ⟦_⟧ (cong ⟦_⟧eq-ax)

-- Interpret the reduction axioms
⟦_⟧step-ax : P ⟶ Q → ⟦ Q ⟧ ≲ ⟦ P ⟧
⟦ `axiom P   ⟧step-ax =
  trans coev (⅋-mono refl (reflexive (Eq.sym (dual-ok P))))
⟦ `cut P     ⟧step-ax =
  trans (⊗-mono refl (reflexive (dual-ok P))) (trans ev (reflexive (Eq.sym mix)))
⟦ `tidy      ⟧step-ax = &-greatest refl refl
⟦ `switch    ⟧step-ax = linear-distrib
⟦ `sequence  ⟧step-ax = sequence
⟦ `left      ⟧step-ax = x≲x⊕y _ _
⟦ `right     ⟧step-ax = y≲x⊕y _ _
⟦ `external  ⟧step-ax = &-⅋-distrib
⟦ `medial    ⟧step-ax =
  &-greatest (◁-mono (x&y≲x _ _) (x&y≲x _ _)) (◁-mono (x&y≲y _ _) (x&y≲y _ _))
⟦ `cotidy    ⟧step-ax = ⊕-least refl refl
⟦ `cosequence ⟧step-ax = ⊗-◁-entropy _ _ _ _
⟦ `coleft     ⟧step-ax = x&y≲x _ _
⟦ `coright    ⟧step-ax = x&y≲y _ _
⟦ `coexternal ⟧step-ax = ⊕-⊗-distrib .proj₂ _ _ _
⟦ `comedial   ⟧step-ax =
  ⊕-least (◁-mono (x≲x⊕y _ _) (x≲x⊕y _ _)) (◁-mono (y≲x⊕y _ _) (y≲x⊕y _ _))

-- The interpretation is closed under monotonicity
module _ {ℓ} {_𝓡_ : Rel Structure ℓ} where

  mono : (f : ∀ {P Q} → P 𝓡 Q → ⟦ Q ⟧ ≲ ⟦ P ⟧) → CongClosure _𝓡_ P Q → ⟦ Q ⟧ ≲ ⟦ P ⟧
  mono f (emb φ)   = f φ
  mono f (φ `⟨◁) = ◁-mono (mono f φ) refl
  mono f (`◁⟩ φ) = ◁-mono refl (mono f φ)
  mono f (φ `⟨⊗) = ⊗-mono (mono f φ) refl
  mono f (`⊗⟩ φ) = ⊗-mono refl (mono f φ)
  mono f (φ `⟨⅋) = ⅋-mono (mono f φ) refl
  mono f (`⅋⟩ φ) = ⅋-mono refl (mono f φ)
  mono f (φ `⟨&) = &-mono (mono f φ) refl
  mono f (`&⟩ φ) = &-mono refl (mono f φ)
  mono f (φ `⟨⊕) = ⊕-mono (mono f φ) refl
  mono f (`⊕⟩ φ) = ⊕-mono refl (mono f φ)

-- Interpret the reduction modulo the equivalence
⟦_⟧step : P ⟶₌ Q → ⟦ Q ⟧ ≲ ⟦ P ⟧
⟦_⟧step = [ reflexive ∘ Eq.sym ∘ ⟦_⟧eq , mono ⟦_⟧step-ax ]

-- Interpret the reflexive-transitive closure of reduction
⟦_⟧steps : P ⟶⋆ Q → ⟦ Q ⟧ ≲ ⟦ P ⟧
⟦_⟧steps {P} {Q} = Star.gfold ⟦_⟧ (flip _≲_) (λ φ ψ → trans ψ ⟦ φ ⟧step) {P} {Q} {Q} refl
