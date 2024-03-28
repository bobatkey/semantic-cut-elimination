{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level using (suc)
open import MAV.Model
open import Function using (flip; id; _∘_; _on_)
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

open import MAV.Formula Atom
open import MAV.Symmetric Atom

private
  variable
    P P′ : Formula
    Q Q′ : Formula

open Model M

⟦_⟧ : Formula → Carrier
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
dual-ok (`- x) = involution
dual-ok (P `⅋ Q) = Eq.trans (⊗-cong (dual-ok P) (dual-ok Q)) involution
dual-ok (P `⊗ Q) =
  Eq.trans (⅋-cong (dual-ok P) (dual-ok Q)) (¬-cong (⊗-cong (Eq.sym involution) (Eq.sym involution)))
dual-ok (P `& Q) = Eq.trans (⊕-cong (dual-ok P) (dual-ok Q)) (¬-cong (&-cong (Eq.sym involution) (Eq.sym involution)))
dual-ok (P `⊕ Q) = Eq.trans (&-cong (dual-ok P) (dual-ok Q)) involution
dual-ok (P `◁ Q) = Eq.trans (◁-cong (dual-ok P) (dual-ok Q)) (Eq.sym ◁-self-dual)

-- Interpret the equivalence axioms
⟦_⟧eq-ax : P ∼ Q → ⟦ P ⟧ ≈ ⟦ Q ⟧
⟦ `⊗-assoc _ _ _ ⟧eq-ax = ⊗-assoc _ _ _
⟦ `⊗-comm _ _    ⟧eq-ax = ⊗-comm _ _
⟦ `⊗-identityʳ _ ⟧eq-ax = ⊗-identityʳ _
⟦ `⅋-assoc _ _ _ ⟧eq-ax = ⅋-assoc _ _ _
⟦ `⅋-comm _ _    ⟧eq-ax = ⅋-comm _ _
⟦ `⅋-identityʳ P ⟧eq-ax = Eq.trans (⅋-cong Eq.refl mix) (⅋-identityʳ _)
⟦ `◁-assoc _ _ _ ⟧eq-ax = ◁-assoc _ _ _
⟦ `◁-identityʳ _ ⟧eq-ax = Eq.trans (◁-cong Eq.refl I-eq-J) (◁-identityʳ _)
⟦ `◁-identityˡ _ ⟧eq-ax = Eq.trans (◁-cong I-eq-J Eq.refl) (◁-identityˡ _)

-- The interpretation is closed under congruence
module _ {ℓ} {_𝓡_ : Rel Formula ℓ} where

  cong : (f : ∀ {P Q} → P 𝓡 Q → ⟦ P ⟧ ≈ ⟦ Q ⟧) → CongClosure _𝓡_ P Q → ⟦ P ⟧ ≈ ⟦ Q ⟧
  cong f (emb φ)   = f φ
  cong f (φ `⟨⊗ Q) = ⊗-cong (cong f φ) Eq.refl
  cong f (P `⊗⟩ φ) = ⊗-cong Eq.refl (cong f φ)
  cong f (φ `⟨⅋ Q) = ⅋-cong (cong f φ) Eq.refl
  cong f (P `⅋⟩ φ) = ⅋-cong Eq.refl (cong f φ)
  cong f (φ `⟨◁ Q) = ◁-cong (cong f φ) Eq.refl
  cong f (P `◁⟩ φ) = ◁-cong Eq.refl (cong f φ)
  cong f (φ `⟨& Q) = &-cong (cong f φ) Eq.refl
  cong f (P `&⟩ φ) = &-cong Eq.refl (cong f φ)
  cong f (φ `⟨⊕ Q) = ⊕-cong (cong f φ) Eq.refl
  cong f (P `⊕⟩ φ) = ⊕-cong Eq.refl (cong f φ)

-- -- Interpret the equivalence
⟦_⟧eq : P ≃ Q → ⟦ P ⟧ ≈ ⟦ Q ⟧
⟦_⟧eq = EqClosure.gfold isEquivalence ⟦_⟧ (cong ⟦_⟧eq-ax)

-- Interpret the reduction axioms
⟦_⟧step-ax : P ⟶ Q → ⟦ Q ⟧ ≲ ⟦ P ⟧
⟦ `axiom P   ⟧step-ax = trans coev (⅋-mono refl (reflexive (Eq.sym (dual-ok P))))
⟦ `cut P     ⟧step-ax = trans (⊗-mono refl (reflexive (dual-ok P))) (trans ev (reflexive (Eq.sym mix)))
⟦ `tidy      ⟧step-ax = &-greatest refl refl
⟦ `switch    ⟧step-ax = linear-distrib
⟦ `sequence  ⟧step-ax = sequence
⟦ `left      ⟧step-ax = x≲x⊕y _ _
⟦ `right     ⟧step-ax = y≲x⊕y _ _
⟦ `external  ⟧step-ax = &-⅋-distrib
⟦ `medial    ⟧step-ax = &-greatest (◁-mono (x&y≲x _ _) (x&y≲x _ _)) (◁-mono (x&y≲y _ _) (x&y≲y _ _))


-- The interpretation is closed under monotonicity
module _ {ℓ} {_𝓡_ : Rel Formula ℓ} where

  mono : (f : ∀ {P Q} → P 𝓡 Q → ⟦ Q ⟧ ≲ ⟦ P ⟧) → CongClosure _𝓡_ P Q → ⟦ Q ⟧ ≲ ⟦ P ⟧
  mono f (emb φ)   = f φ
  mono f (φ `⟨⊗ Q) = ⊗-mono (mono f φ) refl
  mono f (P `⊗⟩ φ) = ⊗-mono refl (mono f φ)
  mono f (φ `⟨⅋ Q) = ⅋-mono (mono f φ) refl
  mono f (P `⅋⟩ φ) = ⅋-mono refl (mono f φ)
  mono f (φ `⟨◁ Q) = ◁-mono (mono f φ) refl
  mono f (P `◁⟩ φ) = ◁-mono refl (mono f φ)
  mono f (φ `⟨& Q) = &-mono (mono f φ) refl
  mono f (P `&⟩ φ) = &-mono refl (mono f φ)
  mono f (φ `⟨⊕ Q) = ⊕-mono (mono f φ) refl
  mono f (P `⊕⟩ φ) = ⊕-mono refl (mono f φ)

-- Interpret the reduction modulo the equivalence
⟦_⟧step : P ⟶₌ Q → ⟦ Q ⟧ ≲ ⟦ P ⟧
⟦_⟧step = [ reflexive ∘ Eq.sym ∘ ⟦_⟧eq , mono ⟦_⟧step-ax ]

-- Interpret the reflexive-transitive closure of reduction
⟦_⟧steps : P ⟶⋆ Q → ⟦ Q ⟧ ≲ ⟦ P ⟧
⟦_⟧steps {P} {Q} = Star.gfold ⟦_⟧ (flip _≲_) (λ φ ψ → trans ψ ⟦ φ ⟧step) {P} {Q} {Q} refl
