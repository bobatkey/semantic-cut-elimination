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

-- Interpret the equivalence
⟦_⟧eq : P ≃ Q → ⟦ P ⟧ ≈ ⟦ Q ⟧
⟦ emb φ   ⟧eq = EqClosure.gfold isEquivalence ⟦_⟧ ⟦_⟧eq-ax φ
⟦ φ `⟨⊗ Q ⟧eq = ⊗-cong ⟦ φ ⟧eq Eq.refl
⟦ P `⊗⟩ φ ⟧eq = ⊗-cong Eq.refl ⟦ φ ⟧eq
⟦ φ `⟨⅋ Q ⟧eq = ⅋-cong ⟦ φ  ⟧eq Eq.refl
⟦ P `⅋⟩ φ ⟧eq = ⅋-cong Eq.refl ⟦ φ  ⟧eq
⟦ φ `⟨◁ Q ⟧eq = ◁-cong ⟦ φ  ⟧eq Eq.refl
⟦ P `◁⟩ φ ⟧eq = ◁-cong Eq.refl ⟦ φ  ⟧eq
⟦ φ `⟨& Q ⟧eq = &-cong ⟦ φ  ⟧eq Eq.refl
⟦ P `&⟩ φ ⟧eq = &-cong Eq.refl ⟦ φ  ⟧eq
⟦ φ `⟨⊕ Q ⟧eq = ⊕-cong ⟦ φ ⟧eq Eq.refl
⟦ P `⊕⟩ φ ⟧eq = ⊕-cong Eq.refl ⟦ φ ⟧eq

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

-- Interpret the reduction modulo the equivalence
⟦_⟧step : CongClosure (_≃_ ∪ _⟶_) P Q → ⟦ Q ⟧ ≲ ⟦ P ⟧
⟦ emb φ   ⟧step = [ reflexive ∘ Eq.sym ∘ ⟦_⟧eq , ⟦_⟧step-ax ] φ
⟦ φ `⟨⊗ Q ⟧step = ⊗-mono ⟦ φ ⟧step refl
⟦ P `⊗⟩ φ ⟧step = ⊗-mono refl ⟦ φ ⟧step
⟦ φ `⟨⅋ Q ⟧step = ⅋-mono ⟦ φ ⟧step refl
⟦ P `⅋⟩ φ ⟧step = ⅋-mono refl ⟦ φ ⟧step
⟦ φ `⟨◁ Q ⟧step = ◁-mono ⟦ φ ⟧step refl
⟦ P `◁⟩ φ ⟧step = ◁-mono refl ⟦ φ ⟧step
⟦ φ `⟨& Q ⟧step = &-mono ⟦ φ ⟧step refl
⟦ P `&⟩ φ ⟧step = &-mono refl ⟦ φ ⟧step
⟦ φ `⟨⊕ Q ⟧step = ⊕-mono ⟦ φ ⟧step refl
⟦ P `⊕⟩ φ ⟧step = ⊕-mono refl ⟦ φ ⟧step

-- Interpret the reflexive-transitive closure of reduction
⟦_⟧steps : P ⟶⋆ Q → ⟦ Q ⟧ ≲ ⟦ P ⟧
⟦_⟧steps {P} {Q} = Star.gfold ⟦_⟧ (flip _≲_) (λ φ ψ → trans ψ ⟦ φ ⟧step) {P} {Q} {Q} refl
