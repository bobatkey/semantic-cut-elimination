{-# OPTIONS --postfix-projections --safe --without-K #-}

open import MAV.Model
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)

module MAV.Interpretation {a ℓ₁ ℓ₂}
         (Atom : Set) (M : Model a ℓ₁ ℓ₂) (V : Atom → M .Model.Carrier) where

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
⟦ P `▷ Q ⟧ = ⟦ P ⟧ ▷ ⟦ Q ⟧

dual-ok : ∀ P → ⟦ `¬ P ⟧ ≈ ¬ ⟦ P ⟧
dual-ok `I = mix
dual-ok (`+ x) = Eq.refl
dual-ok (`- x) = involution
dual-ok (P `⅋ Q) = Eq.trans (⊗-cong (dual-ok P) (dual-ok Q)) involution
dual-ok (P `⊗ Q) =
  Eq.trans (⅋-cong (dual-ok P) (dual-ok Q)) (¬-cong (⊗-cong (Eq.sym involution) (Eq.sym involution)))
dual-ok (P `& Q) = Eq.trans (⊕-cong (dual-ok P) (dual-ok Q)) (¬-cong (&-cong (Eq.sym involution) (Eq.sym involution)))
dual-ok (P `⊕ Q) = Eq.trans (&-cong (dual-ok P) (dual-ok Q)) involution
dual-ok (P `▷ Q) = Eq.trans (▷-cong (dual-ok P) (dual-ok Q)) (Eq.sym ▷-self-dual)

⟦_⟧step : P ⟶ Q → ⟦ Q ⟧ ≲ ⟦ P ⟧
⟦ `axiom P   ⟧step = trans coev (⅋-mono refl (reflexive (Eq.sym (dual-ok P))))
⟦ `cut P     ⟧step = trans (⊗-mono refl (reflexive (dual-ok P))) (trans ev (reflexive (Eq.sym mix)))
⟦ `tidy      ⟧step = &-greatest refl refl
⟦ `switch    ⟧step = linear-distrib
⟦ `sequence  ⟧step = sequence
⟦ `left      ⟧step = x≲x⊕y _ _
⟦ `right     ⟧step = y≲x⊕y _ _
⟦ `external  ⟧step = &-⅋-distrib
⟦ `medial    ⟧step = &-greatest (▷-mono (x&y≲x _ _) (x&y≲x _ _)) (▷-mono (x&y≲y _ _) (x&y≲y _ _))
⟦ S `⟨⊗ Q    ⟧step = ⊗-mono ⟦ S ⟧step refl
⟦ P `⊗⟩ S    ⟧step = ⊗-mono refl ⟦ S ⟧step
⟦ `⊗-assoc   ⟧step = reflexive (⊗-assoc _ _ _)
⟦ `⊗-assoc⁻¹ ⟧step = reflexive (Eq.sym (⊗-assoc _ _ _))
⟦ `⊗-comm    ⟧step = reflexive (⊗-comm _ _)
⟦ `⊗-unit    ⟧step = reflexive (Eq.sym (⊗-identityʳ _))
⟦ `⊗-unit⁻¹  ⟧step = reflexive (⊗-identityʳ _)
⟦ S `⟨⅋ Q    ⟧step = ⅋-mono ⟦ S ⟧step refl
⟦ P `⅋⟩ S    ⟧step = ⅋-mono refl ⟦ S ⟧step
⟦ `⅋-assoc   ⟧step = reflexive (⅋-assoc _ _ _)
⟦ `⅋-assoc⁻¹ ⟧step = reflexive (Eq.sym (⅋-assoc _ _ _))
⟦ `⅋-comm    ⟧step = reflexive (⅋-comm _ _)
⟦ `⅋-unit    ⟧step = reflexive (Eq.trans (Eq.sym (⅋-identityʳ _)) (⅋-cong Eq.refl (Eq.sym mix)))
⟦ `⅋-unit⁻¹  ⟧step = reflexive (Eq.trans (⅋-cong Eq.refl mix) (⅋-identityʳ _))
⟦ S `⟨▷ Q    ⟧step = ▷-mono ⟦ S ⟧step refl
⟦ P `▷⟩ S    ⟧step = ▷-mono refl ⟦ S ⟧step
⟦ `▷-assoc   ⟧step = reflexive (▷-assoc _ _ _)
⟦ `▷-assoc⁻¹ ⟧step = reflexive (Eq.sym (▷-assoc _ _ _))
⟦ `▷-runit   ⟧step = reflexive (Eq.sym (Eq.trans (▷-cong Eq.refl I-eq-J) (▷-identityʳ _)))
⟦ `▷-runit⁻¹ ⟧step = reflexive (Eq.trans (▷-cong Eq.refl I-eq-J) (▷-identityʳ _))
⟦ `▷-lunit   ⟧step = reflexive (Eq.sym (Eq.trans (▷-cong I-eq-J Eq.refl) (▷-identityˡ _)))
⟦ `▷-lunit⁻¹ ⟧step = reflexive (Eq.trans (▷-cong I-eq-J Eq.refl) (▷-identityˡ _))
⟦ S `⟨& Q    ⟧step = &-mono ⟦ S ⟧step refl
⟦ P `&⟩ S    ⟧step = &-mono refl ⟦ S ⟧step
⟦ S `⟨⊕ Q    ⟧step = ⊕-mono ⟦ S ⟧step refl
⟦ P `⊕⟩ S    ⟧step = ⊕-mono refl ⟦ S ⟧step

⟦_⟧steps : P ⟶⋆ Q → ⟦ Q ⟧ ≲ ⟦ P ⟧
⟦ ε     ⟧steps = refl
⟦ x ◅ S ⟧steps = trans ⟦ S ⟧steps ⟦ x ⟧step
