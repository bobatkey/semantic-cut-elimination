{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level using (suc; _⊔_)
open import Data.Bool.Base using (Bool; true; false; T; not)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)

module MAV.Formula {a} (Atom : Set a) where

infix 20 `+_ 
infix 20 `-_ 
infix 15 `¬_
infix 10 _`⅋_
infix 10 _`⊗_
infix 10 _`&_
infix 10 _`⊕_
infix 10 _`◁_

data Formula : Set a where
  `I   : Formula
  `+_  : Atom → Formula
  `-_  : Atom → Formula
  _`⅋_ : Formula → Formula → Formula
  _`⊗_ : Formula → Formula → Formula
  _`&_ : Formula → Formula → Formula
  _`⊕_ : Formula → Formula → Formula
  _`◁_ : Formula → Formula → Formula

private
  variable
    P P′ : Formula
    Q Q′ : Formula
    R R′ : Formula
    S S′ : Formula

`¬_ : Formula → Formula
`¬ `I = `I
`¬ (`+ A) = `- A
`¬ (`- A) = `+ A
`¬ (P `⅋ Q) = `¬ P `⊗ `¬ Q
`¬ (P `⊗ Q) = `¬ P `⅋ `¬ Q
`¬ (P `& Q) = `¬ P `⊕ `¬ Q
`¬ (P `⊕ Q) = `¬ P `& `¬ Q
`¬ (P `◁ Q) = `¬ P `◁ `¬ Q


module _ {ℓ} (_∼_ : Rel Formula ℓ) where
  mutual
    private
      _≃_ : Rel Formula (suc a ⊔ ℓ)
      _≃_ = CongClosure

    data CongClosure : Rel Formula (suc a ⊔ ℓ) where
      emb   : P ∼ P′ → P ≃ P′
      _`⟨⊗_ : P ≃ P′ → (Q : Formula) → (P `⊗ Q) ≃ (P′ `⊗ Q)
      _`⊗⟩_ : (P : Formula) → Q ≃ Q′ → (P `⊗ Q) ≃ (P `⊗ Q′)
      _`⟨⅋_ : P ≃ P′ → (Q : Formula) → (P `⅋ Q) ≃ (P′ `⅋ Q)
      _`⅋⟩_ : (P : Formula) → Q ≃ Q′ → (P `⅋ Q) ≃ (P `⅋ Q′)
      _`⟨◁_ : P ≃ P′ → (Q : Formula) → (P `◁ Q) ≃ (P′ `◁ Q)
      _`◁⟩_ : (P : Formula) → Q ≃ Q′ → (P `◁ Q) ≃ (P `◁ Q′)
      _`⟨&_ : P ≃ P′ → (Q : Formula) → (P `& Q) ≃ (P′ `& Q)
      _`&⟩_ : (P : Formula) → Q ≃ Q′ → (P `& Q) ≃ (P `& Q′)
      _`⟨⊕_ : P ≃ P′ → (Q : Formula) → (P `⊕ Q) ≃ (P′ `⊕ Q)
      _`⊕⟩_ : (P : Formula) → Q ≃ Q′ → (P `⊕ Q) ≃ (P `⊕ Q′)

_≡ᵇ`I : (P : Formula) → Bool
`I       ≡ᵇ`I = true
(`+ A)   ≡ᵇ`I = false
(`- A)   ≡ᵇ`I = false
(P `⅋ Q) ≡ᵇ`I = false
(P `⊗ Q) ≡ᵇ`I = false
(P `& Q) ≡ᵇ`I = false
(P `⊕ Q) ≡ᵇ`I = false
(P `◁ Q) ≡ᵇ`I = false

record NonUnit (P : Formula) : Set where
  field
    nonUnit : T (not (P ≡ᵇ`I))

instance
  `+-nonUnit : ∀ {A}   → NonUnit (`+ A)
  `+-nonUnit = _
  `--nonUnit : ∀ {A}   → NonUnit (`- A)
  `--nonUnit = _
  `⅋-nonUnit : ∀ {P Q} → NonUnit (P `⅋ Q)
  `⅋-nonUnit = _
  `⊗-nonUnit : ∀ {P Q} → NonUnit (P `⊗ Q)
  `⊗-nonUnit = _
  `&-nonUnit : ∀ {P Q} → NonUnit (P `& Q)
  `&-nonUnit = _
  `⊕-nonUnit : ∀ {P Q} → NonUnit (P `⊕ Q)
  `⊕-nonUnit = _
  `◁-nonUnit : ∀ {P Q} → NonUnit (P `◁ Q)
  `◁-nonUnit = _

_≟`I : (P : Formula) → Dec (P ≡ `I)
`I       ≟`I = yes refl
(`+ A)   ≟`I = no (λ ())
(`- A)   ≟`I = no (λ ())
(P `⅋ Q) ≟`I = no (λ ())
(P `⊗ Q) ≟`I = no (λ ())
(P `& Q) ≟`I = no (λ ())
(P `⊕ Q) ≟`I = no (λ ())
(P `◁ Q) ≟`I = no (λ ())

≢-nonUnit : ∀ {P} → P ≢ `I → NonUnit P
≢-nonUnit {`I}     P≢`I = contradiction refl P≢`I 
≢-nonUnit {`+ A}   P≢`I = _
≢-nonUnit {`- A}   P≢`I = _
≢-nonUnit {P `⅋ Q} P≢`I = _
≢-nonUnit {P `⊗ Q} P≢`I = _
≢-nonUnit {P `& Q} P≢`I = _
≢-nonUnit {P `⊕ Q} P≢`I = _
≢-nonUnit {P `◁ Q} P≢`I = _
