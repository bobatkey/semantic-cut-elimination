{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level using (suc; _⊔_)
open import Data.Bool.Base using (Bool; true; false; T; not)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)

module BV.Structure {a} (Atom : Set a) where

infix 20 `+_ 
infix 20 `-_ 
infix 15 `¬_
infix 10 _`◁_
infix 10 _`⅋_
infix 10 _`⊗_

data Structure : Set a where
  `I   : Structure
  `+_  : Atom → Structure
  `-_  : Atom → Structure
  _`◁_ : Structure → Structure → Structure
  _`⅋_ : Structure → Structure → Structure
  _`⊗_ : Structure → Structure → Structure

private
  variable
    P P′ : Structure
    Q Q′ : Structure
    R R′ : Structure
    S S′ : Structure

`¬_ : Structure → Structure
`¬ `I = `I
`¬ (`+ A) = `- A
`¬ (`- A) = `+ A
`¬ (P `◁ Q) = `¬ P `◁ `¬ Q
`¬ (P `⅋ Q) = `¬ P `⊗ `¬ Q
`¬ (P `⊗ Q) = `¬ P `⅋ `¬ Q


module _ {ℓ} (_∼_ : Rel Structure ℓ) where
  mutual
    private
      _≃_ : Rel Structure (suc a ⊔ ℓ)
      _≃_ = CongClosure

    data CongClosure : Rel Structure (suc a ⊔ ℓ) where
      emb   : P ∼ P′ → P ≃ P′
      _`⟨◁ : P ≃ P′ → (P `◁ Q) ≃ (P′ `◁ Q)
      `◁⟩_ : Q ≃ Q′ → (P `◁ Q) ≃ (P `◁ Q′)
      _`⟨⊗ : P ≃ P′ → (P `⊗ Q) ≃ (P′ `⊗ Q)
      `⊗⟩_ : Q ≃ Q′ → (P `⊗ Q) ≃ (P `⊗ Q′)
      _`⟨⅋ : P ≃ P′ → (P `⅋ Q) ≃ (P′ `⅋ Q)
      `⅋⟩_ : Q ≃ Q′ → (P `⅋ Q) ≃ (P `⅋ Q′)

_≡ᵇ`I : (P : Structure) → Bool
`I       ≡ᵇ`I = true
(`+ A)   ≡ᵇ`I = false
(`- A)   ≡ᵇ`I = false
(P `◁ Q) ≡ᵇ`I = false
(P `⅋ Q) ≡ᵇ`I = false
(P `⊗ Q) ≡ᵇ`I = false

record NonUnit (P : Structure) : Set where
  field
    nonUnit : T (not (P ≡ᵇ`I))

instance
  `+-nonUnit : ∀ {A}   → NonUnit (`+ A)
  `+-nonUnit = _
  `--nonUnit : ∀ {A}   → NonUnit (`- A)
  `--nonUnit = _
  `◁-nonUnit : ∀ {P Q} → NonUnit (P `◁ Q)
  `◁-nonUnit = _
  `⅋-nonUnit : ∀ {P Q} → NonUnit (P `⅋ Q)
  `⅋-nonUnit = _
  `⊗-nonUnit : ∀ {P Q} → NonUnit (P `⊗ Q)
  `⊗-nonUnit = _

_≟`I : (P : Structure) → Dec (P ≡ `I)
`I       ≟`I = yes refl
(`+ A)   ≟`I = no (λ ())
(`- A)   ≟`I = no (λ ())
(P `◁ Q) ≟`I = no (λ ())
(P `⅋ Q) ≟`I = no (λ ())
(P `⊗ Q) ≟`I = no (λ ())

≢-nonUnit : ∀ {P} → P ≢ `I → NonUnit P
≢-nonUnit {`I}     P≢`I = contradiction refl P≢`I 
≢-nonUnit {`+ A}   P≢`I = _
≢-nonUnit {`- A}   P≢`I = _
≢-nonUnit {P `◁ Q} P≢`I = _
≢-nonUnit {P `⅋ Q} P≢`I = _
≢-nonUnit {P `⊗ Q} P≢`I = _
