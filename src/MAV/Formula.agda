{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Data.Bool.Base using (Bool; true; false; T; not)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)

module MAV.Formula (At : Set) where

infix 20 `+_ 
infix 20 `-_ 
infix 15 `¬_
infix 10 _`⅋_
infix 10 _`⊗_
infix 10 _`&_
infix 10 _`⊕_
infix 10 _`▷_

data Formula : Set where
  `I   : Formula
  `+_  : At → Formula
  `-_  : At → Formula
  _`⅋_ : Formula → Formula → Formula
  _`⊗_ : Formula → Formula → Formula
  _`&_ : Formula → Formula → Formula
  _`⊕_ : Formula → Formula → Formula
  _`▷_ : Formula → Formula → Formula

`¬_ : Formula → Formula
`¬ `I = `I
`¬ (`+ A) = `- A
`¬ (`- A) = `+ A
`¬ (P `⅋ Q) = `¬ P `⊗ `¬ Q
`¬ (P `⊗ Q) = `¬ P `⅋ `¬ Q
`¬ (P `& Q) = `¬ P `⊕ `¬ Q
`¬ (P `⊕ Q) = `¬ P `& `¬ Q
`¬ (P `▷ Q) = `¬ P `▷ `¬ Q

_≡ᵇ`I : (P : Formula) → Bool
`I       ≡ᵇ`I = true
(`+ A)   ≡ᵇ`I = false
(`- A)   ≡ᵇ`I = false
(P `⅋ Q) ≡ᵇ`I = false
(P `⊗ Q) ≡ᵇ`I = false
(P `& Q) ≡ᵇ`I = false
(P `⊕ Q) ≡ᵇ`I = false
(P `▷ Q) ≡ᵇ`I = false

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
  `▷-nonUnit : ∀ {P Q} → NonUnit (P `▷ Q)
  `▷-nonUnit = _
