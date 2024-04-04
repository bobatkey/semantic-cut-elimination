{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level using (suc; _⊔_)
open import Data.Bool.Base using (Bool; true; false; T; not)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)

module NEL.Structure {a} (Atom : Set a) where

infix 20 `+_
infix 20 `-_
infix 16 `!_ `?_
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
  `!_  : Structure → Structure
  `?_  : Structure → Structure

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
`¬ (`! P) = `? (`¬ P)
`¬ (`? P) = `! (`¬ P)
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
      `!⟩_  : P ≃ P′ → (`! P) ≃ (`! P′)
