{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level using (suc; _⊔_)
open import Data.Bool.Base using (Bool; true; false; T; not)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)

module NEL.Formula {a} (Atom : Set a) where

infix 20 `+_
infix 20 `-_
infix 16 `!_ `?_
infix 15 `¬_
infix 10 _`◁_
infix 10 _`⅋_
infix 10 _`⊗_

data Formula : Set a where
  `I   : Formula
  `+_  : Atom → Formula
  `-_  : Atom → Formula
  _`◁_ : Formula → Formula → Formula
  _`⅋_ : Formula → Formula → Formula
  _`⊗_ : Formula → Formula → Formula
  `!_  : Formula → Formula
  `?_  : Formula → Formula

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
`¬ (`! P) = `? (`¬ P)
`¬ (`? P) = `! (`¬ P)
`¬ (P `◁ Q) = `¬ P `◁ `¬ Q
`¬ (P `⅋ Q) = `¬ P `⊗ `¬ Q
`¬ (P `⊗ Q) = `¬ P `⅋ `¬ Q


module _ {ℓ} (_∼_ : Rel Formula ℓ) where
  mutual
    private
      _≃_ : Rel Formula (suc a ⊔ ℓ)
      _≃_ = CongClosure

    data CongClosure : Rel Formula (suc a ⊔ ℓ) where
      emb   : P ∼ P′ → P ≃ P′
      _`⟨◁ : P ≃ P′ → (P `◁ Q) ≃ (P′ `◁ Q)
      `◁⟩_ : Q ≃ Q′ → (P `◁ Q) ≃ (P `◁ Q′)
      _`⟨⊗ : P ≃ P′ → (P `⊗ Q) ≃ (P′ `⊗ Q)
      `⊗⟩_ : Q ≃ Q′ → (P `⊗ Q) ≃ (P `⊗ Q′)
      _`⟨⅋ : P ≃ P′ → (P `⅋ Q) ≃ (P′ `⅋ Q)
      `⅋⟩_ : Q ≃ Q′ → (P `⅋ Q) ≃ (P `⅋ Q′)
      `!⟩_  : P ≃ P′ → (`! P) ≃ (`! P′)
