{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Relation.Binary using (Preorder)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star)

module MAV.Symmetric {a} (Atom : Set a) where

open import MAV.Formula Atom

private
  variable
    A A′ : Atom
    B B′ : Atom
    P P′ : Formula
    Q Q′ : Formula
    R R′ : Formula
    S S′ : Formula

infix 5 _⟶_

data _⟶_ : Formula → Formula → Set a where
  `axiom    : ∀ P → P `⅋ `¬ P ⟶ `I
  `cut      : ∀ P → `I ⟶ P `⊗ `¬ P

  `tidy     : `I `& `I ⟶ `I
  `switch   : (P `⊗ Q) `⅋ R ⟶ P `⊗ (Q `⅋ R)
  `sequence : (P `◁ Q) `⅋ (R `◁ S) ⟶ (P `⅋ R) `◁ (Q `⅋ S)
  `left     : P `⊕ Q ⟶ P
  `right    : P `⊕ Q ⟶ Q
  `external : (P `& Q) `⅋ R ⟶ (P `⅋ R) `& (Q `⅋ R)
  `medial   : (P `◁ Q) `& (R `◁ S) ⟶ (P `& R) `◁ (Q `& S)

  _`⟨⊗_      : P ⟶ P′ → (Q : Formula) → P `⊗ Q ⟶ P′ `⊗ Q
  _`⊗⟩_      : (P : Formula) → Q ⟶ Q′ → P `⊗ Q ⟶ P `⊗ Q′
  `⊗-assoc   : P `⊗ (Q `⊗ R) ⟶ (P `⊗ Q) `⊗ R
  `⊗-assoc⁻¹ : (P `⊗ Q) `⊗ R ⟶ P `⊗ (Q `⊗ R)
  `⊗-comm    : P `⊗ Q ⟶ Q `⊗ P
  `⊗-unit    : P `⊗ `I ⟶ P
  `⊗-unit⁻¹  : P ⟶ P `⊗ `I

  _`⟨⅋_      : P ⟶ P′ → (Q : Formula) → P `⅋ Q ⟶ P′ `⅋ Q
  _`⅋⟩_      : (P : Formula) → Q ⟶ Q′ → P `⅋ Q ⟶ P `⅋ Q′
  `⅋-assoc   : P `⅋ (Q `⅋ R) ⟶ (P `⅋ Q) `⅋ R
  `⅋-assoc⁻¹ : (P `⅋ Q) `⅋ R ⟶ P `⅋ (Q `⅋ R)
  `⅋-comm    : P `⅋ Q ⟶ Q `⅋ P
  `⅋-unit    : P `⅋ `I ⟶ P
  `⅋-unit⁻¹  : P ⟶ P `⅋ `I

  _`⟨◁_      : P ⟶ P′ → (Q : Formula) → P `◁ Q ⟶ P′ `◁ Q
  _`◁⟩_      : (P : Formula) → Q ⟶ Q′ → P `◁ Q ⟶ P `◁ Q′
  `◁-assoc   : P `◁ (Q `◁ R) ⟶ (P `◁ Q) `◁ R
  `◁-assoc⁻¹ : (P `◁ Q) `◁ R ⟶ P `◁ (Q `◁ R)
  `◁-runit   : P `◁ `I ⟶ P
  `◁-runit⁻¹ : P ⟶ P `◁ `I
  `◁-lunit   : `I `◁ P ⟶ P
  `◁-lunit⁻¹ : P ⟶ `I `◁ P

  _`⟨&_      : P ⟶ P′ → (Q : Formula) → P `& Q ⟶ P′ `& Q
  _`&⟩_      : (P : Formula) → Q ⟶ Q′ → P `& Q ⟶ P `& Q′

  _`⟨⊕_      : P ⟶ P′ → (Q : Formula) → P `⊕ Q ⟶ P′ `⊕ Q
  _`⊕⟩_      : (P : Formula) → Q ⟶ Q′ → P `⊕ Q ⟶ P `⊕ Q′

infix  5 _⟶⋆_

_⟶⋆_ : Formula → Formula → Set a
_⟶⋆_ = Star _⟶_
