{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level using (suc; _⊔_)
open import Relation.Binary
open import Data.Sum using (inj₂)
open import Relation.Binary.Construct.Union using (_∪_)
import Relation.Binary.Construct.Union as Union
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties as StarProps
open import Relation.Binary.Construct.Closure.Symmetric using (SymClosure)
import Relation.Binary.Construct.Closure.Symmetric as SymClosure
open import Relation.Binary.Construct.Closure.Equivalence using (EqClosure)
import Relation.Binary.Construct.Closure.Equivalence as EqClosure

module MAUV.Symmetric {a} (Atom : Set a) where

open import MAUV.Structure Atom

private
  variable
    A A′ : Atom
    B B′ : Atom
    P P′ : Structure
    Q Q′ : Structure
    R R′ : Structure
    S S′ : Structure

infix 5 _∼_

data _∼_ : Rel Structure a where
  `⊗-assoc     : ((P `⊗ Q) `⊗ R) ∼ (P `⊗ (Q `⊗ R))
  `⊗-comm      : (P `⊗ Q) ∼ (Q `⊗ P)
  `⊗-identityʳ : (P `⊗ `I) ∼ P
  `⅋-assoc     : ((P `⅋ Q) `⅋ R) ∼ (P `⅋ (Q `⅋ R))
  `⅋-comm      : (P `⅋ Q) ∼ (Q `⅋ P)
  `⅋-identityʳ : (P `⅋ `I) ∼ P
  `◁-assoc     : ((P `◁ Q) `◁ R) ∼ (P `◁ (Q `◁ R))
  `◁-identityʳ : (P `◁ `I) ∼ P
  `◁-identityˡ : (`I `◁ P) ∼ P

infix 5 _∼ᶜ_

_∼ᶜ_ : Rel Structure (suc a)
_∼ᶜ_ = CongClosure _∼_

infix 5 _≃_

_≃_ : Rel Structure (suc a)
_≃_ = EqClosure _∼ᶜ_

infix 5 _⟶_

data _⟶_ : Rel Structure a where
  `axiom    : ∀ P → P `⅋ `¬ P ⟶ `I
  `tidy     : `I `& `I ⟶ `I
  `switch   : (P `⊗ Q) `⅋ R ⟶ P `⊗ (Q `⅋ R)
  `sequence : (P `◁ Q) `⅋ (R `◁ S) ⟶ (P `⅋ R) `◁ (Q `⅋ S)
  `left     : P `⊕ Q ⟶ P
  `right    : P `⊕ Q ⟶ Q
  `external : (P `& Q) `⅋ R ⟶ (P `⅋ R) `& (Q `⅋ R)
  `medial   : (P `◁ Q) `& (R `◁ S) ⟶ (P `& R) `◁ (Q `& S)
  `externalu : `⊤ `⅋ R ⟶ `⊤
  `medialu   : `⊤ ⟶ `⊤ `◁ `⊤
  `medialu2  : `⊤ ⟶ `I

  `cut        : ∀ P → `I ⟶ P `⊗ `¬ P
  `cotidy     : `I ⟶ `I `⊕ `I
  `cosequence : (P `⊗ R) `◁ (Q `⊗ S) ⟶ (P `◁ Q) `⊗ (R `◁ S)
  `coleft     : P ⟶ P `& Q
  `coright    : Q ⟶ P `& Q
  `coexternal : (P `⊗ R) `⊕ (Q `⊗ R) ⟶ (P `⊕ Q) `⊗ R
  `comedial   : (P `⊕ R) `◁ (Q `⊕ S) ⟶ (P `◁ Q) `⊕ (R `◁ S)
  `coexternalu : `𝟘 ⟶ `𝟘 `⊗ R
  `comedialu   : `𝟘 `◁ `𝟘 ⟶ `𝟘
  `comedialu2  : `I ⟶ `𝟘

infix 5 _⟶ᶜ_

_⟶ᶜ_ : Rel Structure (suc a)
_⟶ᶜ_ = CongClosure _⟶_

infix 5 _⟶₌_

_⟶₌_ : Rel Structure (suc a)
_⟶₌_ = _≃_ ∪ _⟶ᶜ_

infix  5 _⟶⋆_

_⟶⋆_ : Rel Structure (suc a)
_⟶⋆_ = Star _⟶₌_

step : P ⟶ Q → P ⟶₌ Q
step P⟶Q = inj₂ (emb P⟶Q)
