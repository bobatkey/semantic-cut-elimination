{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level using (suc; _⊔_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (const; flip; _∘_)
open import Relation.Binary
open import Relation.Binary.Definitions using (Reflexive; Trans)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
import Relation.Binary.Construct.Closure.Symmetric as SymClosure
import Relation.Binary.Construct.Closure.Equivalence as EqClosure
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)

module BV.Base.Reasoning {a} (Atom : Set a) where

open import BV.Formula Atom
open import BV.Base Atom as BV public hiding (_⟶⋆_)

private
  variable
    P P′ : Formula
    Q Q′ : Formula
    R R′ : Formula
    S S′ : Formula

module Deep where

  infix  1 begin_
  infixr 2 _⟶⟨_⟩_
  infixr 2 _∼⟨_⟩_
  infixr 2 _∼⟨_⟨_
  infix  3 _∎

  data _IsDerivableFrom_ : Formula → Formula → Set (suc a) where
    _∼⟨_⟩_   : (P : Formula) → P ∼ᶜ Q → Q IsDerivableFrom R → P IsDerivableFrom R
    _∼⟨_⟨_   : (P : Formula) → Q ∼ᶜ P → Q IsDerivableFrom R → P IsDerivableFrom R
    _⟶⟨_⟩_  : (P : Formula) → P ⟶ᶜ Q → Q IsDerivableFrom R → P IsDerivableFrom R
    _∎       : (P : Formula) → P IsDerivableFrom P

  data _⟶⋆_ (P Q : Formula) : Set (suc a) where
    begin_ : P IsDerivableFrom Q → P ⟶⋆ Q

  to-≃ : P ≃ Q → P IsDerivableFrom Q
  to-≃ {P} {.P} ε                     = P ∎
  to-≃ {P} {Q} (SymClosure.fwd φ ◅ ψ) = P ∼⟨ φ ⟩ to-≃ ψ
  to-≃ {P} {Q} (SymClosure.bwd φ ◅ ψ) = P ∼⟨ φ ⟨ to-≃ ψ
  
  to-⟶ : P ⟶ Q → P IsDerivableFrom Q
  to-⟶ {P} {Q} P⟶Q = P ⟶⟨ emb P⟶Q ⟩ Q ∎

  _`⟨◁ᵈ : P IsDerivableFrom P′ → (P `◁ Q) IsDerivableFrom (P′ `◁ Q)
  (_ ⟶⟨ φ ⟩ ψ) `⟨◁ᵈ = _ ⟶⟨ φ `⟨◁ ⟩ ψ `⟨◁ᵈ
  (_ ∼⟨ φ ⟩ ψ) `⟨◁ᵈ = _ ∼⟨ φ `⟨◁ ⟩ ψ `⟨◁ᵈ
  (_ ∼⟨ φ ⟨ ψ) `⟨◁ᵈ = _ ∼⟨ φ `⟨◁ ⟨ ψ `⟨◁ᵈ
  (_ ∎) `⟨◁ᵈ = _ ∎

  `◁⟩ᵈ_ : Q IsDerivableFrom Q′ → (P `◁ Q) IsDerivableFrom (P `◁ Q′)
  `◁⟩ᵈ (_ ⟶⟨ φ ⟩ ψ) = _ ⟶⟨ `◁⟩ φ ⟩ `◁⟩ᵈ ψ
  `◁⟩ᵈ (_ ∼⟨ φ ⟩ ψ) = _ ∼⟨ `◁⟩ φ ⟩ `◁⟩ᵈ ψ
  `◁⟩ᵈ (_ ∼⟨ φ ⟨ ψ) = _ ∼⟨ `◁⟩ φ ⟨ `◁⟩ᵈ ψ
  `◁⟩ᵈ (_ ∎) = _ ∎

  _`⟨⊗ᵈ : P IsDerivableFrom P′ → (P `⊗ Q) IsDerivableFrom (P′ `⊗ Q)
  (_ ⟶⟨ φ ⟩ ψ) `⟨⊗ᵈ = _ ⟶⟨ φ `⟨⊗ ⟩ ψ `⟨⊗ᵈ
  (_ ∼⟨ φ ⟩ ψ) `⟨⊗ᵈ = _ ∼⟨ φ `⟨⊗ ⟩ ψ `⟨⊗ᵈ
  (_ ∼⟨ φ ⟨ ψ) `⟨⊗ᵈ = _ ∼⟨ φ `⟨⊗ ⟨ ψ `⟨⊗ᵈ
  (_ ∎) `⟨⊗ᵈ = _ ∎

  `⊗⟩ᵈ_ : Q IsDerivableFrom Q′ → (P `⊗ Q) IsDerivableFrom (P `⊗ Q′)
  `⊗⟩ᵈ (_ ⟶⟨ φ ⟩ ψ) = _ ⟶⟨ `⊗⟩ φ ⟩ `⊗⟩ᵈ ψ
  `⊗⟩ᵈ (_ ∼⟨ φ ⟩ ψ) = _ ∼⟨ `⊗⟩ φ ⟩ `⊗⟩ᵈ ψ
  `⊗⟩ᵈ (_ ∼⟨ φ ⟨ ψ) = _ ∼⟨ `⊗⟩ φ ⟨ `⊗⟩ᵈ ψ
  `⊗⟩ᵈ (_ ∎) = _ ∎

  _`⟨⅋ᵈ : P IsDerivableFrom P′ → (P `⅋ Q) IsDerivableFrom (P′ `⅋ Q)
  (_ ⟶⟨ φ ⟩ ψ) `⟨⅋ᵈ = _ ⟶⟨ φ `⟨⅋ ⟩ ψ `⟨⅋ᵈ
  (_ ∼⟨ φ ⟩ ψ) `⟨⅋ᵈ = _ ∼⟨ φ `⟨⅋ ⟩ ψ `⟨⅋ᵈ
  (_ ∼⟨ φ ⟨ ψ) `⟨⅋ᵈ = _ ∼⟨ φ `⟨⅋ ⟨ ψ `⟨⅋ᵈ
  (_ ∎) `⟨⅋ᵈ = _ ∎

  `⅋⟩ᵈ_ : Q IsDerivableFrom Q′ → (P `⅋ Q) IsDerivableFrom (P `⅋ Q′)
  `⅋⟩ᵈ (_ ⟶⟨ φ ⟩ ψ) = _ ⟶⟨ `⅋⟩ φ ⟩ `⅋⟩ᵈ ψ
  `⅋⟩ᵈ (_ ∼⟨ φ ⟩ ψ) = _ ∼⟨ `⅋⟩ φ ⟩ `⅋⟩ᵈ ψ
  `⅋⟩ᵈ (_ ∼⟨ φ ⟨ ψ) = _ ∼⟨ `⅋⟩ φ ⟨ `⅋⟩ᵈ ψ
  `⅋⟩ᵈ (_ ∎) = _ ∎

  to-⟶ᶜ : P ⟶ᶜ Q → P IsDerivableFrom Q
  to-⟶ᶜ (emb φ) = to-⟶ φ
  to-⟶ᶜ (φ `⟨◁) = to-⟶ᶜ φ `⟨◁ᵈ
  to-⟶ᶜ (`◁⟩ φ) = `◁⟩ᵈ to-⟶ᶜ φ
  to-⟶ᶜ (φ `⟨⊗) = to-⟶ᶜ φ `⟨⊗ᵈ
  to-⟶ᶜ (`⊗⟩ φ) = `⊗⟩ᵈ to-⟶ᶜ φ
  to-⟶ᶜ (φ `⟨⅋) = to-⟶ᶜ φ `⟨⅋ᵈ
  to-⟶ᶜ (`⅋⟩ φ) = `⅋⟩ᵈ to-⟶ᶜ φ

  to-⟶₌ : P ⟶₌ Q → P IsDerivableFrom Q
  to-⟶₌ (inj₁ φ) = to-≃ φ
  to-⟶₌ (inj₂ φ) = to-⟶ᶜ φ

  to-⟶⋆ : P BV.⟶⋆ Q → P IsDerivableFrom Q
  to-⟶⋆ {P} {.P} ε       = P ∎
  to-⟶⋆ {P} { Q} (φ ◅ ψ) = trans (to-⟶₌ φ) (to-⟶⋆ ψ)
    where
      trans : Transitive _IsDerivableFrom_
      trans (P ⟶⟨ φ ⟩ ψ′) ψ = P ⟶⟨ φ ⟩ trans ψ′ ψ
      trans (P ∼⟨ φ ⟩ ψ′) ψ = P ∼⟨ φ ⟩ trans ψ′ ψ
      trans (P ∼⟨ φ ⟨ ψ′) ψ = P ∼⟨ φ ⟨ trans ψ′ ψ
      trans (P ∎) ψ = ψ

  to : P BV.⟶⋆ Q → P ⟶⋆ Q
  to φ = begin to-⟶⋆ φ

  from : P IsDerivableFrom Q → P BV.⟶⋆ Q
  from (_ ⟶⟨ φ ⟩ ψ) = inj₂ φ ◅ from ψ
  from (_ ∼⟨ φ ⟩ ψ) = inj₁ (SymClosure.fwd φ ◅ ε) ◅ from ψ
  from (_ ∼⟨ φ ⟨ ψ) = inj₁ (SymClosure.bwd φ ◅ ε) ◅ from ψ
  from (_ ∎) = ε

open BV public using (_⟶⋆_)
open Deep public using (_∼⟨_⟩_; _∼⟨_⟨_; _⟶⟨_⟩_; _∎)

infix 1 begin_

begin_ : Deep._IsDerivableFrom_ ⇒ _⟶⋆_
begin φ = Deep.from φ
