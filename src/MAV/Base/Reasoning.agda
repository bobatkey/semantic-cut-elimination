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

module MAV.Base.Reasoning {a} (Atom : Set a) where

open import MAV.Formula Atom
import MAV.Base Atom as MAV

private
  variable
    P P′ : Formula
    Q Q′ : Formula
    R R′ : Formula
    S S′ : Formula

module Deep where

  open MAV public hiding (_⟶⋆_)

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

  from-≃ : P ≃ Q → P IsDerivableFrom Q
  from-≃ {P} {.P} ε                     = P ∎
  from-≃ {P} {Q} (SymClosure.fwd φ ◅ ψ) = P ∼⟨ φ ⟩ from-≃ ψ
  from-≃ {P} {Q} (SymClosure.bwd φ ◅ ψ) = P ∼⟨ φ ⟨ from-≃ ψ
  
  from-⟶ : P ⟶ Q → P IsDerivableFrom Q
  from-⟶ {P} {Q} P⟶Q = P ⟶⟨ emb P⟶Q ⟩ Q ∎

  _`⟨⊗ᵈ_ : P IsDerivableFrom P′ → (Q : Formula) → (P `⊗ Q) IsDerivableFrom (P′ `⊗ Q)
  (P ⟶⟨ φ ⟩ ψ) `⟨⊗ᵈ Q = P `⊗ Q ⟶⟨ φ `⟨⊗ Q ⟩ ψ `⟨⊗ᵈ Q
  (P ∼⟨ φ ⟩ ψ) `⟨⊗ᵈ Q = P `⊗ Q ∼⟨ φ `⟨⊗ Q ⟩ ψ `⟨⊗ᵈ Q
  (P ∼⟨ φ ⟨ ψ) `⟨⊗ᵈ Q = P `⊗ Q ∼⟨ φ `⟨⊗ Q ⟨ ψ `⟨⊗ᵈ Q
  (P ∎) `⟨⊗ᵈ Q = (P `⊗ Q) ∎

  _`⊗⟩ᵈ_ : (P : Formula) → Q IsDerivableFrom Q′ → (P `⊗ Q) IsDerivableFrom (P `⊗ Q′)
  P `⊗⟩ᵈ (Q ⟶⟨ φ ⟩ ψ) = P `⊗ Q ⟶⟨ P `⊗⟩ φ ⟩ P `⊗⟩ᵈ ψ
  P `⊗⟩ᵈ (Q ∼⟨ φ ⟩ ψ) = P `⊗ Q ∼⟨ P `⊗⟩ φ ⟩ P `⊗⟩ᵈ ψ
  P `⊗⟩ᵈ (Q ∼⟨ φ ⟨ ψ) = P `⊗ Q ∼⟨ P `⊗⟩ φ ⟨ P `⊗⟩ᵈ ψ
  P `⊗⟩ᵈ (Q ∎) = P `⊗ Q ∎

  _`⟨⅋ᵈ_ : P IsDerivableFrom P′ → (Q : Formula) → (P `⅋ Q) IsDerivableFrom (P′ `⅋ Q)
  (P ⟶⟨ φ ⟩ ψ) `⟨⅋ᵈ Q = P `⅋ Q ⟶⟨ φ `⟨⅋ Q ⟩ ψ `⟨⅋ᵈ Q
  (P ∼⟨ φ ⟩ ψ) `⟨⅋ᵈ Q = P `⅋ Q ∼⟨ φ `⟨⅋ Q ⟩ ψ `⟨⅋ᵈ Q
  (P ∼⟨ φ ⟨ ψ) `⟨⅋ᵈ Q = P `⅋ Q ∼⟨ φ `⟨⅋ Q ⟨ ψ `⟨⅋ᵈ Q
  (P ∎) `⟨⅋ᵈ Q = (P `⅋ Q) ∎

  _`⅋⟩ᵈ_ : (P : Formula) → Q IsDerivableFrom Q′ → (P `⅋ Q) IsDerivableFrom (P `⅋ Q′)
  P `⅋⟩ᵈ (Q ⟶⟨ φ ⟩ ψ) = P `⅋ Q ⟶⟨ P `⅋⟩ φ ⟩ P `⅋⟩ᵈ ψ
  P `⅋⟩ᵈ (Q ∼⟨ φ ⟩ ψ) = P `⅋ Q ∼⟨ P `⅋⟩ φ ⟩ P `⅋⟩ᵈ ψ
  P `⅋⟩ᵈ (Q ∼⟨ φ ⟨ ψ) = P `⅋ Q ∼⟨ P `⅋⟩ φ ⟨ P `⅋⟩ᵈ ψ
  P `⅋⟩ᵈ (Q ∎) = P `⅋ Q ∎

  _`⟨◁ᵈ_ : P IsDerivableFrom P′ → (Q : Formula) → (P `◁ Q) IsDerivableFrom (P′ `◁ Q)
  (P ⟶⟨ φ ⟩ ψ) `⟨◁ᵈ Q = P `◁ Q ⟶⟨ φ `⟨◁ Q ⟩ ψ `⟨◁ᵈ Q
  (P ∼⟨ φ ⟩ ψ) `⟨◁ᵈ Q = P `◁ Q ∼⟨ φ `⟨◁ Q ⟩ ψ `⟨◁ᵈ Q
  (P ∼⟨ φ ⟨ ψ) `⟨◁ᵈ Q = P `◁ Q ∼⟨ φ `⟨◁ Q ⟨ ψ `⟨◁ᵈ Q
  (P ∎) `⟨◁ᵈ Q = (P `◁ Q) ∎

  _`◁⟩ᵈ_ : (P : Formula) → Q IsDerivableFrom Q′ → (P `◁ Q) IsDerivableFrom (P `◁ Q′)
  P `◁⟩ᵈ (Q ⟶⟨ φ ⟩ ψ) = P `◁ Q ⟶⟨ P `◁⟩ φ ⟩ P `◁⟩ᵈ ψ
  P `◁⟩ᵈ (Q ∼⟨ φ ⟩ ψ) = P `◁ Q ∼⟨ P `◁⟩ φ ⟩ P `◁⟩ᵈ ψ
  P `◁⟩ᵈ (Q ∼⟨ φ ⟨ ψ) = P `◁ Q ∼⟨ P `◁⟩ φ ⟨ P `◁⟩ᵈ ψ
  P `◁⟩ᵈ (Q ∎) = P `◁ Q ∎

  _`⟨&ᵈ_ : P IsDerivableFrom P′ → (Q : Formula) → (P `& Q) IsDerivableFrom (P′ `& Q)
  (P ⟶⟨ φ ⟩ ψ) `⟨&ᵈ Q = P `& Q ⟶⟨ φ `⟨& Q ⟩ ψ `⟨&ᵈ Q
  (P ∼⟨ φ ⟩ ψ) `⟨&ᵈ Q = P `& Q ∼⟨ φ `⟨& Q ⟩ ψ `⟨&ᵈ Q
  (P ∼⟨ φ ⟨ ψ) `⟨&ᵈ Q = P `& Q ∼⟨ φ `⟨& Q ⟨ ψ `⟨&ᵈ Q
  (P ∎) `⟨&ᵈ Q = (P `& Q) ∎

  _`&⟩ᵈ_ : (P : Formula) → Q IsDerivableFrom Q′ → (P `& Q) IsDerivableFrom (P `& Q′)
  P `&⟩ᵈ (Q ⟶⟨ φ ⟩ ψ) = P `& Q ⟶⟨ P `&⟩ φ ⟩ P `&⟩ᵈ ψ
  P `&⟩ᵈ (Q ∼⟨ φ ⟩ ψ) = P `& Q ∼⟨ P `&⟩ φ ⟩ P `&⟩ᵈ ψ
  P `&⟩ᵈ (Q ∼⟨ φ ⟨ ψ) = P `& Q ∼⟨ P `&⟩ φ ⟨ P `&⟩ᵈ ψ
  P `&⟩ᵈ (Q ∎) = P `& Q ∎

  _`⟨⊕ᵈ_ : P IsDerivableFrom P′ → (Q : Formula) → (P `⊕ Q) IsDerivableFrom (P′ `⊕ Q)
  (P ⟶⟨ φ ⟩ ψ) `⟨⊕ᵈ Q = P `⊕ Q ⟶⟨ φ `⟨⊕ Q ⟩ ψ `⟨⊕ᵈ Q
  (P ∼⟨ φ ⟩ ψ) `⟨⊕ᵈ Q = P `⊕ Q ∼⟨ φ `⟨⊕ Q ⟩ ψ `⟨⊕ᵈ Q
  (P ∼⟨ φ ⟨ ψ) `⟨⊕ᵈ Q = P `⊕ Q ∼⟨ φ `⟨⊕ Q ⟨ ψ `⟨⊕ᵈ Q
  (P ∎) `⟨⊕ᵈ Q = (P `⊕ Q) ∎

  _`⊕⟩ᵈ_ : (P : Formula) → Q IsDerivableFrom Q′ → (P `⊕ Q) IsDerivableFrom (P `⊕ Q′)
  P `⊕⟩ᵈ (Q ⟶⟨ φ ⟩ ψ) = P `⊕ Q ⟶⟨ P `⊕⟩ φ ⟩ P `⊕⟩ᵈ ψ
  P `⊕⟩ᵈ (Q ∼⟨ φ ⟩ ψ) = P `⊕ Q ∼⟨ P `⊕⟩ φ ⟩ P `⊕⟩ᵈ ψ
  P `⊕⟩ᵈ (Q ∼⟨ φ ⟨ ψ) = P `⊕ Q ∼⟨ P `⊕⟩ φ ⟨ P `⊕⟩ᵈ ψ
  P `⊕⟩ᵈ (Q ∎) = P `⊕ Q ∎

  from-⟶ᶜ : P ⟶ᶜ Q → P IsDerivableFrom Q
  from-⟶ᶜ (emb φ) = from-⟶ φ
  from-⟶ᶜ (φ `⟨⊗ Q) = from-⟶ᶜ φ `⟨⊗ᵈ Q
  from-⟶ᶜ (P `⊗⟩ φ) = P `⊗⟩ᵈ from-⟶ᶜ φ
  from-⟶ᶜ (φ `⟨⅋ Q) = from-⟶ᶜ φ `⟨⅋ᵈ Q
  from-⟶ᶜ (P `⅋⟩ φ) = P `⅋⟩ᵈ from-⟶ᶜ φ
  from-⟶ᶜ (φ `⟨◁ Q) = from-⟶ᶜ φ `⟨◁ᵈ Q
  from-⟶ᶜ (P `◁⟩ φ) = P `◁⟩ᵈ from-⟶ᶜ φ
  from-⟶ᶜ (φ `⟨& Q) = from-⟶ᶜ φ `⟨&ᵈ Q
  from-⟶ᶜ (P `&⟩ φ) = P `&⟩ᵈ from-⟶ᶜ φ
  from-⟶ᶜ (φ `⟨⊕ Q) = from-⟶ᶜ φ `⟨⊕ᵈ Q
  from-⟶ᶜ (P `⊕⟩ φ) = P `⊕⟩ᵈ from-⟶ᶜ φ

  from-⟶₌ : P ⟶₌ Q → P IsDerivableFrom Q
  from-⟶₌ (inj₁ φ) = from-≃ φ
  from-⟶₌ (inj₂ φ) = from-⟶ᶜ φ

  from-⟶⋆ : P MAV.⟶⋆ Q → P IsDerivableFrom Q
  from-⟶⋆ {P} {.P} ε       = P ∎
  from-⟶⋆ {P} { Q} (φ ◅ ψ) = trans (from-⟶₌ φ) (from-⟶⋆ ψ)
    where
      trans : Transitive _IsDerivableFrom_
      trans (P ⟶⟨ φ ⟩ ψ′) ψ = P ⟶⟨ φ ⟩ trans ψ′ ψ
      trans (P ∼⟨ φ ⟩ ψ′) ψ = P ∼⟨ φ ⟩ trans ψ′ ψ
      trans (P ∼⟨ φ ⟨ ψ′) ψ = P ∼⟨ φ ⟨ trans ψ′ ψ
      trans (P ∎) ψ = ψ

  from : P MAV.⟶⋆ Q → P ⟶⋆ Q
  from φ = begin from-⟶⋆ φ

  to : P IsDerivableFrom Q → P MAV.⟶⋆ Q
  to (_ ⟶⟨ φ ⟩ ψ) = inj₂ φ ◅ to ψ
  to (_ ∼⟨ φ ⟩ ψ) = inj₁ (SymClosure.fwd φ ◅ ε) ◅ to ψ
  to (_ ∼⟨ φ ⟨ ψ) = inj₁ (SymClosure.bwd φ ◅ ε) ◅ to ψ
  to (_ ∎) = ε

open MAV public using (_⟶⋆_)
open Deep public hiding (_⟶⋆_; begin_)

infix 1 begin_

begin_ : _IsDerivableFrom_ ⇒ _⟶⋆_
begin φ = to φ
