module MAV.Base.Reasoning {a} (Atom : Set a) where

open import Level using (suc)
open import Data.Sum using (inj₁; inj₂)
open import Function using (flip)
open import MAV.Frame
open import MAV.Formula Atom
open import MAV.Base Atom
open import Relation.Binary
open import Relation.Binary.Definitions using (Reflexive; Trans)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (ε; _◅_; _◅◅_)
import Relation.Binary.Construct.Closure.Equivalence as EqClosure
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)

module ⟶⋆ = IsPartialOrder ⟶⋆-isPartialOrder

private
  variable
    P P′ : Formula
    Q Q′ : Formula
    R R′ : Formula
    S S′ : Formula

infix 4 _IsRelatedTo_

data _IsRelatedTo_ (P Q : Formula) : Set (suc a) where
  infers     : (P⟶Q : P ⟶ Q) → P IsRelatedTo Q
  derives    : (P⟶⋆Q : P ⟶⋆ Q) → P IsRelatedTo Q
  equals-fwd : (P∼Q : P ∼ Q) → P IsRelatedTo Q
  equals-bwd : (Q∼P : Q ∼ P) → P IsRelatedTo Q
  equals     : (P≃Q : P ≃ Q) → P IsRelatedTo Q

infix 1 begin_

begin_ : _IsRelatedTo_ ⇒ _⟶⋆_
begin (infers P⟶Q) = step P⟶Q ◅ ε
begin (derives P⟶⋆Q) = P⟶⋆Q
begin (equals-fwd P∼Q) = fwd P∼Q ◅ ε
begin (equals-bwd Q∼P) = bwd Q∼P ◅ ε
begin (equals P≃Q) = emb (inj₁ P≃Q) ◅ ε

infixr 2 ≡-step

≡-step : P ≡ Q → Q IsRelatedTo R → P IsRelatedTo R
≡-step ≡.refl Q-R = Q-R

syntax ≡-step P Q-R P≡Q = P ≡⟨ P≡Q ⟩ Q-R

infixr 2 ⟶-step

⟶-step : P ⟶ Q → Q IsRelatedTo R → P IsRelatedTo R
⟶-step P⟶Q Q-R = derives (step P⟶Q ◅ (begin Q-R))

syntax ⟶-step P Q-R P⟶Q = P ⟶⟨ P⟶Q ⟩ Q-R

infixr 2 ⟶⋆-step

⟶⋆-step : P ⟶⋆ Q → Q IsRelatedTo R → P IsRelatedTo R
⟶⋆-step P⟶⋆Q Q-R = derives (P⟶⋆Q ◅◅ (begin Q-R))

syntax ⟶⋆-step P Q-R P⟶⋆Q = P ⟶⋆⟨ P⟶⋆Q ⟩ Q-R

infixr 2 ∼-step-fwd

∼-step-fwd : P ∼ Q → Q IsRelatedTo R → P IsRelatedTo R
∼-step-fwd P∼Q Q-R = derives (fwd P∼Q ◅ (begin Q-R))

syntax ∼-step-fwd P Q-R P∼Q = P ∼⟨ P∼Q ⟩ Q-R

infixr 2 ∼-step-bwd

∼-step-bwd : Q ∼ P → Q IsRelatedTo R → P IsRelatedTo R
∼-step-bwd Q∼P Q-R = derives (bwd Q∼P ◅ (begin Q-R))

syntax ∼-step-bwd P Q-R Q∼P = P ∼⟨ Q∼P ⟨ Q-R

infixr 2 ≃-step-fwd

≃-step-fwd : P ≃ Q → Q IsRelatedTo R → P IsRelatedTo R
≃-step-fwd P≃Q Q-R = derives (emb (inj₁ P≃Q) ◅ (begin Q-R))

syntax ≃-step-fwd P Q-R P≃Q = P ≃⟨ P≃Q ⟩ Q-R

infixr 2 ≃-step-bwd

≃-step-bwd : Q ≃ P → Q IsRelatedTo R → P IsRelatedTo R
≃-step-bwd Q≃P Q-R = derives (emb (inj₁ (EqClosure.symmetric _ Q≃P)) ◅ (begin Q-R))

syntax ≃-step-bwd P Q-R P≃Q = P ≃⟨ P≃Q ⟨ Q-R

infix 3 _∎

_∎ : Reflexive _IsRelatedTo_
_∎ = derives ⟶⋆.refl
 