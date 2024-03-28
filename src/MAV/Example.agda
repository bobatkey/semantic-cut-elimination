{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Data.Empty using (⊥)
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_; _◅◅_)
open import Relation.Binary.Construct.Closure.Symmetric

module MAV.Example where

Atom : Set
Atom = ⊥

open import MAV.Formula Atom
open import MAV.CutElim Atom using (cut-elim)
-- import MAV.Base Atom as MAV
import MAV.Base.Reasoning Atom as MAV
import MAV.Symmetric Atom as SMAV

-- An example:
--
--  Normalising A proof that (`I `⊕ `I) `◁ (`I `& `I) ⊸ (`I `⊕ `I) `◁ (`I `& `I):

example₁ : Formula
example₁ = (`I `⊕ `I) `◁ (`I `& `I)

SMAV-proof-of-example₁ : (example₁ `⅋ `¬ example₁) SMAV.⟶⋆ `I
SMAV-proof-of-example₁ = SMAV.step (`axiom example₁) ◅ ε
  where open SMAV

MAV-proof-of-example₁ : (example₁ `⅋ `¬ example₁) MAV.⟶⋆ `I
MAV-proof-of-example₁ =
  begin 
    ((`I `⊕ `I) `◁ (`I `& `I)) `⅋ ((`I `& `I) `◁ (`I `⊕ `I)) 
  ∼⟨ emb (`⅋-comm ((`I `& `I) `◁ (`I `⊕ `I)) ((`I `⊕ `I) `◁ (`I `& `I))) ⟨
    ((`I `& `I) `◁ (`I `⊕ `I)) `⅋ ((`I `⊕ `I) `◁ (`I `& `I)) 
  ∼⟨ emb (`⅋-comm ((`I `⊕ `I) `◁ (`I `& `I)) ((`I `& `I) `◁ (`I `⊕ `I))) ⟨
    ((`I `⊕ `I) `◁ (`I `& `I)) `⅋ ((`I `& `I) `◁ (`I `⊕ `I)) 
  ∼⟨ emb (`⅋-comm ((`I `& `I) `◁ (`I `⊕ `I)) ((`I `⊕ `I) `◁ (`I `& `I))) ⟨
    ((`I `& `I) `◁ (`I `⊕ `I)) `⅋ ((`I `⊕ `I) `◁ (`I `& `I)) 
  ∼⟨ emb (`⅋-comm ((`I `⊕ `I) `◁ (`I `& `I)) ((`I `& `I) `◁ (`I `⊕ `I))) ⟨
    ((`I `⊕ `I) `◁ (`I `& `I)) `⅋ ((`I `& `I) `◁ (`I `⊕ `I)) 
  ∼⟨ emb (`⅋-comm ((`I `& `I) `◁ (`I `⊕ `I)) ((`I `⊕ `I) `◁ (`I `& `I))) ⟨
    ((`I `& `I) `◁ (`I `⊕ `I)) `⅋ ((`I `⊕ `I) `◁ (`I `& `I)) 
  ∼⟨ emb (`⅋-comm ((`I `⊕ `I) `◁ (`I `& `I)) ((`I `& `I) `◁ (`I `⊕ `I))) ⟨
    ((`I `⊕ `I) `◁ (`I `& `I)) `⅋ ((`I `& `I) `◁ (`I `⊕ `I)) 
  ∼⟨ emb (`⅋-comm ((`I `& `I) `◁ (`I `⊕ `I)) ((`I `⊕ `I) `◁ (`I `& `I))) ⟨
    ((`I `& `I) `◁ (`I `⊕ `I)) `⅋ ((`I `⊕ `I) `◁ (`I `& `I)) 
  ∼⟨ emb (`⅋-comm ((`I `⊕ `I) `◁ (`I `& `I)) ((`I `& `I) `◁ (`I `⊕ `I))) ⟨
    ((`I `⊕ `I) `◁ (`I `& `I)) `⅋ ((`I `& `I) `◁ (`I `⊕ `I)) 
  ∼⟨ emb (`⅋-comm ((`I `& `I) `◁ (`I `⊕ `I)) ((`I `⊕ `I) `◁ (`I `& `I))) ⟨
    ((`I `& `I) `◁ (`I `⊕ `I)) `⅋ ((`I `⊕ `I) `◁ (`I `& `I)) 
  ∼⟨ emb (`⅋-comm ((`I `⊕ `I) `◁ (`I `& `I)) ((`I `& `I) `◁ (`I `⊕ `I))) ⟨
    ((`I `⊕ `I) `◁ (`I `& `I)) `⅋ ((`I `& `I) `◁ (`I `⊕ `I)) 
  ∼⟨ emb (`⅋-comm ((`I `& `I) `◁ (`I `⊕ `I)) ((`I `⊕ `I) `◁ (`I `& `I))) ⟨
    ((`I `& `I) `◁ (`I `⊕ `I)) `⅋ ((`I `⊕ `I) `◁ (`I `& `I))
  ⟶⟨ emb `sequence ⟩
    ((`I `& `I) `⅋ (`I `⊕ `I)) `◁ ((`I `⊕ `I) `⅋ (`I `& `I)) 
  ∼⟨ emb (`⅋-comm (`I `⊕ `I) (`I `& `I)) `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I)) ⟨
    ((`I `⊕ `I) `⅋ (`I `& `I)) `◁ ((`I `⊕ `I) `⅋ (`I `& `I)) 
  ∼⟨ emb (`⅋-comm (`I `& `I) (`I `⊕ `I)) `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I)) ⟨
    ((`I `& `I) `⅋ (`I `⊕ `I)) `◁ ((`I `⊕ `I) `⅋ (`I `& `I))
  ⟶⟨ emb `external `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I)) ⟩
    ((`I `⅋ (`I `⊕ `I)) `& (`I `⅋ (`I `⊕ `I))) `◁ ((`I `⊕ `I) `⅋ (`I `& `I)) 
  ∼⟨ ((`I `⅋ (`I `⊕ `I)) `&⟩ emb (`⅋-comm (`I `⊕ `I) `I)) `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I)) ⟨
    ((`I `⅋ (`I `⊕ `I)) `& ((`I `⊕ `I) `⅋ `I)) `◁ ((`I `⊕ `I) `⅋ (`I `& `I)) 
  ∼⟨ ((`I `⅋ (`I `⊕ `I)) `&⟩ emb (`⅋-comm `I (`I `⊕ `I))) `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I)) ⟨
    ((`I `⅋ (`I `⊕ `I)) `& (`I `⅋ (`I `⊕ `I))) `◁ ((`I `⊕ `I) `⅋ (`I `& `I)) 
  ∼⟨ ((`I `⅋ (`I `⊕ `I)) `&⟩ emb (`⅋-comm `I (`I `⊕ `I))) `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I)) ⟩
    ((`I `⅋ (`I `⊕ `I)) `& ((`I `⊕ `I) `⅋ `I)) `◁ ((`I `⊕ `I) `⅋ (`I `& `I)) 
  ∼⟨ ((`I `⅋ (`I `⊕ `I)) `&⟩ emb (`⅋-identityʳ (`I `⊕ `I))) `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I)) ⟩
    ((`I `⅋ (`I `⊕ `I)) `& (`I `⊕ `I)) `◁ ((`I `⊕ `I) `⅋ (`I `& `I)) 
  ∼⟨ (emb (`⅋-comm (`I `⊕ `I) `I) `⟨& (`I `⊕ `I)) `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I)) ⟨
    (((`I `⊕ `I) `⅋ `I) `& (`I `⊕ `I)) `◁ ((`I `⊕ `I) `⅋ (`I `& `I)) 
  ∼⟨ (emb (`⅋-comm `I (`I `⊕ `I)) `⟨& (`I `⊕ `I)) `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I)) ⟨
    ((`I `⅋ (`I `⊕ `I)) `& (`I `⊕ `I)) `◁ ((`I `⊕ `I) `⅋ (`I `& `I)) 
  ∼⟨ (emb (`⅋-comm `I (`I `⊕ `I)) `⟨& (`I `⊕ `I)) `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I)) ⟩
    (((`I `⊕ `I) `⅋ `I) `& (`I `⊕ `I)) `◁ ((`I `⊕ `I) `⅋ (`I `& `I)) 
  ∼⟨ (emb (`⅋-identityʳ (`I `⊕ `I)) `⟨& (`I `⊕ `I)) `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I)) ⟩
    ((`I `⊕ `I) `& (`I `⊕ `I)) `◁ ((`I `⊕ `I) `⅋ (`I `& `I))
  ⟶⟨ ((`I `⊕ `I) `&⟩ emb `right) `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I)) ⟩
    ((`I `⊕ `I) `& `I) `◁ ((`I `⊕ `I) `⅋ (`I `& `I))
  ⟶⟨ (emb `left `⟨& `I) `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I)) ⟩
    (`I `& `I) `◁ ((`I `⊕ `I) `⅋ (`I `& `I))
  ⟶⟨ emb `tidy `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I)) ⟩
    `I `◁ ((`I `⊕ `I) `⅋ (`I `& `I)) 
  ∼⟨ emb (`◁-identityˡ ((`I `⊕ `I) `⅋ (`I `& `I))) ⟩
    (`I `⊕ `I) `⅋ (`I `& `I) 
  ∼⟨ emb (`⅋-comm (`I `& `I) (`I `⊕ `I)) ⟨
    (`I `& `I) `⅋ (`I `⊕ `I)
  ⟶⟨ emb `external ⟩
    (`I `⅋ (`I `⊕ `I)) `& (`I `⅋ (`I `⊕ `I)) 
  ∼⟨ (`I `⅋ (`I `⊕ `I)) `&⟩ emb (`⅋-comm (`I `⊕ `I) `I) ⟨
    (`I `⅋ (`I `⊕ `I)) `& ((`I `⊕ `I) `⅋ `I)
  ⟶⟨ (`I `⅋ (`I `⊕ `I)) `&⟩ (emb `right `⟨⅋ `I) ⟩
    (`I `⅋ (`I `⊕ `I)) `& (`I `⅋ `I) 
  ∼⟨ (`I `⅋ (`I `⊕ `I)) `&⟩ emb (`⅋-comm `I `I) ⟩
    (`I `⅋ (`I `⊕ `I)) `& (`I `⅋ `I) 
  ∼⟨ (`I `⅋ (`I `⊕ `I)) `&⟩ emb (`⅋-identityʳ `I) ⟩
    (`I `⅋ (`I `⊕ `I)) `& `I 
  ∼⟨ emb (`⅋-comm (`I `⊕ `I) `I) `⟨& `I ⟨
    ((`I `⊕ `I) `⅋ `I) `& `I
  ⟶⟨ (emb `left `⟨⅋ `I) `⟨& `I ⟩
    (`I `⅋ `I) `& `I 
  ∼⟨ emb (`⅋-comm `I `I) `⟨& `I ⟩
    (`I `⅋ `I) `& `I 
  ∼⟨ emb (`⅋-identityʳ `I) `⟨& `I ⟩
    `I `& `I
  ⟶⟨ emb `tidy ⟩
    `I
  ∎
  where open MAV

_ : cut-elim _ SMAV-proof-of-example₁ ≡ MAV-proof-of-example₁
_ = refl
