{-# OPTIONS --postfix-projections --safe --without-K #-}

module MAV.Example where

open import Data.Empty using (⊥)
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_; _◅◅_)

Atom : Set
Atom = ⊥

open import MAV.Formula Atom
open import MAV.CutElim Atom using (cut-elim)
import MAV.Base Atom as MAV
import MAV.Symmetric Atom as SMAV

-- An example:
--
--  Normalising A proof that (`I `⊕ `I) `◁ (`I `& `I) ⊸ (`I `⊕ `I) `◁ (`I `& `I):

example₁ : Formula
example₁ = (`I `⊕ `I) `◁ (`I `& `I)

SMAV-proof-of-example₁ : (example₁ `⅋ `¬ example₁) SMAV.⟶⋆ `I
SMAV-proof-of-example₁ =
  SMAV.step (`axiom example₁) ◅ ε
  where open SMAV

MAV-proof-of-example₁ : (example₁ `⅋ `¬ example₁) MAV.⟶⋆ `I
MAV-proof-of-example₁
    = bwd (`⅋-comm ((`I `& `I) `◁ (`I `⊕ `I)) ((`I `⊕ `I) `◁ (`I `& `I)))
    ◅ bwd (`⅋-comm ((`I `⊕ `I) `◁ (`I `& `I)) ((`I `& `I) `◁ (`I `⊕ `I)))
    ◅ bwd (`⅋-comm ((`I `& `I) `◁ (`I `⊕ `I)) ((`I `⊕ `I) `◁ (`I `& `I)))
    ◅ bwd (`⅋-comm ((`I `⊕ `I) `◁ (`I `& `I)) ((`I `& `I) `◁ (`I `⊕ `I)))
    ◅ bwd (`⅋-comm ((`I `& `I) `◁ (`I `⊕ `I)) ((`I `⊕ `I) `◁ (`I `& `I)))
    ◅ bwd (`⅋-comm ((`I `⊕ `I) `◁ (`I `& `I)) ((`I `& `I) `◁ (`I `⊕ `I)))
    ◅ bwd (`⅋-comm ((`I `& `I) `◁ (`I `⊕ `I)) ((`I `⊕ `I) `◁ (`I `& `I)))
    ◅ bwd (`⅋-comm ((`I `⊕ `I) `◁ (`I `& `I)) ((`I `& `I) `◁ (`I `⊕ `I)))
    ◅ bwd (`⅋-comm ((`I `& `I) `◁ (`I `⊕ `I)) ((`I `⊕ `I) `◁ (`I `& `I)))
    ◅ bwd (`⅋-comm ((`I `⊕ `I) `◁ (`I `& `I)) ((`I `& `I) `◁ (`I `⊕ `I)))
    ◅ bwd (`⅋-comm ((`I `& `I) `◁ (`I `⊕ `I)) ((`I `⊕ `I) `◁ (`I `& `I)))
    ◅ step `sequence
    ◅ bwd (`⅋-comm (`I `⊕ `I) (`I `& `I)) `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I))
    ◅ bwd (`⅋-comm (`I `& `I) (`I `⊕ `I)) `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I))
    ◅ step `external `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I))
    ◅ ((`I `⅋ (`I `⊕ `I)) `&⟩ bwd (`⅋-comm (`I `⊕ `I) `I)) `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I))
    ◅ ((`I `⅋ (`I `⊕ `I)) `&⟩ bwd (`⅋-comm `I (`I `⊕ `I))) `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I))
    ◅ (((`I `⅋ (`I `⊕ `I)) `&⟩ fwd (`⅋-comm `I (`I `⊕ `I))) `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I))) 
    ◅ (((`I `⅋ (`I `⊕ `I)) `&⟩ fwd (`⅋-identityʳ (`I `⊕ `I))) `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I))) 
    ◅ (((`I `⅋ (`I `⊕ `I)) `&⟩ emb (inj₂ `right)) `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I))) 
    ◅ ((bwd (`⅋-comm (`I `⊕ `I) `I) `⟨& `I) `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I))) 
    ◅ ((bwd (`⅋-comm `I (`I `⊕ `I)) `⟨& `I) `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I))) 
    ◅ ((fwd (`⅋-comm `I (`I `⊕ `I)) `⟨& `I) `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I))) 
    ◅ ((fwd (`⅋-identityʳ (`I `⊕ `I)) `⟨& `I) `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I))) 
    ◅ (step `left `⟨& `I) `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I))
    ◅ step `tidy `⟨◁ ((`I `⊕ `I) `⅋ (`I `& `I))
    ◅ fwd (`◁-identityˡ ((`I `⊕ `I) `⅋ (`I `& `I)))
    ◅ bwd (`⅋-comm (`I `& `I) (`I `⊕ `I))
    ◅ step `external
    ◅ ((`I `⅋ (`I `⊕ `I)) `&⟩ bwd (`⅋-comm (`I `⊕ `I) `I))
    ◅ ((`I `⅋ (`I `⊕ `I)) `&⟩ (step `right `⟨⅋ `I))
    ◅ ((`I `⅋ (`I `⊕ `I)) `&⟩ fwd (`⅋-comm `I `I))
    ◅ ((`I `⅋ (`I `⊕ `I)) `&⟩ fwd (`⅋-identityʳ `I))
    ◅ (bwd (`⅋-comm (`I `⊕ `I) `I) `⟨& `I) 
    ◅ (step `left `⟨⅋ `I) `⟨& `I
    ◅ (fwd (`⅋-comm `I `I)) `⟨& `I
    ◅ (fwd (`⅋-identityʳ `I)) `⟨& `I
    ◅ step `tidy
    ◅ ε
    where open MAV

-- _ : cut-elim _ SMAV-proof-of-example₁ ≡ MAV-proof-of-example₁
-- _ = refl
 