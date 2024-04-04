{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Data.Empty using (⊥)
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_; _◅◅_)
open import Relation.Binary.Construct.Closure.Symmetric

module MAUV.Example where

Atom : Set
Atom = ⊥

open import MAUV.Structure Atom
open import MAUV.CutElim Atom using (cut-elim)
import MAUV.Base.Reasoning Atom as MAUV
import MAUV.Symmetric Atom as SMAUV

-- An example:
--
--  Normalising A proof that (`I `⊕ `I) `◁ (`I `& `I) ⊸ (`I `⊕ `I) `◁ (`I `& `I):

example₁ : Structure
example₁ = (`I `⊕ `I) `◁ (`I `& `I)

SMAUV-proof-of-example₁ : (example₁ `⅋ `¬ example₁) SMAUV.⟶⋆ `I
SMAUV-proof-of-example₁ = SMAUV.step (`axiom example₁) ◅ ε
  where open SMAUV

-- MAUV-proof-of-example₁ : (example₁ `⅋ `¬ example₁) MAUV.Deep.⟶⋆ `I
MAUV-proof-of-example₁ : (example₁ `⅋ `¬ example₁) MAUV.⟶⋆ `I
MAUV-proof-of-example₁ = 
  -- {! Deep.to (cut-elim _ SMAUV-proof-of-example₁) !}
  begin
    ((`I `⊕ `I) `◁ (`I `& `I)) `⅋ ((`I `& `I) `◁ (`I `⊕ `I)) 
  ∼⟨ emb `⅋-comm ⟨ 
    ((`I `& `I) `◁ (`I `⊕ `I)) `⅋ ((`I `⊕ `I) `◁ (`I `& `I)) 
  ∼⟨ emb `⅋-comm ⟨ 
    ((`I `⊕ `I) `◁ (`I `& `I)) `⅋ ((`I `& `I) `◁ (`I `⊕ `I)) 
  ∼⟨ emb `⅋-comm ⟨ 
    ((`I `& `I) `◁ (`I `⊕ `I)) `⅋ ((`I `⊕ `I) `◁ (`I `& `I)) 
  ∼⟨ emb `⅋-comm ⟨ 
    ((`I `⊕ `I) `◁ (`I `& `I)) `⅋ ((`I `& `I) `◁ (`I `⊕ `I)) 
  ∼⟨ emb `⅋-comm ⟨ 
    ((`I `& `I) `◁ (`I `⊕ `I)) `⅋ ((`I `⊕ `I) `◁ (`I `& `I)) 
  ∼⟨ emb `⅋-comm ⟨ 
    ((`I `⊕ `I) `◁ (`I `& `I)) `⅋ ((`I `& `I) `◁ (`I `⊕ `I)) 
  ∼⟨ emb `⅋-comm ⟨ 
    ((`I `& `I) `◁ (`I `⊕ `I)) `⅋ ((`I `⊕ `I) `◁ (`I `& `I)) 
  ∼⟨ emb `⅋-comm ⟨ 
    ((`I `⊕ `I) `◁ (`I `& `I)) `⅋ ((`I `& `I) `◁ (`I `⊕ `I)) 
  ∼⟨ emb `⅋-comm ⟨ 
    ((`I `& `I) `◁ (`I `⊕ `I)) `⅋ ((`I `⊕ `I) `◁ (`I `& `I)) 
  ∼⟨ emb `⅋-comm ⟨ 
    ((`I `⊕ `I) `◁ (`I `& `I)) `⅋ ((`I `& `I) `◁ (`I `⊕ `I)) 
  ∼⟨ emb `⅋-comm ⟨ 
    ((`I `& `I) `◁ (`I `⊕ `I)) `⅋ ((`I `⊕ `I) `◁ (`I `& `I))
  ⟶⟨ emb `sequence ⟩
      ((`I `& `I) `⅋ (`I `⊕ `I)) `◁ ((`I `⊕ `I) `⅋ (`I `& `I)) 
  ∼⟨ emb `⅋-comm `⟨◁ ⟨ 
    ((`I `⊕ `I) `⅋ (`I `& `I)) `◁ ((`I `⊕ `I) `⅋ (`I `& `I)) 
  ∼⟨ emb `⅋-comm `⟨◁ ⟨ 
    ((`I `& `I) `⅋ (`I `⊕ `I)) `◁ ((`I `⊕ `I) `⅋ (`I `& `I))
  ⟶⟨ emb `external `⟨◁ ⟩
      ((`I `⅋ (`I `⊕ `I)) `& (`I `⅋ (`I `⊕ `I))) `◁  ((`I `⊕ `I) `⅋ (`I `& `I))  
  ∼⟨ (`&⟩ emb `⅋-comm) `⟨◁ ⟨ 
    ((`I `⅋ (`I `⊕ `I)) `& ((`I `⊕ `I) `⅋ `I)) `◁  ((`I `⊕ `I) `⅋ (`I `& `I))  
  ∼⟨ (`&⟩ emb `⅋-comm) `⟨◁ ⟨ 
    ((`I `⅋ (`I `⊕ `I)) `& (`I `⅋ (`I `⊕ `I))) `◁  ((`I `⊕ `I) `⅋ (`I `& `I))  
  ∼⟨ (`&⟩ emb `⅋-comm) `⟨◁ ⟩
    ((`I `⅋ (`I `⊕ `I)) `& ((`I `⊕ `I) `⅋ `I)) `◁  ((`I `⊕ `I) `⅋ (`I `& `I))  
  ∼⟨ (`&⟩ emb `⅋-identityʳ) `⟨◁ ⟩
    ((`I `⅋ (`I `⊕ `I)) `& (`I `⊕ `I)) `◁ ((`I `⊕ `I) `⅋ (`I `& `I))  
  ∼⟨ (emb `⅋-comm `⟨&) `⟨◁ ⟨ 
    (((`I `⊕ `I) `⅋ `I) `& (`I `⊕ `I)) `◁ ((`I `⊕ `I) `⅋ (`I `& `I))  
  ∼⟨ (emb `⅋-comm `⟨&) `⟨◁ ⟨ 
    ((`I `⅋ (`I `⊕ `I)) `& (`I `⊕ `I)) `◁ ((`I `⊕ `I) `⅋ (`I `& `I))  
  ∼⟨ (emb `⅋-comm `⟨&) `⟨◁ ⟩
    (((`I `⊕ `I) `⅋ `I) `& (`I `⊕ `I)) `◁ ((`I `⊕ `I) `⅋ (`I `& `I))  
  ∼⟨ (emb `⅋-identityʳ `⟨&) `⟨◁ ⟩
    ((`I `⊕ `I) `& (`I `⊕ `I)) `◁ ((`I `⊕ `I) `⅋ (`I `& `I))
  ⟶⟨ (`&⟩ emb `right) `⟨◁ ⟩
    ((`I `⊕ `I) `& `I) `◁ ((`I `⊕ `I) `⅋ (`I `& `I))
  ⟶⟨ (emb `left `⟨&) `⟨◁ ⟩ 
    (`I `& `I) `◁ ((`I `⊕ `I) `⅋ (`I `& `I))
  ⟶⟨ emb `tidy `⟨◁ ⟩
    `I `◁ ((`I `⊕ `I) `⅋ (`I `& `I)) 
  ∼⟨ emb `◁-identityˡ ⟩
    (`I `⊕ `I) `⅋ (`I `& `I) 
  ∼⟨ emb `⅋-comm ⟨ 
    (`I `& `I) `⅋ (`I `⊕ `I)
  ⟶⟨ emb `external ⟩
      (`I `⅋ (`I `⊕ `I)) `& (`I `⅋ (`I `⊕ `I)) 
  ∼⟨ `&⟩ emb `⅋-comm  ⟨ 
    (`I `⅋ (`I `⊕ `I)) `& ((`I `⊕ `I) `⅋ `I)
  ⟶⟨ `&⟩ (emb `right `⟨⅋) ⟩
    (`I `⅋ (`I `⊕ `I)) `& (`I `⅋ `I) 
  ∼⟨ `&⟩ emb `⅋-comm ⟩
    (`I `⅋ (`I `⊕ `I)) `& (`I `⅋ `I) 
  ∼⟨ `&⟩ emb `⅋-identityʳ ⟩
    (`I `⅋ (`I `⊕ `I)) `& `I 
  ∼⟨ emb `⅋-comm `⟨& ⟨ 
    ((`I `⊕ `I) `⅋ `I) `& `I
  ⟶⟨ (emb `left `⟨⅋) `⟨& ⟩
    (`I `⅋ `I) `& `I 
  ∼⟨ emb `⅋-comm `⟨& ⟩
    (`I `⅋ `I) `& `I 
  ∼⟨ emb `⅋-identityʳ `⟨& ⟩
    `I `& `I
  ⟶⟨ emb `tidy ⟩
    `I
  ∎
  -- where open MAUV.Deep
  where open MAUV

_ : cut-elim _ SMAUV-proof-of-example₁ ≡ MAUV-proof-of-example₁
_ = refl
