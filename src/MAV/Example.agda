{-# OPTIONS --postfix-projections --safe --without-K #-}

module MAV.Example where

open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)

Atom : Set
Atom = ⊥

open import MAV.Formula Atom
open import MAV.CutElim Atom using (cut-elim)
import MAV.Base Atom as MAV
import MAV.Symmetric Atom as SMAV

-- An example:
--
--  Normalising A proof that (`I `⊕ `I) `▷ (`I `& `I) ⊸ (`I `⊕ `I) `▷ (`I `& `I):

example₁ : Formula
example₁ = (`I `⊕ `I) `▷ (`I `& `I)

SMAV-proof-of-example₁ : (example₁ `⅋ `¬ example₁) SMAV.⟶⋆ `I
SMAV-proof-of-example₁ =
  `axiom example₁ ◅ ε
  where open SMAV

MAV-proof-of-example₁ : (example₁ `⅋ `¬ example₁) MAV.⟶⋆ `I
MAV-proof-of-example₁ = -- {!cut-elim _ SMAV-proof-of-example₁!}
  `⅋-comm ◅
  `⅋-comm ◅
  `⅋-comm ◅
  `⅋-comm ◅
  `⅋-comm ◅
  `⅋-comm ◅
  `⅋-comm ◅
  `⅋-comm ◅
  `⅋-comm ◅
  `⅋-comm ◅
  `⅋-comm ◅
  `sequence ◅
  (`⅋-comm `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  (`⅋-comm `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  (`external `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  (((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-comm) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  (((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-comm) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  (((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-comm) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  (((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-unit) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  (((`I `⅋ (`I `⊕ `I)) `&⟩ `right) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  ((`⅋-comm `⟨& `I) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  ((`⅋-comm `⟨& `I) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  ((`⅋-comm `⟨& `I) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  ((`⅋-unit `⟨& `I) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  ((`left `⟨& `I) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  (`tidy `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  `▷-lunit ◅
  `⅋-comm ◅
  `external ◅
  ((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-comm) ◅
  ((`I `⅋ (`I `⊕ `I)) `&⟩ (`right `⟨⅋ `I)) ◅
  ((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-comm) ◅
  ((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-unit) ◅
  (`⅋-comm `⟨& `I) ◅
  ((`left `⟨⅋ `I) `⟨& `I) ◅
  (`⅋-comm `⟨& `I) ◅
  (`⅋-unit `⟨& `I) ◅
  `tidy ◅
  ε
  where open MAV

{-  `⅋-comm ◅
  `⅋-comm ◅
  `⅋-comm ◅
  `sequence ◅
  (`⅋-comm `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  (`⅋-comm `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  (`external `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  (((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-comm) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  (((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-comm) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  (((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-comm) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  (((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-unit) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  (((`I `⅋ (`I `⊕ `I)) `&⟩ `right) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  ((`⅋-comm `⟨& `I) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  ((`⅋-comm `⟨& `I) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  ((`⅋-comm `⟨& `I) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  ((`⅋-unit `⟨& `I) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  ((`left `⟨& `I) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  (`tidy `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
  `▷-lunit ◅
  `⅋-comm ◅
  `external ◅
  ((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-comm) ◅
  ((`I `⅋ (`I `⊕ `I)) `&⟩ (`right `⟨⅋ `I)) ◅
  ((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-comm) ◅
  ((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-unit) ◅
  (`⅋-comm `⟨& `I) ◅
  ((`left `⟨⅋ `I) `⟨& `I) ◅
  (`⅋-comm `⟨& `I) ◅ (`⅋-unit `⟨& `I) ◅ `tidy ◅ ε
  where open MAV
-}

_ : cut-elim _ SMAV-proof-of-example₁ ≡ MAV-proof-of-example₁
_ = refl
