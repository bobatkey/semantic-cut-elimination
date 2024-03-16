{-# OPTIONS --postfix-projections --safe --without-K #-}

module MAV.Base (Atom : Set) where

open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (0ℓ; lift; lower; Lift; suc)
open import Prelude
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties as Star

open import MAV.Formula Atom

private
  variable
    A A′ : Atom
    P P′ : Formula
    Q Q′ : Formula
    R R′ : Formula
    S S′ : Formula

infix 5 _⟶_

-- One step of the “analytic” proof system
data _⟶_ : Formula → Formula → Set where
  `axiom    : `+ A `⅋ `- A ⟶ `I

  `tidy     : `I `& `I ⟶ `I
  `switch   : (P `⊗ Q) `⅋ R ⟶ P `⊗ (Q `⅋ R)
  `sequence : (P `▷ Q) `⅋ (R `▷ S) ⟶ (P `⅋ R) `▷ (Q `⅋ S)
  `left     : P `⊕ Q ⟶ P
  `right    : P `⊕ Q ⟶ Q
  `external : (P `& Q) `⅋ R ⟶ (P `⅋ R) `& (Q `⅋ R)
  `medial   : (P `▷ Q) `& (R `▷ S) ⟶ (P `& R) `▷ (Q `& S)

  -- _`⟨⊗_      : P ⟶ P′ → (Q : Formula) → P `⊗ Q ⟶ P′ `⊗ Q
  _`⊗⟩_      : (P : Formula) → Q ⟶ Q′ → P `⊗ Q ⟶ P `⊗ Q′
  -- `⊗-assoc   : P `⊗ (Q `⊗ R) ⟶ (P `⊗ Q) `⊗ R
  -- `⊗-assoc⁻¹ : (P `⊗ Q) `⊗ R ⟶ P `⊗ (Q `⊗ R)
  `⊗-comm    : P `⊗ Q ⟶ Q `⊗ P
  `⊗-unit    : P `⊗ `I ⟶ P
  -- `⊗-unit⁻¹  : P ⟶ (P `⊗ `I)

  _`⟨⅋_      : P ⟶ P′ → (Q : Formula) → (P `⅋ Q) ⟶ (P′ `⅋ Q)
  _`⅋⟩_      : (P : Formula) → Q ⟶ Q′ → (P `⅋ Q) ⟶ (P `⅋ Q′)
  `⅋-assoc   : (P `⅋ (Q `⅋ R)) ⟶ ((P `⅋ Q) `⅋ R)
  `⅋-assoc⁻¹ : ((P `⅋ Q) `⅋ R) ⟶ (P `⅋ (Q `⅋ R))
  `⅋-comm    : (P `⅋ Q) ⟶ (Q `⅋ P)
  `⅋-unit    : (P `⅋ `I) ⟶ P
  `⅋-unit⁻¹  : P ⟶ (P `⅋ `I)

  _`⟨▷_      : P ⟶ P′ → (Q : Formula) → (P `▷ Q) ⟶ (P′ `▷ Q)
  _`▷⟩_      : (P : Formula) → Q ⟶ Q′ → (P `▷ Q) ⟶ (P `▷ Q′)
  `▷-assoc   : (P `▷ (Q `▷ R)) ⟶ ((P `▷ Q) `▷ R)
  `▷-assoc⁻¹ : ((P `▷ Q) `▷ R) ⟶ (P `▷ (Q `▷ R))
  `▷-runit   : (P `▷ `I) ⟶ P
  `▷-runit⁻¹ : P ⟶ (P `▷ `I)
  `▷-lunit   : (`I `▷ P) ⟶ P
  `▷-lunit⁻¹ : P ⟶ (`I `▷ P)

  _`⟨&_      : P ⟶ P′ → (Q : Formula) → (P `& Q) ⟶ (P′ `& Q)
  _`&⟩_      : (P : Formula) → Q ⟶ Q′ → (P `& Q) ⟶ (P `& Q′)


infix  5 _⟶*_

_⟶*_ : Formula → Formula → Set
_⟶*_ = Star _⟶_

------------------------------------------------------------------------------
-- Turning the proof system into A pre-order

⟶*-refl : ∀ {P} → P ⟶* P
⟶*-refl = ε

⟶*-trans : P ⟶* Q → Q ⟶* R → P ⟶* R
⟶*-trans ε           q⟶*R = q⟶*R
⟶*-trans (x ◅ p⟶*Q) q⟶*R = x ◅ ⟶*-trans p⟶*Q q⟶*R

⟶*-isPreorder : IsPreorder _⟶*_
⟶*-isPreorder .IsPreorder.refl = ⟶*-refl
⟶*-isPreorder .IsPreorder.trans = ⟶*-trans

-- ⅋ is A monoid in the proof system
_`⅋⟩*_ : (P : Formula) → Q ⟶* Q′ → (P `⅋ Q) ⟶* (P `⅋ Q′)
P `⅋⟩* ε = ε
P `⅋⟩* (x ◅ ϕ) = (P `⅋⟩ x) ◅ (P `⅋⟩* ϕ)

_`⟨⅋*_ : P ⟶* P′ → (Q : Formula) →  (P `⅋ Q) ⟶* (P′ `⅋ Q)
ε       `⟨⅋* Q = ε
(x ◅ ϕ) `⟨⅋* Q = (x `⟨⅋ Q) ◅ (ϕ `⟨⅋* Q)

`⅋-mono : (P ⟶* P′) → (Q ⟶* Q′) → (P `⅋ Q) ⟶* (P′ `⅋ Q′)
`⅋-mono {P = P} {Q′ = Q′} f g = ⟶*-trans (P `⅋⟩* g) (f `⟨⅋* Q′)

`⅋-isMonoid : IsMonoid ⟶*-isPreorder _`⅋_ `I
`⅋-isMonoid .IsMonoid.mono = `⅋-mono
`⅋-isMonoid .IsMonoid.assoc = `⅋-assoc⁻¹ ◅ ε , `⅋-assoc ◅ ε
`⅋-isMonoid .IsMonoid.lunit = `⅋-comm ◅ `⅋-unit ◅ ε , `⅋-unit⁻¹ ◅ `⅋-comm ◅ ε
`⅋-isMonoid .IsMonoid.runit = `⅋-unit ◅ ε , `⅋-unit⁻¹ ◅ ε

`⅋-sym : P `⅋ Q ⟶* Q `⅋ P
`⅋-sym = `⅋-comm ◅ ε

-- ▷ is A monoid in the proof system
_`▷⟩*_ : (P : Formula) → Q ⟶* Q′ → P `▷ Q ⟶* P `▷ Q′
P `▷⟩* ε = ε
P `▷⟩* (x ◅ ϕ) = (P `▷⟩ x) ◅ (P `▷⟩* ϕ)

_`⟨▷*_ : P ⟶* P′ → (Q : Formula) → P `▷ Q ⟶* P′ `▷ Q
ε       `⟨▷* Q = ε
(x ◅ ϕ) `⟨▷* Q = (x `⟨▷ Q) ◅ (ϕ `⟨▷* Q)

`▷-mono : (P ⟶* P′) → (Q ⟶* Q′) → (P `▷ Q) ⟶* (P′ `▷ Q′)
`▷-mono {P = P} {Q′ = Q′} f g = ⟶*-trans (P `▷⟩* g) (f `⟨▷* Q′)

`▷-isMonoid : IsMonoid ⟶*-isPreorder _`▷_ `I
`▷-isMonoid .IsMonoid.mono = `▷-mono
`▷-isMonoid .IsMonoid.assoc = `▷-assoc⁻¹ ◅ ε , `▷-assoc ◅ ε
`▷-isMonoid .IsMonoid.lunit = `▷-lunit ◅ ε , `▷-lunit⁻¹ ◅ ε
`▷-isMonoid .IsMonoid.runit = `▷-runit ◅ ε , `▷-runit⁻¹ ◅ ε

⅋-`▷-isDuoidal : IsDuoidal ⟶*-isPreorder `⅋-isMonoid `▷-isMonoid
⅋-`▷-isDuoidal .IsDuoidal.exchange = `sequence ◅ ε
⅋-`▷-isDuoidal .IsDuoidal.mu = `⅋-unit ◅ ε

-- & is A monotone operator
_`&⟩*_ : (P : Formula) → Q ⟶* Q′ → P `& Q ⟶* P `& Q′
P `&⟩* ε = ε
P `&⟩* (x ◅ ϕ) = (P `&⟩ x) ◅ (P `&⟩* ϕ)

_`⟨&*_ : P ⟶* P′ → (Q : Formula) → (P `& Q) ⟶* (P′ `& Q)
ε       `⟨&* Q = ε
(x ◅ ϕ) `⟨&* Q = (x `⟨& Q) ◅ (ϕ `⟨&* Q)

`&-mono : P ⟶* P′ → Q ⟶* Q′ → P `& Q ⟶* P′ `& Q′
`&-mono {P = P} {Q′ = Q′} f g = ⟶*-trans (P `&⟩* g) (f `⟨&* Q′)

-- _⊗_ is A monotone operator
_`⊗⟩*_ : (P : Formula) → Q ⟶* Q′ → (P `⊗ Q) ⟶* (P `⊗ Q′)
P `⊗⟩* ε = ε
P `⊗⟩* (x ◅ ϕ) = (P `⊗⟩ x) ◅ (P `⊗⟩* ϕ)

-- _`⟨⊗*_ : P ⟶* P′ → (Q : Formula) → (P `⊗ Q) ⟶* (P′ `⊗ Q)
-- ε       `⟨⊗* Q = ε
-- (x ◅ ϕ) `⟨⊗* Q = (x `⟨⊗ Q) ◅ (ϕ `⟨⊗* Q)
