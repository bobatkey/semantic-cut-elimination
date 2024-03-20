{-# OPTIONS --postfix-projections --safe --without-K #-}

module MAV.Base (Atom : Set) where

open import Algebra.Ordered.Structures.Duoidal
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (0ℓ; lift; lower; Lift; suc)
open import Relation.Binary using (IsPartialOrder; Poset)
open import Relation.Binary.Construct.Core.Symmetric using (SymCore)
import Relation.Binary.Construct.Core.Symmetric as SymCore
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
  -- `⊗-unit    : P `⊗ `I ⟶ P
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

  -- _`⟨⊕_      : P ⟶ P′ → (Q : Formula) → (P `⊕ Q) ⟶ (P′ `⊕ Q)
  -- _`⊕⟩_      : (P : Formula) → Q ⟶ Q′ → (P `⊕ Q) ⟶ (P `⊕ Q′)

------------------------------------------------------------------------------
-- Turning the proof system into a pre-order

open import Algebra.Ordered

infix 5 _⟶*_

_⟶*_ : Formula → Formula → Set
_⟶*_ = Star _⟶_

infix 5 _⟷*_

_⟷*_ : Formula → Formula → Set
_⟷*_ = SymCore _⟶*_

⟶*-isPartialOrder : IsPartialOrder _⟷*_ _⟶*_
⟶*-isPartialOrder = SymCore.isPreorder⇒isPartialOrder _⟶*_ (Star.isPreorder _⟶_)

open IsPartialOrder ⟶*-isPartialOrder
  using ()
  renaming (trans to ⟶*-trans)

⟶*-Poset : Poset 0ℓ 0ℓ 0ℓ
⟶*-Poset .Poset.Carrier = Formula
⟶*-Poset .Poset._≈_ = _⟷*_
⟶*-Poset .Poset._≤_ = _⟶*_
⟶*-Poset .Poset.isPartialOrder = ⟶*-isPartialOrder

------------------------------------------------------------------------------
-- Turning ⊗ into a commutative pomonoid

_`⊗⟩*_ : (P : Formula) → Q ⟶* Q′ → (P `⊗ Q) ⟶* (P `⊗ Q′)
P `⊗⟩* ε = ε
P `⊗⟩* (x ◅ ϕ) = (P `⊗⟩ x) ◅ (P `⊗⟩* ϕ)

-- _`⟨⊗*_ : P ⟶* P′ → (Q : Formula) →  (P `⊗ Q) ⟶* (P′ `⊗ Q)
-- ε       `⟨⊗* Q = ε
-- (x ◅ ϕ) `⟨⊗* Q = (x `⟨⊗ Q) ◅ (ϕ `⟨⊗* Q)

-- `⊗-mono : (P ⟶* P′) → (Q ⟶* Q′) → (P `⊗ Q) ⟶* (P′ `⊗ Q′)
-- `⊗-mono {P = P} {Q′ = Q′} f g = ⟶*-trans (P `⊗⟩* g) (f `⟨⊗* Q′)

-- `⊗-isPomagma : IsPomagma _⟷*_ _⟶*_ _`⊗_
-- `⊗-isPomagma .IsPomagma.isPartialOrder = ⟶*-isPartialOrder
-- `⊗-isPomagma .IsPomagma.mono = `⊗-mono

-- `⊗-isPosemigroup : IsPosemigroup  _⟷*_ _⟶*_ _`⊗_
-- `⊗-isPosemigroup .IsPosemigroup.isPomagma = `⊗-isPomagma
-- `⊗-isPosemigroup .IsPosemigroup.assoc P Q R = (`⊗-assoc⁻¹ ◅ ε , `⊗-assoc ◅ ε)

-- `⊗-isPomonoid : IsPomonoid _⟷*_ _⟶*_ _`⊗_ `I
-- `⊗-isPomonoid .IsPomonoid.isPosemigroup = `⊗-isPosemigroup
-- `⊗-isPomonoid .IsPomonoid.identity = 
--   (λ P → (`⊗-comm ◅ `⊗-unit ◅ ε , `⊗-unit⁻¹ ◅ `⊗-comm ◅ ε)) ,
--   (λ P → (`⊗-unit ◅ ε , `⊗-unit⁻¹ ◅ ε))

-- `⊗-isCommutativePomonoid : IsCommutativePomonoid  _⟷*_ _⟶*_ _`⊗_ `I
-- `⊗-isCommutativePomonoid .IsCommutativePomonoid.isPomonoid = `⊗-isPomonoid
-- `⊗-isCommutativePomonoid .IsCommutativePomonoid.comm P Q = (`⊗-comm ◅ ε , `⊗-comm ◅ ε)

------------------------------------------------------------------------------
-- Turning ⅋ into a commutative pomonoid

_`⅋⟩*_ : (P : Formula) → Q ⟶* Q′ → (P `⅋ Q) ⟶* (P `⅋ Q′)
P `⅋⟩* ε = ε
P `⅋⟩* (x ◅ ϕ) = (P `⅋⟩ x) ◅ (P `⅋⟩* ϕ)

_`⟨⅋*_ : P ⟶* P′ → (Q : Formula) →  (P `⅋ Q) ⟶* (P′ `⅋ Q)
ε       `⟨⅋* Q = ε
(x ◅ ϕ) `⟨⅋* Q = (x `⟨⅋ Q) ◅ (ϕ `⟨⅋* Q)

`⅋-mono : (P ⟶* P′) → (Q ⟶* Q′) → (P `⅋ Q) ⟶* (P′ `⅋ Q′)
`⅋-mono {P = P} {Q′ = Q′} f g = ⟶*-trans (P `⅋⟩* g) (f `⟨⅋* Q′)

`⅋-isPomagma : IsPomagma _⟷*_ _⟶*_ _`⅋_
`⅋-isPomagma .IsPomagma.isPartialOrder = ⟶*-isPartialOrder
`⅋-isPomagma .IsPomagma.mono = `⅋-mono

`⅋-isPosemigroup : IsPosemigroup  _⟷*_ _⟶*_ _`⅋_
`⅋-isPosemigroup .IsPosemigroup.isPomagma = `⅋-isPomagma
`⅋-isPosemigroup .IsPosemigroup.assoc P Q R = (`⅋-assoc⁻¹ ◅ ε , `⅋-assoc ◅ ε)

`⅋-isPomonoid : IsPomonoid _⟷*_ _⟶*_ _`⅋_ `I
`⅋-isPomonoid .IsPomonoid.isPosemigroup = `⅋-isPosemigroup
`⅋-isPomonoid .IsPomonoid.identity =
  (λ P → (`⅋-comm ◅ `⅋-unit ◅ ε , `⅋-unit⁻¹ ◅ `⅋-comm ◅ ε)) ,
  (λ P → (`⅋-unit ◅ ε , `⅋-unit⁻¹ ◅ ε))

`⅋-isCommutativePomonoid : IsCommutativePomonoid  _⟷*_ _⟶*_ _`⅋_ `I
`⅋-isCommutativePomonoid .IsCommutativePomonoid.isPomonoid = `⅋-isPomonoid
`⅋-isCommutativePomonoid .IsCommutativePomonoid.comm P Q = (`⅋-comm ◅ ε , `⅋-comm ◅ ε)



------------------------------------------------------------------------------
-- Turning ▷ into a pomonoid

_`▷⟩*_ : (P : Formula) → Q ⟶* Q′ → P `▷ Q ⟶* P `▷ Q′
P `▷⟩* ε = ε
P `▷⟩* (x ◅ ϕ) = (P `▷⟩ x) ◅ (P `▷⟩* ϕ)

_`⟨▷*_ : P ⟶* P′ → (Q : Formula) → P `▷ Q ⟶* P′ `▷ Q
ε       `⟨▷* Q = ε
(x ◅ ϕ) `⟨▷* Q = (x `⟨▷ Q) ◅ (ϕ `⟨▷* Q)

`▷-mono : (P ⟶* P′) → (Q ⟶* Q′) → (P `▷ Q) ⟶* (P′ `▷ Q′)
`▷-mono {P = P} {Q′ = Q′} f g = ⟶*-trans (P `▷⟩* g) (f `⟨▷* Q′)

`▷-isPomagma : IsPomagma _⟷*_ _⟶*_ _`▷_
`▷-isPomagma .IsPomagma.isPartialOrder = ⟶*-isPartialOrder
`▷-isPomagma .IsPomagma.mono = `▷-mono

`▷-isPosemigroup : IsPosemigroup  _⟷*_ _⟶*_ _`▷_
`▷-isPosemigroup .IsPosemigroup.isPomagma = `▷-isPomagma
`▷-isPosemigroup .IsPosemigroup.assoc P Q R = (`▷-assoc⁻¹ ◅ ε , `▷-assoc ◅ ε)

`▷-isPomonoid : IsPomonoid _⟷*_ _⟶*_ _`▷_ `I
`▷-isPomonoid .IsPomonoid.isPosemigroup = `▷-isPosemigroup
`▷-isPomonoid .IsPomonoid.identity = 
  (λ P → (`▷-lunit ◅ ε , `▷-lunit⁻¹ ◅ ε)) ,
  (λ P → (`▷-runit ◅ ε , `▷-runit⁻¹ ◅ ε))

------------------------------------------------------------------------------
-- Turning ⅋ and ▷ into a duoid

`⅋-`▷-isDuoidal : IsDuoidal _⟷*_ _⟶*_ _`⅋_ _`▷_ `I `I
`⅋-`▷-isDuoidal .IsDuoidal.∙-isPomonoid = `⅋-isPomonoid
`⅋-`▷-isDuoidal .IsDuoidal.▷-isPomonoid = `▷-isPomonoid
`⅋-`▷-isDuoidal .IsDuoidal.∙-▷-entropy w x y z = `sequence ◅ ε
`⅋-`▷-isDuoidal .IsDuoidal.∙-idem-ι = `⅋-unit ◅ ε
`⅋-`▷-isDuoidal .IsDuoidal.▷-idem-ε = `▷-lunit⁻¹ ◅ ε -- or `▷-runit⁻¹ ◅ ε
`⅋-`▷-isDuoidal .IsDuoidal.ε≲ι = ε

------------------------------------------------------------------------------
-- Turning & into a pomagma

_`&⟩*_ : (P : Formula) → Q ⟶* Q′ → P `& Q ⟶* P `& Q′
P `&⟩* ε = ε
P `&⟩* (x ◅ ϕ) = (P `&⟩ x) ◅ (P `&⟩* ϕ)

_`⟨&*_ : P ⟶* P′ → (Q : Formula) → (P `& Q) ⟶* (P′ `& Q)
ε       `⟨&* Q = ε
(x ◅ ϕ) `⟨&* Q = (x `⟨& Q) ◅ (ϕ `⟨&* Q)

`&-mono : P ⟶* P′ → Q ⟶* Q′ → P `& Q ⟶* P′ `& Q′
`&-mono {P = P} {Q′ = Q′} f g = ⟶*-trans (P `&⟩* g) (f `⟨&* Q′)

`&-isPomagma : IsPomagma _⟷*_ _⟶*_ _`&_
`&-isPomagma .IsPomagma.isPartialOrder = ⟶*-isPartialOrder
`&-isPomagma .IsPomagma.mono = `&-mono

`&-Pomagma : Pomagma 0ℓ 0ℓ 0ℓ
`&-Pomagma = record { isPomagma = `&-isPomagma }

------------------------------------------------------------------------------
-- Turning ⊕ into a pomagma

-- _`⊕⟩*_ : (P : Formula) → Q ⟶* Q′ → P `⊕ Q ⟶* P `⊕ Q′
-- P `⊕⟩* ε = ε
-- P `⊕⟩* (x ◅ ϕ) = (P `⊕⟩ x) ◅ (P `⊕⟩* ϕ)

-- _`⟨⊕*_ : P ⟶* P′ → (Q : Formula) → (P `⊕ Q) ⟶* (P′ `⊕ Q)
-- ε       `⟨⊕* Q = ε
-- (x ◅ ϕ) `⟨⊕* Q = (x `⟨⊕ Q) ◅ (ϕ `⟨⊕* Q)

-- `⊕-mono : P ⟶* P′ → Q ⟶* Q′ → P `⊕ Q ⟶* P′ `⊕ Q′
-- `⊕-mono {P = P} {Q′ = Q′} f g = ⟶*-trans (P `⊕⟩* g) (f `⟨⊕* Q′)

-- `⊕-isPomagma : IsPomagma _⟷*_ _⟶*_ _`⊕_
-- `⊕-isPomagma .IsPomagma.isPartialOrder = ⟶*-isPartialOrder
-- `⊕-isPomagma .IsPomagma.mono = `⊕-mono
