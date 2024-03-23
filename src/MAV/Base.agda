{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Algebra using (_DistributesOver_)
open import Algebra.Ordered
open import Algebra.Ordered.Structures.Duoidal using (IsDuoidal)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Level using (0ℓ; lift; lower; Lift; suc)
open import Relation.Binary using (IsPartialOrder; Poset)
open import Relation.Binary.Construct.Core.Symmetric using (SymCore)
import Relation.Binary.Construct.Core.Symmetric as SymCore
open import Relation.Binary.Construct.Closure.Equivalence using (EqClosure)
import Relation.Binary.Construct.Closure.Equivalence as EqClosure
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties as StarProps
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl)

module MAV.Base {a} (Atom : Set a) where

open import MAV.Frame
open import MAV.Formula Atom

private
  variable
    A A′ : Atom
    B B′ : Atom
    P P′ : Formula
    Q Q′ : Formula
    R R′ : Formula
    S S′ : Formula
  
infix 5 _⟶_

-- One step of the “analytic” proof system
data _⟶_ : Formula → Formula → Set a where
  `axiom    : `- A `⅋ `+ A ⟶ `I

  `tidy     : `I `& `I ⟶ `I
  `switch   : .{{NonUnit P}} → .{{NonUnit R}} → 
              (P `⊗ Q) `⅋ R ⟶ P `⊗ (Q `⅋ R)
  `sequence : -- .{{NonUnit P}} → .{{NonUnit S}} → 
              (P `▷ Q) `⅋ (R `▷ S) ⟶ (P `⅋ R) `▷ (Q `⅋ S)
  `left     : P `⊕ Q ⟶ P
  `right    : P `⊕ Q ⟶ Q
  `external : -- .{{NonUnit R}} →
              (P `& Q) `⅋ R ⟶ (P `⅋ R) `& (Q `⅋ R)
  `medial   : -- .{{NonUnit P ⊎ NonUnit R}} → .{{NonUnit Q ⊎ NonUnit S}} →
              (P `▷ Q) `& (R `▷ S) ⟶ (P `& R) `▷ (Q `& S)

  _`⟨⊗_      : P ⟶ P′ → (Q : Formula) → P `⊗ Q ⟶ P′ `⊗ Q
  _`⊗⟩_      : (P : Formula) → Q ⟶ Q′ → P `⊗ Q ⟶ P `⊗ Q′
  -- `⊗-assoc   : P `⊗ (Q `⊗ R) ⟶ (P `⊗ Q) `⊗ R
  -- `⊗-assoc⁻¹ : (P `⊗ Q) `⊗ R ⟶ P `⊗ (Q `⊗ R)
  `⊗-comm    : P `⊗ Q ⟶ Q `⊗ P
  `⊗-unit    : P `⊗ `I ⟶ P
  `⊗-unit⁻¹  : P ⟶ (P `⊗ `I)

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

infix 5 _⟶⋆_

_⟶⋆_ : Formula → Formula → Set a
_⟶⋆_ = Star _⟶_

infix 5 _⟷⋆_

_⟷⋆_ : Formula → Formula → Set a
_⟷⋆_ = SymCore _⟶⋆_

⟶⋆-isPartialOrder : IsPartialOrder _⟷⋆_ _⟶⋆_
⟶⋆-isPartialOrder = SymCore.isPreorder⇒isPartialOrder _⟶⋆_ (StarProps.isPreorder _⟶_)

⟶⋆-Poset : Poset a a a
⟶⋆-Poset .Poset.Carrier = Formula
⟶⋆-Poset .Poset._≈_ = _⟷⋆_
⟶⋆-Poset .Poset._≤_ = _⟶⋆_
⟶⋆-Poset .Poset.isPartialOrder = ⟶⋆-isPartialOrder

------------------------------------------------------------------------------
-- Lift congruence rules to the preorder

_`⊗⟩⋆_ : (P : Formula) → Q ⟶⋆ Q′ → (P `⊗ Q) ⟶⋆ (P `⊗ Q′)
P `⊗⟩⋆ Q⟶⋆Q′ = Star.gmap _ (P `⊗⟩_) Q⟶⋆Q′

_`⟨⊗⋆_ : P ⟶⋆ P′ → (Q : Formula) → P `⊗ Q ⟶⋆ P′ `⊗ Q
P⟶⋆P′ `⟨⊗⋆ Q = Star.gmap _ (_`⟨⊗ Q) P⟶⋆P′

-- _`⟨⊗⋆_ : P ⟶⋆ P′ → (Q : Formula) → P `⊗ Q ⟶⋆ P′ `⊗ Q
-- f `⟨⊗⋆ Q = `⊗-comm ◅ Q `⊗⟩⋆ f ◅◅ `⊗-comm ◅ ε

_`⅋⟩⋆_ : (P : Formula) → Q ⟶⋆ Q′ → (P `⅋ Q) ⟶⋆ (P `⅋ Q′)
P `⅋⟩⋆ Q⟶⋆Q′ = Star.gmap _ (P `⅋⟩_) Q⟶⋆Q′

_`⟨⅋⋆_ : P ⟶⋆ P′ → (Q : Formula) → P `⅋ Q ⟶⋆ P′ `⅋ Q
P⟶⋆P′ `⟨⅋⋆ Q = Star.gmap _ (_`⟨⅋ Q) P⟶⋆P′

-- _`⟨⅋⋆_ : P ⟶⋆ P′ → (Q : Formula) → P `⅋ Q ⟶⋆ P′ `⅋ Q
-- f `⟨⅋⋆ Q = `⅋-comm ◅ Q `⅋⟩⋆ f ◅◅ `⅋-comm ◅ ε

_`▷⟩⋆_ : (P : Formula) → Q ⟶⋆ Q′ → (P `▷ Q) ⟶⋆ (P `▷ Q′)
P `▷⟩⋆ Q⟶⋆Q′ = Star.gmap _ (P `▷⟩_) Q⟶⋆Q′

_`⟨▷⋆_ : P ⟶⋆ P′ → (Q : Formula) → P `▷ Q ⟶⋆ P′ `▷ Q
P⟶⋆P′ `⟨▷⋆ Q = Star.gmap _ (_`⟨▷ Q) P⟶⋆P′

_`&⟩⋆_ : (P : Formula) → Q ⟶⋆ Q′ → (P `& Q) ⟶⋆ (P `& Q′)
P `&⟩⋆ Q⟶⋆Q′ = Star.gmap _ (P `&⟩_) Q⟶⋆Q′

_`⟨&⋆_ : P ⟶⋆ P′ → (Q : Formula) → P `& Q ⟶⋆ P′ `& Q
P⟶⋆P′ `⟨&⋆ Q = Star.gmap _ (_`⟨& Q) P⟶⋆P′

------------------------------------------------------------------------------
-- Deriving full versions of switch and sequence

`switch⋆ : (P `⊗ Q) `⅋ R ⟶⋆ P `⊗ (Q `⅋ R)
`switch⋆ {P} {Q} {R} with P ≟`I | R ≟`I 
... |     P≟`I | yes refl = `⅋-unit ◅ P `⊗⟩ `⅋-unit⁻¹ ◅ ε
... | yes refl | no  R≢`I = `⊗-comm `⟨⅋ R ◅ `⊗-unit `⟨⅋ R ◅ `⊗-unit⁻¹ ◅ `⊗-comm ◅ ε
... | no  P≢`I | no  R≢`I = `switch {{≢-nonUnit P≢`I}} {{≢-nonUnit R≢`I}} ◅ ε

`sequence⋆ : (P `▷ Q) `⅋ (R `▷ S) ⟶⋆ (P `⅋ R) `▷ (Q `⅋ S)
`sequence⋆ = `sequence ◅ ε
-- `sequence⋆ {P} {Q} {R} {S} with P ≟`I | S ≟`I
-- ... | yes refl |     S≟`I = `▷-lunit `⟨⅋ (R `▷ S) ◅ {!   !} ◅ ε
-- ... | no  P≢`I | yes refl = {!   !}
-- ... | no  P≢`I | no  S≢`I = `sequence {{≢-nonUnit P≢`I}} {{≢-nonUnit S≢`I}} ◅ ε

------------------------------------------------------------------------------
-- Turning ⊗ into a commutative pomonoid

-- `⊗-mono : (P ⟶⋆ P′) → (Q ⟶⋆ Q′) → (P `⊗ Q) ⟶⋆ (P′ `⊗ Q′)
-- `⊗-mono {P = P} {Q′ = Q′} f g = ⟶⋆-trans (P `⊗⟩⋆ g) (f `⟨⊗⋆ Q′)

-- `⊗-isPomagma : IsPomagma _⟷⋆_ _⟶⋆_ _`⊗_
-- `⊗-isPomagma .IsPomagma.isPartialOrder = ⟶⋆-isPartialOrder
-- `⊗-isPomagma .IsPomagma.mono = `⊗-mono

-- `⊗-isPosemigroup : IsPosemigroup  _⟷⋆_ _⟶⋆_ _`⊗_
-- `⊗-isPosemigroup .IsPosemigroup.isPomagma = `⊗-isPomagma
-- `⊗-isPosemigroup .IsPosemigroup.assoc P Q R = (`⊗-assoc⁻¹ ◅ ε , `⊗-assoc ◅ ε)

-- `⊗-isPomonoid : IsPomonoid _⟷⋆_ _⟶⋆_ _`⊗_ `I
-- `⊗-isPomonoid .IsPomonoid.isPosemigroup = `⊗-isPosemigroup
-- `⊗-isPomonoid .IsPomonoid.identity = 
--   (λ P → (`⊗-comm ◅ `⊗-unit ◅ ε , `⊗-unit⁻¹ ◅ `⊗-comm ◅ ε)) ,
--   (λ P → (`⊗-unit ◅ ε , `⊗-unit⁻¹ ◅ ε))

-- `⊗-isCommutativePomonoid : IsCommutativePomonoid  _⟷⋆_ _⟶⋆_ _`⊗_ `I
-- `⊗-isCommutativePomonoid .IsCommutativePomonoid.isPomonoid = `⊗-isPomonoid
-- `⊗-isCommutativePomonoid .IsCommutativePomonoid.comm P Q = (`⊗-comm ◅ ε , `⊗-comm ◅ ε)

------------------------------------------------------------------------------
-- Turning ⅋ into a commutative pomonoid

`⅋-mono : (P ⟶⋆ P′) → (Q ⟶⋆ Q′) → (P `⅋ Q) ⟶⋆ (P′ `⅋ Q′)
`⅋-mono {P = P} {Q′ = Q′} f g = P `⅋⟩⋆ g ◅◅ f `⟨⅋⋆ Q′

`⅋-isPomagma : IsPomagma _⟷⋆_ _⟶⋆_ _`⅋_
`⅋-isPomagma .IsPomagma.isPartialOrder = ⟶⋆-isPartialOrder
`⅋-isPomagma .IsPomagma.mono = `⅋-mono

`⅋-isPosemigroup : IsPosemigroup  _⟷⋆_ _⟶⋆_ _`⅋_
`⅋-isPosemigroup .IsPosemigroup.isPomagma = `⅋-isPomagma
`⅋-isPosemigroup .IsPosemigroup.assoc P Q R = (`⅋-assoc⁻¹ ◅ ε , `⅋-assoc ◅ ε)

`⅋-isPomonoid : IsPomonoid _⟷⋆_ _⟶⋆_ _`⅋_ `I
`⅋-isPomonoid .IsPomonoid.isPosemigroup = `⅋-isPosemigroup
`⅋-isPomonoid .IsPomonoid.identity =
  (λ P → (`⅋-comm ◅ `⅋-unit ◅ ε , `⅋-unit⁻¹ ◅ `⅋-comm ◅ ε)) ,
  (λ P → (`⅋-unit ◅ ε , `⅋-unit⁻¹ ◅ ε))

`⅋-isCommutativePomonoid : IsCommutativePomonoid  _⟷⋆_ _⟶⋆_ _`⅋_ `I
`⅋-isCommutativePomonoid .IsCommutativePomonoid.isPomonoid = `⅋-isPomonoid
`⅋-isCommutativePomonoid .IsCommutativePomonoid.comm P Q = (`⅋-comm ◅ ε , `⅋-comm ◅ ε)

------------------------------------------------------------------------------
-- Turning ▷ into a pomonoid

`▷-mono : (P ⟶⋆ P′) → (Q ⟶⋆ Q′) → (P `▷ Q) ⟶⋆ (P′ `▷ Q′)
`▷-mono {P = P} {Q′ = Q′} f g = P `▷⟩⋆ g ◅◅ f `⟨▷⋆ Q′

`▷-isPomagma : IsPomagma _⟷⋆_ _⟶⋆_ _`▷_
`▷-isPomagma .IsPomagma.isPartialOrder = ⟶⋆-isPartialOrder
`▷-isPomagma .IsPomagma.mono = `▷-mono

`▷-isPosemigroup : IsPosemigroup  _⟷⋆_ _⟶⋆_ _`▷_
`▷-isPosemigroup .IsPosemigroup.isPomagma = `▷-isPomagma
`▷-isPosemigroup .IsPosemigroup.assoc P Q R = (`▷-assoc⁻¹ ◅ ε , `▷-assoc ◅ ε)

`▷-isPomonoid : IsPomonoid _⟷⋆_ _⟶⋆_ _`▷_ `I
`▷-isPomonoid .IsPomonoid.isPosemigroup = `▷-isPosemigroup
`▷-isPomonoid .IsPomonoid.identity = 
  (λ P → (`▷-lunit ◅ ε , `▷-lunit⁻¹ ◅ ε)) ,
  (λ P → (`▷-runit ◅ ε , `▷-runit⁻¹ ◅ ε))

------------------------------------------------------------------------------
-- Turning ⅋ and ▷ into a duoid

`⅋-`▷-isDuoidal : IsDuoidal _⟷⋆_ _⟶⋆_ _`⅋_ _`▷_ `I `I
`⅋-`▷-isDuoidal .IsDuoidal.∙-isPomonoid = `⅋-isPomonoid
`⅋-`▷-isDuoidal .IsDuoidal.▷-isPomonoid = `▷-isPomonoid
`⅋-`▷-isDuoidal .IsDuoidal.∙-▷-entropy w x y z = `sequence⋆
`⅋-`▷-isDuoidal .IsDuoidal.∙-idem-ι = `⅋-unit ◅ ε
`⅋-`▷-isDuoidal .IsDuoidal.▷-idem-ε = `▷-lunit⁻¹ ◅ ε -- or `▷-runit⁻¹ ◅ ε
`⅋-`▷-isDuoidal .IsDuoidal.ε≲ι = ε

------------------------------------------------------------------------------
-- Turning & into a pomagma

`&-mono : P ⟶⋆ P′ → Q ⟶⋆ Q′ → P `& Q ⟶⋆ P′ `& Q′
`&-mono {P = P} {Q′ = Q′} f g = P `&⟩⋆ g ◅◅ f `⟨&⋆ Q′

`&-isPomagma : IsPomagma _⟷⋆_ _⟶⋆_ _`&_
`&-isPomagma .IsPomagma.isPartialOrder = ⟶⋆-isPartialOrder
`&-isPomagma .IsPomagma.mono = `&-mono

`&-Pomagma : Pomagma a a a
`&-Pomagma = record { isPomagma = `&-isPomagma }

-- FIXME: should probably have a left-external and a right-external
`⅋-distrib-`& : _DistributesOver_ _⟶⋆_ _`⅋_ _`&_
`⅋-distrib-`& .proj₁ x y z = `⅋-comm ◅ `external ◅ `&-mono (`⅋-comm ◅ ε) (`⅋-comm ◅ ε)
`⅋-distrib-`& .proj₂ x y z = `external ◅ ε

`&-`▷-entropy : Entropy _⟶⋆_ _`&_ _`▷_
`&-`▷-entropy w x y z = `medial ◅ ε

------------------------------------------------------------------------------
-- Turning ⊕ into a pomagma

-- `⊕-mono : P ⟶⋆ P′ → Q ⟶⋆ Q′ → P `⊕ Q ⟶⋆ P′ `⊕ Q′
-- `⊕-mono {P = P} {Q′ = Q′} f g = P `⊕⟩⋆ g ◅◅ f `⟨⊕⋆ Q′

-- `⊕-isPomagma : IsPomagma _⟷⋆_ _⟶⋆_ _`⊕_
-- `⊕-isPomagma .IsPomagma.isPartialOrder = ⟶⋆-isPartialOrder
-- `⊕-isPomagma .IsPomagma.mono = `⊕-mono

------------------------------------------------------------------------------
frame : Frame a a a
frame .Frame.Carrier = Formula
frame .Frame._≈_ = _⟷⋆_
frame .Frame._≲_ = _⟶⋆_
frame .Frame.I = `I
frame .Frame._⅋_ = _`⅋_
frame .Frame._▷_ = _`▷_
frame .Frame._&_ = _`&_
frame .Frame.⅋-isCommutativePomonoid = `⅋-isCommutativePomonoid
frame .Frame.&-mono = `&-mono
frame .Frame.⅋-▷-isDuoidal = `⅋-`▷-isDuoidal
frame .Frame.⅋-distrib-& = `⅋-distrib-`&
frame .Frame.&-▷-entropy = `&-`▷-entropy
frame .Frame.&-tidy = `tidy ◅ ε
 