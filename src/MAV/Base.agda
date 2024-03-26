{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Algebra.Definitions
open import Algebra.Ordered
open import Algebra.Ordered.Structures.Duoidal using (IsDuoidal)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Level using (suc; _⊔_)
open import Relation.Binary
open import Relation.Binary.Construct.Union using (_∪_)
import Relation.Binary.Construct.Union as Union
open import Relation.Binary.Construct.Core.Symmetric using (SymCore)
import Relation.Binary.Construct.Core.Symmetric as SymCore
open import Relation.Binary.Construct.Closure.Symmetric using (SymClosure)
import Relation.Binary.Construct.Closure.Symmetric as SymClosure
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties as StarProps
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_)
import Relation.Binary.PropositionalEquality.Core as PropEq
import Relation.Binary.Reasoning.PartialOrder as PartialOrderReasoning

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

module _ {ℓ} (_∼_ : Rel Formula ℓ) where
  mutual
    private
      _≅_ : Rel Formula (suc a ⊔ ℓ)
      _≅_ = CongClosure

    data CongClosure : Rel Formula (suc a ⊔ ℓ) where
      emb   : P ∼ P′ → P ≅ P′
      _`⟨⊗_ : P ≅ P′ → (Q : Formula) → (P `⊗ Q) ≅ (P′ `⊗ Q)
      _`⊗⟩_ : (P : Formula) → Q ≅ Q′ → (P `⊗ Q) ≅ (P `⊗ Q′)
      _`⟨⅋_ : P ≅ P′ → (Q : Formula) → (P `⅋ Q) ≅ (P′ `⅋ Q)
      _`⅋⟩_ : (P : Formula) → Q ≅ Q′ → (P `⅋ Q) ≅ (P `⅋ Q′)
      _`⟨◁_ : P ≅ P′ → (Q : Formula) → (P `◁ Q) ≅ (P′ `◁ Q)
      _`◁⟩_ : (P : Formula) → Q ≅ Q′ → (P `◁ Q) ≅ (P `◁ Q′)
      _`⟨&_ : P ≅ P′ → (Q : Formula) → (P `& Q) ≅ (P′ `& Q)
      _`&⟩_ : (P : Formula) → Q ≅ Q′ → (P `& Q) ≅ (P `& Q′)
      _`⟨⊕_ : P ≅ P′ → (Q : Formula) → (P `⊕ Q) ≅ (P′ `⊕ Q)
      _`⊕⟩_ : (P : Formula) → Q ≅ Q′ → (P `⊕ Q) ≅ (P `⊕ Q′)

infix 5 _∼_

data _∼_ : Rel Formula a where
  `⊗-assoc     : Associative _∼_ _`⊗_
  `⊗-comm      : Commutative _∼_ _`⊗_
  `⊗-identityʳ : RightIdentity _∼_ `I _`⊗_
  `⅋-assoc     : Associative _∼_ _`⅋_
  `⅋-comm      : Commutative _∼_ _`⅋_
  `⅋-identityʳ : RightIdentity _∼_ `I _`⅋_
  `◁-assoc     : Associative _∼_ _`◁_
  `◁-identityʳ : RightIdentity _∼_ `I _`◁_
  `◁-identityˡ : LeftIdentity _∼_ `I _`◁_
  
infix 5 _⟶_

-- One step of the “analytic” proof system
data _⟶_ : Formula → Formula → Set a where
  `axiom    : `- A `⅋ `+ A ⟶ `I

  `tidy     : `I `& `I ⟶ `I
  `switch   : (P `⊗ Q) `⅋ R ⟶ P `⊗ (Q `⅋ R)
  `sequence : (P `◁ Q) `⅋ (R `◁ S) ⟶ (P `⅋ R) `◁ (Q `⅋ S)
  `left     : P `⊕ Q ⟶ P
  `right    : P `⊕ Q ⟶ Q
  `external : (P `& Q) `⅋ R ⟶ (P `⅋ R) `& (Q `⅋ R)
  `medial   : (P `◁ Q) `& (R `◁ S) ⟶ (P `& R) `◁ (Q `& S)

------------------------------------------------------------------------------
-- Turning the proof system into a pre-order

infix 5 _⟶⋆_

_⟶⋆_ : Rel Formula (suc a)
_⟶⋆_ = Star (CongClosure (SymClosure _∼_ ∪ _⟶_))

infix 5 _⟷⋆_

_⟷⋆_ : Rel Formula (suc a)
_⟷⋆_ = SymCore _⟶⋆_

pattern fwd P∼Q = emb (inj₁ (SymClosure.fwd P∼Q))
pattern bwd P∼Q = emb (inj₁ (SymClosure.bwd P∼Q))
pattern step P⟶Q = emb (inj₂ P⟶Q)

-- fwd : P ∼ Q → P ⟶⋆ Q
-- fwd P∼Q = emb (inj₁ (SymClosure.fwd P∼Q)) ◅ ε

-- bwd : P ∼ Q → Q ⟶⋆ P
-- bwd P∼Q = emb (inj₁ (SymClosure.bwd P∼Q)) ◅ ε

fab : P ∼ Q → P ⟷⋆ Q
fab P∼Q = (fwd P∼Q ◅ ε , bwd P∼Q ◅ ε)

-- step : P ⟶ Q → P ⟶⋆ Q
-- step P⟶Q = emb (inj₂ P⟶Q) ◅ ε

⟶⋆-isPartialOrder : IsPartialOrder _⟷⋆_ _⟶⋆_
⟶⋆-isPartialOrder = SymCore.isPreorder⇒isPartialOrder _⟶⋆_ (StarProps.isPreorder _)

⟶⋆-Poset : Poset a (suc a) (suc a)
⟶⋆-Poset .Poset.Carrier = Formula
⟶⋆-Poset .Poset._≈_ = _⟷⋆_
⟶⋆-Poset .Poset._≤_ = _⟶⋆_
⟶⋆-Poset .Poset.isPartialOrder = ⟶⋆-isPartialOrder

open IsPartialOrder ⟶⋆-isPartialOrder public
  using () renaming (isEquivalence to ⟷⋆-isEquivalence)

open IsEquivalence ⟷⋆-isEquivalence
  using ()
  renaming
    ( refl  to ⟷⋆-refl
    ; trans to ⟷⋆-trans
    )

-- ------------------------------------------------------------------------------
-- -- Lift congruence rules to the preorder

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

_`◁⟩⋆_ : (P : Formula) → Q ⟶⋆ Q′ → (P `◁ Q) ⟶⋆ (P `◁ Q′)
P `◁⟩⋆ Q⟶⋆Q′ = Star.gmap _ (P `◁⟩_) Q⟶⋆Q′

_`⟨◁⋆_ : P ⟶⋆ P′ → (Q : Formula) → P `◁ Q ⟶⋆ P′ `◁ Q
P⟶⋆P′ `⟨◁⋆ Q = Star.gmap _ (_`⟨◁ Q) P⟶⋆P′

_`&⟩⋆_ : (P : Formula) → Q ⟶⋆ Q′ → (P `& Q) ⟶⋆ (P `& Q′)
P `&⟩⋆ Q⟶⋆Q′ = Star.gmap _ (P `&⟩_) Q⟶⋆Q′

_`⟨&⋆_ : P ⟶⋆ P′ → (Q : Formula) → P `& Q ⟶⋆ P′ `& Q
P⟶⋆P′ `⟨&⋆ Q = Star.gmap _ (_`⟨& Q) P⟶⋆P′

------------------------------------------------------------------------------
-- Deriving full versions of switch and sequence

-- `switch⋆ : (P `⊗ Q) `⅋ R ⟶⋆ P `⊗ (Q `⅋ R)
-- `switch⋆ {P} {Q} {R} with P ≟`I | R ≟`I 
-- ... |     P≟`I | yes refl = `⅋-unit ◅ P `⊗⟩ `⅋-unit⁻¹ ◅ ε
-- ... | yes refl | no  R≢`I = `⊗-comm `⟨⅋ R ◅ `⊗-unit `⟨⅋ R ◅ `⊗-unit⁻¹ ◅ `⊗-comm ◅ ε
-- ... | no  P≢`I | no  R≢`I = `switch {{≢-nonUnit P≢`I}} {{≢-nonUnit R≢`I}} ◅ ε

-- `sequence⋆ : (P `◁ Q) `⅋ (R `◁ S) ⟶⋆ (P `⅋ R) `◁ (Q `⅋ S)
-- `sequence⋆ = `sequence ◅ ε
-- `sequence⋆ {P} {Q} {R} {S} with P ≟`I | S ≟`I
-- ... | yes refl |     S≟`I = `◁-lunit `⟨⅋ (R `◁ S) ◅ {!   !} ◅ ε
-- ... | no  P≢`I | yes refl = {!   !}
-- ... | no  P≢`I | no  S≢`I = `sequence {{≢-nonUnit P≢`I}} {{≢-nonUnit S≢`I}} ◅ ε

------------------------------------------------------------------------------
-- Turning ⊗ into a commutative pomonoid

-- `⊗-mono : (P ⟶⋆ P′) → (Q ⟶⋆ Q′) → (P `⊗ Q) ⟶⋆ (P′ `⊗ Q′)
-- `⊗-mono {P = P} {Q′ = Q′} f g = P `⊗⟩⋆ g ◅◅ f `⟨⊗⋆ Q′

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
`⅋-isPosemigroup .IsPosemigroup.assoc P Q R = fab (`⅋-assoc P Q R)

`⅋-isPomonoid : IsPomonoid _⟷⋆_ _⟶⋆_ _`⅋_ `I
`⅋-isPomonoid .IsPomonoid.isPosemigroup = `⅋-isPosemigroup
`⅋-isPomonoid .IsPomonoid.identity = identityˡ , identityʳ
  where
    identityʳ = λ P → fab (`⅋-identityʳ P)
    identityˡ = λ P → ⟷⋆-trans (fab (`⅋-comm `I P)) (identityʳ P)

`⅋-isCommutativePomonoid : IsCommutativePomonoid  _⟷⋆_ _⟶⋆_ _`⅋_ `I
`⅋-isCommutativePomonoid .IsCommutativePomonoid.isPomonoid = `⅋-isPomonoid
`⅋-isCommutativePomonoid .IsCommutativePomonoid.comm P Q = fab (`⅋-comm P Q)

------------------------------------------------------------------------------
-- Turning ◁ into a pomonoid

`◁-mono : (P ⟶⋆ P′) → (Q ⟶⋆ Q′) → (P `◁ Q) ⟶⋆ (P′ `◁ Q′)
`◁-mono {P = P} {Q′ = Q′} f g = P `◁⟩⋆ g ◅◅ f `⟨◁⋆ Q′

`◁-isPomagma : IsPomagma _⟷⋆_ _⟶⋆_ _`◁_
`◁-isPomagma .IsPomagma.isPartialOrder = ⟶⋆-isPartialOrder
`◁-isPomagma .IsPomagma.mono = `◁-mono

`◁-isPosemigroup : IsPosemigroup  _⟷⋆_ _⟶⋆_ _`◁_
`◁-isPosemigroup .IsPosemigroup.isPomagma = `◁-isPomagma
`◁-isPosemigroup .IsPosemigroup.assoc P Q R = fab (`◁-assoc P Q R)

`◁-isPomonoid : IsPomonoid _⟷⋆_ _⟶⋆_ _`◁_ `I
`◁-isPomonoid .IsPomonoid.isPosemigroup = `◁-isPosemigroup
`◁-isPomonoid .IsPomonoid.identity = (identityˡ , identityʳ)
  where
    identityʳ = λ P → fab (`◁-identityʳ P)
    identityˡ = λ P → fab (`◁-identityˡ P)

------------------------------------------------------------------------------
-- Turning ⅋ and ◁ into a duoid

`⅋-`◁-isDuoidal : IsDuoidal _⟷⋆_ _⟶⋆_ _`⅋_ _`◁_ `I `I
`⅋-`◁-isDuoidal .IsDuoidal.∙-isPomonoid = `⅋-isPomonoid
`⅋-`◁-isDuoidal .IsDuoidal.◁-isPomonoid = `◁-isPomonoid
`⅋-`◁-isDuoidal .IsDuoidal.∙-◁-entropy P Q R S = step `sequence ◅ ε
`⅋-`◁-isDuoidal .IsDuoidal.∙-idem-ι = fwd (`⅋-identityʳ `I) ◅ ε
`⅋-`◁-isDuoidal .IsDuoidal.◁-idem-ε = bwd (`◁-identityʳ `I) ◅ ε
`⅋-`◁-isDuoidal .IsDuoidal.ε≲ι = ε

------------------------------------------------------------------------------
-- Turning & into a pomagma

`&-mono : P ⟶⋆ P′ → Q ⟶⋆ Q′ → P `& Q ⟶⋆ P′ `& Q′
`&-mono {P = P} {Q′ = Q′} f g = P `&⟩⋆ g ◅◅ f `⟨&⋆ Q′

`&-isPomagma : IsPomagma _⟷⋆_ _⟶⋆_ _`&_
`&-isPomagma .IsPomagma.isPartialOrder = ⟶⋆-isPartialOrder
`&-isPomagma .IsPomagma.mono = `&-mono

`&-Pomagma : Pomagma a (suc a) (suc a)
`&-Pomagma = record { isPomagma = `&-isPomagma }

-- FIXME: should probably have a left-external and a right-external
`⅋-distrib-`& : _DistributesOver_ _⟶⋆_ _`⅋_ _`&_
`⅋-distrib-`& .proj₁ P Q R = fwd (`⅋-comm _ _) ◅ step `external ◅ ε ◅◅ `&-mono (fwd (`⅋-comm _ _) ◅ ε) (fwd (`⅋-comm _ _) ◅ ε)
`⅋-distrib-`& .proj₂ P Q R = step `external ◅ ε

`&-`◁-entropy : Entropy _⟶⋆_ _`&_ _`◁_
`&-`◁-entropy P Q R S = step `medial ◅ ε

------------------------------------------------------------------------------
-- Turning ⊕ into a pomagma

-- `⊕-mono : P ⟶⋆ P′ → Q ⟶⋆ Q′ → P `⊕ Q ⟶⋆ P′ `⊕ Q′
-- `⊕-mono {P = P} {Q′ = Q′} f g = P `⊕⟩⋆ g ◅◅ f `⟨⊕⋆ Q′

-- `⊕-isPomagma : IsPomagma _⟷⋆_ _⟶⋆_ _`⊕_
-- `⊕-isPomagma .IsPomagma.isPartialOrder = ⟶⋆-isPartialOrder
-- `⊕-isPomagma .IsPomagma.mono = `⊕-mono

------------------------------------------------------------------------------
frame : Frame a (suc a) (suc a)
frame .Frame.Carrier = Formula
frame .Frame._≈_ = _⟷⋆_
frame .Frame._≲_ = _⟶⋆_
frame .Frame.I = `I
frame .Frame._⅋_ = _`⅋_
frame .Frame._◁_ = _`◁_
frame .Frame._&_ = _`&_
frame .Frame.⅋-isCommutativePomonoid = `⅋-isCommutativePomonoid
frame .Frame.&-mono = `&-mono
frame .Frame.⅋-◁-isDuoidal = `⅋-`◁-isDuoidal
frame .Frame.⅋-distrib-& = `⅋-distrib-`&
frame .Frame.&-◁-entropy = `&-`◁-entropy
frame .Frame.&-tidy = step `tidy ◅ ε
 