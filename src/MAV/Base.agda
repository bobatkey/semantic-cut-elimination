{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Algebra.Core using (Op₁)
open import Algebra.Ordered
open import Algebra.Ordered.Structures.Duoidal using (IsDuoidal)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Level using (suc; _⊔_)
open import Relation.Binary using (Rel; _=[_]⇒_; IsPartialOrder; Poset; IsEquivalence; Antisymmetric)
open import Relation.Binary.Construct.Union using (_∪_)
import Relation.Binary.Construct.Union as Union
open import Relation.Binary.Construct.Core.Symmetric using (SymCore)
import Relation.Binary.Construct.Core.Symmetric as SymCore
open import Relation.Binary.Construct.Closure.Symmetric using (SymClosure)
import Relation.Binary.Construct.Closure.Symmetric as SymClosure
open import Relation.Binary.Construct.Closure.Equivalence using (EqClosure)
import Relation.Binary.Construct.Closure.Equivalence as EqClosure
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties as StarProps
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

module _ where
  infix 5 _∼_

  mutual
    data _∼_ : Rel Formula a where
      -- `⊗-assoc     : Associative _`⊗_
      `⊗-comm      : Commutative _`⊗_
      `⊗-identityʳ : RightIdentity `I _`⊗_
      `⅋-assoc     : Associative _`⅋_
      `⅋-comm      : Commutative _`⅋_
      `⅋-identityʳ : RightIdentity `I _`⅋_
      `◁-assoc     : Associative _`◁_
      `◁-identityʳ : RightIdentity `I _`◁_
      `◁-identityˡ : LeftIdentity `I _`◁_

    open import Algebra.Definitions _∼_

infix 5 _∼ᶜ_

_∼ᶜ_ : Rel Formula (suc a)
_∼ᶜ_ = CongClosure _∼_

infix 5 _≃_

_≃_ : Rel Formula (suc a)
_≃_ = EqClosure _∼ᶜ_

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

infix 5 _⟶ᶜ_

_⟶ᶜ_ : Rel Formula (suc a)
_⟶ᶜ_ = CongClosure _⟶_

infix 5 _⟶₌_

_⟶₌_ : Rel Formula (suc a)
_⟶₌_ = _≃_ ∪ _⟶ᶜ_

infix 5 _⟶⋆_

_⟶⋆_ : Rel Formula (suc a)
_⟶⋆_ = Star _⟶₌_

infix 5 _⟷⋆_

_⟷⋆_ : Rel Formula (suc a)
_⟷⋆_ = SymCore _⟶⋆_

fwd : P ∼ Q → P ⟶₌ Q
fwd P∼Q = inj₁ (SymClosure.fwd (emb P∼Q) ◅ ε)

bwd : P ∼ Q → Q ⟶₌ P
bwd P∼Q = inj₁ (SymClosure.bwd (emb P∼Q) ◅ ε)

fwd∧bwd : P ∼ Q → P ⟷⋆ Q
fwd∧bwd P∼Q = (fwd P∼Q ◅ ε , bwd P∼Q ◅ ε)

step : P ⟶ Q → P ⟶₌ Q
step P⟶Q = inj₂ (emb P⟶Q)

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

------------------------------------------------------------------------------
-- Lift congruence rules to the preorder

⟶⋆-map : (f : Op₁ Formula) (g : ∀ {R} → CongClosure R =[ f ]⇒ CongClosure R) → P ⟶⋆ P′ → f P ⟶⋆ f P′ 
⟶⋆-map f g = Star.gmap f (Sum.map (EqClosure.gmap f g) g)

_`⊗⟩⋆_ : (P : Formula) → Q ⟶⋆ Q′ → (P `⊗ Q) ⟶⋆ (P `⊗ Q′)
P `⊗⟩⋆ Q⟶⋆Q′ = ⟶⋆-map _ (P `⊗⟩_) Q⟶⋆Q′

_`⟨⊗⋆_ : P ⟶⋆ P′ → (Q : Formula) → P `⊗ Q ⟶⋆ P′ `⊗ Q
P⟶⋆P′ `⟨⊗⋆ Q = ⟶⋆-map _ (_`⟨⊗ Q) P⟶⋆P′

-- _`⟨⊗⋆_ : P ⟶⋆ P′ → (Q : Formula) → P `⊗ Q ⟶⋆ P′ `⊗ Q
-- f `⟨⊗⋆ Q = `⊗-comm ◅ Q `⊗⟩⋆ f ◅◅ `⊗-comm ◅ ε

_`⅋⟩⋆_ : (P : Formula) → Q ⟶⋆ Q′ → (P `⅋ Q) ⟶⋆ (P `⅋ Q′)
P `⅋⟩⋆ Q⟶⋆Q′ = ⟶⋆-map _ (P `⅋⟩_) Q⟶⋆Q′

_`⟨⅋⋆_ : P ⟶⋆ P′ → (Q : Formula) → P `⅋ Q ⟶⋆ P′ `⅋ Q
P⟶⋆P′ `⟨⅋⋆ Q = ⟶⋆-map _ (_`⟨⅋ Q) P⟶⋆P′

-- _`⟨⅋⋆_ : P ⟶⋆ P′ → (Q : Formula) → P `⅋ Q ⟶⋆ P′ `⅋ Q
-- f `⟨⅋⋆ Q = `⅋-comm ◅ Q `⅋⟩⋆ f ◅◅ `⅋-comm ◅ ε

_`◁⟩⋆_ : (P : Formula) → Q ⟶⋆ Q′ → (P `◁ Q) ⟶⋆ (P `◁ Q′)
P `◁⟩⋆ Q⟶⋆Q′ = ⟶⋆-map _ (P `◁⟩_) Q⟶⋆Q′

_`⟨◁⋆_ : P ⟶⋆ P′ → (Q : Formula) → P `◁ Q ⟶⋆ P′ `◁ Q
P⟶⋆P′ `⟨◁⋆ Q = ⟶⋆-map _ (_`⟨◁ Q) P⟶⋆P′

_`&⟩⋆_ : (P : Formula) → Q ⟶⋆ Q′ → (P `& Q) ⟶⋆ (P `& Q′)
P `&⟩⋆ Q⟶⋆Q′ = ⟶⋆-map _ (P `&⟩_) Q⟶⋆Q′

_`⟨&⋆_ : P ⟶⋆ P′ → (Q : Formula) → P `& Q ⟶⋆ P′ `& Q
P⟶⋆P′ `⟨&⋆ Q = ⟶⋆-map _ (_`⟨& Q) P⟶⋆P′

_`⊕⟩⋆_ : (P : Formula) → Q ⟶⋆ Q′ → (P `⊕ Q) ⟶⋆ (P `⊕ Q′)
P `⊕⟩⋆ Q⟶⋆Q′ = ⟶⋆-map _ (P `⊕⟩_) Q⟶⋆Q′

_`⟨⊕⋆_ : P ⟶⋆ P′ → (Q : Formula) → P `⊕ Q ⟶⋆ P′ `⊕ Q
P⟶⋆P′ `⟨⊕⋆ Q = ⟶⋆-map _ (_`⟨⊕ Q) P⟶⋆P′

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

`⊗-mono : (P ⟶⋆ P′) → (Q ⟶⋆ Q′) → (P `⊗ Q) ⟶⋆ (P′ `⊗ Q′)
`⊗-mono {P = P} {Q′ = Q′} f g = P `⊗⟩⋆ g ◅◅ f `⟨⊗⋆ Q′

`⊗-isPomagma : IsPomagma _⟷⋆_ _⟶⋆_ _`⊗_
`⊗-isPomagma .IsPomagma.isPartialOrder = ⟶⋆-isPartialOrder
`⊗-isPomagma .IsPomagma.mono = `⊗-mono

-- `⊗-isPosemigroup : IsPosemigroup  _⟷⋆_ _⟶⋆_ _`⊗_
-- `⊗-isPosemigroup .IsPosemigroup.isPomagma = `⊗-isPomagma
-- `⊗-isPosemigroup .IsPosemigroup.assoc P Q R = fwd∧bwd (`⊗-assoc P Q R)

-- `⊗-isPomonoid : IsPomonoid _⟷⋆_ _⟶⋆_ _`⊗_ `I
-- `⊗-isPomonoid .IsPomonoid.isPosemigroup = `⊗-isPosemigroup
-- `⊗-isPomonoid .IsPomonoid.identity = identityˡ , identityʳ
--   where
--     identityʳ = λ P → fwd∧bwd (`⊗-identityʳ P)
--     identityˡ = λ P → ⟷⋆-trans (fwd∧bwd (`⊗-comm `I P)) (identityʳ P)

-- `⊗-isCommutativePomonoid : IsCommutativePomonoid  _⟷⋆_ _⟶⋆_ _`⊗_ `I
-- `⊗-isCommutativePomonoid .IsCommutativePomonoid.isPomonoid = `⊗-isPomonoid
-- `⊗-isCommutativePomonoid .IsCommutativePomonoid.comm P Q = fwd∧bwd (`⊗-comm P Q)

------------------------------------------------------------------------------
-- Turning ⅋ into a commutative pomonoid

`⅋-mono : (P ⟶⋆ P′) → (Q ⟶⋆ Q′) → (P `⅋ Q) ⟶⋆ (P′ `⅋ Q′)
`⅋-mono {P = P} {Q′ = Q′} f g = P `⅋⟩⋆ g ◅◅ f `⟨⅋⋆ Q′

`⅋-isPomagma : IsPomagma _⟷⋆_ _⟶⋆_ _`⅋_
`⅋-isPomagma .IsPomagma.isPartialOrder = ⟶⋆-isPartialOrder
`⅋-isPomagma .IsPomagma.mono = `⅋-mono

`⅋-isPosemigroup : IsPosemigroup  _⟷⋆_ _⟶⋆_ _`⅋_
`⅋-isPosemigroup .IsPosemigroup.isPomagma = `⅋-isPomagma
`⅋-isPosemigroup .IsPosemigroup.assoc P Q R = fwd∧bwd (`⅋-assoc P Q R)

`⅋-isPomonoid : IsPomonoid _⟷⋆_ _⟶⋆_ _`⅋_ `I
`⅋-isPomonoid .IsPomonoid.isPosemigroup = `⅋-isPosemigroup
`⅋-isPomonoid .IsPomonoid.identity = identityˡ , identityʳ
  where
    identityʳ = λ P → fwd∧bwd (`⅋-identityʳ P)
    identityˡ = λ P → ⟷⋆-trans (fwd∧bwd (`⅋-comm `I P)) (identityʳ P)

`⅋-isCommutativePomonoid : IsCommutativePomonoid  _⟷⋆_ _⟶⋆_ _`⅋_ `I
`⅋-isCommutativePomonoid .IsCommutativePomonoid.isPomonoid = `⅋-isPomonoid
`⅋-isCommutativePomonoid .IsCommutativePomonoid.comm P Q = fwd∧bwd (`⅋-comm P Q)

------------------------------------------------------------------------------
-- Turning ◁ into a pomonoid

`◁-mono : (P ⟶⋆ P′) → (Q ⟶⋆ Q′) → (P `◁ Q) ⟶⋆ (P′ `◁ Q′)
`◁-mono {P = P} {Q′ = Q′} f g = P `◁⟩⋆ g ◅◅ f `⟨◁⋆ Q′

`◁-isPomagma : IsPomagma _⟷⋆_ _⟶⋆_ _`◁_
`◁-isPomagma .IsPomagma.isPartialOrder = ⟶⋆-isPartialOrder
`◁-isPomagma .IsPomagma.mono = `◁-mono

`◁-isPosemigroup : IsPosemigroup  _⟷⋆_ _⟶⋆_ _`◁_
`◁-isPosemigroup .IsPosemigroup.isPomagma = `◁-isPomagma
`◁-isPosemigroup .IsPosemigroup.assoc P Q R = fwd∧bwd (`◁-assoc P Q R)

`◁-isPomonoid : IsPomonoid _⟷⋆_ _⟶⋆_ _`◁_ `I
`◁-isPomonoid .IsPomonoid.isPosemigroup = `◁-isPosemigroup
`◁-isPomonoid .IsPomonoid.identity = (identityˡ , identityʳ)
  where
    identityʳ = λ P → fwd∧bwd (`◁-identityʳ P)
    identityˡ = λ P → fwd∧bwd (`◁-identityˡ P)

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

open import Algebra.Definitions _⟶⋆_ using (_DistributesOver_)

-- FIXME: should probably have a left-external and a right-external
`⅋-distrib-`& : _`⅋_ DistributesOver _`&_
`⅋-distrib-`& .proj₁ P Q R = fwd (`⅋-comm _ _) ◅ step `external ◅ ε ◅◅ `&-mono (fwd (`⅋-comm _ _) ◅ ε) (fwd (`⅋-comm _ _) ◅ ε)
`⅋-distrib-`& .proj₂ P Q R = step `external ◅ ε

`&-`◁-entropy : Entropy _⟶⋆_ _`&_ _`◁_
`&-`◁-entropy P Q R S = step `medial ◅ ε

------------------------------------------------------------------------------
-- Turning ⊕ into a pomagma

`⊕-mono : P ⟶⋆ P′ → Q ⟶⋆ Q′ → P `⊕ Q ⟶⋆ P′ `⊕ Q′
`⊕-mono {P = P} {Q′ = Q′} f g = P `⊕⟩⋆ g ◅◅ f `⟨⊕⋆ Q′

`⊕-isPomagma : IsPomagma _⟷⋆_ _⟶⋆_ _`⊕_
`⊕-isPomagma .IsPomagma.isPartialOrder = ⟶⋆-isPartialOrder
`⊕-isPomagma .IsPomagma.mono = `⊕-mono

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
   