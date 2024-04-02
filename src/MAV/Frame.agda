{-# OPTIONS --postfix-projections --safe --without-K #-}

module MAV.Frame where

open import Level using (suc; _⊔_; Lift; lift; 0ℓ; lower)
open import Algebra.Ordered
open import Algebra.Ordered.Structures.Duoidal
open import Algebra using (_DistributesOver_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax)
open import Relation.Binary

open import MAV.Model

record Frame c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Carrier : Set c
    _≈_     : Carrier → Carrier → Set ℓ₁
    _≲_     : Carrier → Carrier → Set ℓ₂

    I       : Carrier
    _◁_     : Carrier → Carrier → Carrier
    _⅋_     : Carrier → Carrier → Carrier
    _&_     : Carrier → Carrier → Carrier

    ⅋-◁-isCommutativeDuoidal : IsCommutativeDuoidal _≈_ _≲_ _⅋_ _◁_ I I
    ⅋-distrib-&              : _DistributesOver_ _≲_ _⅋_ _&_

    -- FIXME: this is half of IsDuoidal when the first operation is only a semigroup
    &-mono                  : Monotonic₂ _≲_ _≲_ _≲_ _&_
    &-◁-entropy             : Entropy _≲_ _&_ _◁_
    &-tidy                  : (I & I) ≲ I

  open IsCommutativeDuoidal ⅋-◁-isCommutativeDuoidal public
    using
      ( isPreorder
      ; isPartialOrder
      ; refl
      ; reflexive
      ; trans
      ; antisym
      ; isEquivalence
      ; setoid
      ; module Eq
      ; ◁-isMagma
      ; ◁-isSemigroup
      ; ◁-isMonoid
      ; ◁-isPromagma
      ; ◁-isProsemigroup
      ; ◁-isPromonoid
      ; ◁-isPomagma
      ; ◁-isPosemigroup
      ; ◁-cong
      ; ◁-congˡ
      ; ◁-congʳ
      ; ◁-mono
      ; ◁-monoˡ
      ; ◁-monoʳ
      ; ◁-assoc
      ; ◁-identity
      ; ◁-identityˡ
      ; ◁-identityʳ
      ; ◁-isPomonoid
      ; ◁-idem-ε
      ; ε≲ι
      )
    renaming
      ( ∙-isMagma               to ⅋-isMagma
      ; ∙-isSemigroup           to ⅋-isSemigroup
      ; ∙-isMonoid              to ⅋-isMonoid
      ; ∙-isPromagma            to ⅋-isPromagma
      ; ∙-isProsemigroup        to ⅋-isProsemigroup
      ; ∙-isPromonoid           to ⅋-isPromonoid
      ; ∙-isPomagma             to ⅋-isPomagma
      ; ∙-isPosemigroup         to ⅋-isPosemigroup
      ; ∙-isPomonoid            to ⅋-isPomonoid
      ; ∙-isCommutativePomonoid to ⅋-isCommutativePomonoid
      ; isDuoidal               to ⅋-◁-isDuoidal
      ; ∙-◁-entropy             to ⅋-◁-entropy
      ; ∙-idem-ι                to ⅋-idem-ι
      ; ∙-cong                  to ⅋-cong
      ; ∙-congˡ                 to ⅋-congˡ
      ; ∙-congʳ                 to ⅋-congʳ
      ; ∙-mono                  to ⅋-mono
      ; ∙-monoˡ                 to ⅋-monoˡ
      ; ∙-monoʳ                 to ⅋-monoʳ
      ; ∙-assoc                 to ⅋-assoc
      ; ∙-identity              to ⅋-identity
      ; ∙-identityˡ             to ⅋-identityˡ
      ; ∙-identityʳ             to ⅋-identityʳ
      ; ∙-comm                  to ⅋-comm
      )

  poset : Poset _ _ _
  poset = record { isPartialOrder = isPartialOrder }

  &-isPomagma : IsPomagma _≈_ _≲_ _&_
  &-isPomagma = record
    { isPartialOrder = isPartialOrder
    ; mono = &-mono
    }

  &-pomagma : Pomagma _ _ _
  &-pomagma = record { isPomagma = &-isPomagma }

module FrameModel {a ℓ₁ ℓ₂} (frame : Frame a ℓ₁ ℓ₂) where

  import Algebra.Ordered.Construction.LowerSet
  import Algebra.Ordered.Construction.Ideal
  import Algebra.Ordered.Construction.Chu

  open Frame frame

  module LSet = Algebra.Ordered.Construction.LowerSet poset
  module LMon = LSet.LiftIsCommutativePomonoid ⅋-isCommutativePomonoid

  module ISet = Algebra.Ordered.Construction.Ideal &-pomagma
  module IDDMon = ISet.DayDistributive ⅋-isCommutativePomonoid ⅋-distrib-&
  module IDEMon = ISet.DayEntropic ◁-isPomonoid &-◁-entropy &-tidy
  module IDuo = ISet.DayDuoidal ⅋-◁-isCommutativeDuoidal ⅋-distrib-& &-◁-entropy &-tidy

  open ISet._≤ⁱ_
  open ISet.Ideal

  units-iso : IDDMon.εⁱ ISet.≈ⁱ IDEMon.ιⁱ
  units-iso .proj₁ = IDuo.εⁱ≤ιⁱ
  units-iso .proj₂ .*≤ⁱ* {x} x≤I = ISet.leaf x x≤I , refl

  module CSet = Algebra.Ordered.Construction.Chu.Construction
                  IDDMon.⊸ⁱ-∙ⁱ-isResiduatedCommutativePomonoid
                  ISet.∧ⁱ-isMeetSemilattice
                  ISet.∨ⁱ-isJoinSemilattice
                  IDDMon.εⁱ
  open CSet public
      using
        ( Chu
        ; _==>_
        ; module SelfDual
        ; _≅_
        ; ==>-trans
        ; ⊗-isCommutativePomonoid
        ; ⊗-isStarAutonomous
        ; &-isMeet
        )
      renaming
        ( _⊗_ to _⟦⊗⟧_
        ; _&_ to _⟦&⟧_
        ; I to ⟦I⟧
        ; ¬ to ⟦¬⟧
        ; embed to Chu-embed
        )

  open Chu
  open _==>_

  K-m : (IDDMon.εⁱ IDEMon.◁ⁱ IDDMon.εⁱ) ISet.≤ⁱ IDDMon.εⁱ
  K-m = ISet.≤ⁱ-trans (IDEMon.◁ⁱ-mono (ISet.≤ⁱ-reflexive units-iso) ISet.≤ⁱ-refl) (ISet.≤ⁱ-reflexive (IDEMon.◁ⁱ-identityˡ _))
  K-u : IDEMon.ιⁱ ISet.≤ⁱ IDDMon.εⁱ
  K-u = ISet.≤ⁱ-reflexive (ISet.Eq.sym units-iso)

  open SelfDual IDuo.∙ⁱ-◁ⁱ-isDuoidal K-m K-u
    renaming
      ( J   to ⟦J⟧
      ; _⍮_ to _⟦⍮⟧_
      )

  Chu-mix : ⟦I⟧ ≅ ⟦¬⟧ ⟦I⟧
  Chu-mix .proj₁ .fpos = ISet.≤ⁱ-refl
  Chu-mix .proj₁ .fneg = ISet.≤ⁱ-refl
  Chu-mix .proj₂ .fpos = ISet.≤ⁱ-refl
  Chu-mix .proj₂ .fneg = ISet.≤ⁱ-refl

  I-eq-J : ⟦I⟧ ≅ ⟦J⟧
  I-eq-J .proj₁ .fpos = ISet.≤ⁱ-reflexive units-iso
  I-eq-J .proj₁ .fneg = ISet.≤ⁱ-reflexive (ISet.Eq.sym units-iso)
  I-eq-J .proj₂ .fpos = ISet.≤ⁱ-reflexive (ISet.Eq.sym units-iso)
  I-eq-J .proj₂ .fneg = ISet.≤ⁱ-reflexive units-iso

  ⊗-⍮-isCommutativeDuoidal : IsCommutativeDuoidal _≅_ _==>_ _⟦⊗⟧_ _⟦⍮⟧_ ⟦I⟧ ⟦J⟧
  ⊗-⍮-isCommutativeDuoidal = record
    { isDuoidal = ⊗-⍮-isDuoidal 
    ; ∙-comm    = ⊗-isCommutativePomonoid .IsCommutativePomonoid.comm 
    }

  model : Model (suc (suc (a ⊔ ℓ₂))) (a ⊔ ℓ₂) (a ⊔ ℓ₂)
  model .Model.Carrier = Chu
  model .Model._≈_ = _≅_
  model .Model._≲_ = _==>_
  model .Model.¬ = ⟦¬⟧
  model .Model.I = ⟦I⟧
  model .Model.J = ⟦J⟧
  model .Model._⊗_ = _⟦⊗⟧_
  model .Model._◁_ = _⟦⍮⟧_
  model .Model._&_ = _⟦&⟧_
  model .Model.mix = Chu-mix
  model .Model.&-isMeet = &-isMeet
  model .Model.⊗-◁-isCommutativeDuoidal = ⊗-⍮-isCommutativeDuoidal
  model .Model.I-eq-J = I-eq-J
  model .Model.◁-self-dual = self-dual
  model .Model.⊗-isStarAutonomous = ⊗-isStarAutonomous

  embed : Carrier → Chu
  embed x = Chu-embed (ISet.ηⁱ x)
