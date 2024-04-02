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

  module L where
    open Algebra.Ordered.Construction.LowerSet poset public
    open LiftIsCommutativePomonoid ⅋-isCommutativePomonoid public
      renaming
        ( _∙_             to _⅋_
        ; ∙-mono          to ⅋-mono
        ; ∙-monoˡ         to ⅋-monoˡ
        ; ∙-monoʳ         to ⅋-monoʳ
        ; ∙-cong          to ⅋-cong
        ; ∙-congˡ         to ⅋-congˡ
        ; ∙-congʳ         to ⅋-congʳ
        ; ∙-assoc         to ⅋-assoc
        ; ∙-identity      to ⅋-identity
        ; ∙-identityˡ     to ⅋-identityˡ
        ; ∙-identityʳ     to ⅋-identityʳ
        ; ∙-isPomonoid    to ⅋-isPomonoid
        )

  module I where
    open Algebra.Ordered.Construction.Ideal &-pomagma public
    open DayDistributive ⅋-isCommutativePomonoid ⅋-distrib-& public
      renaming
        ( _∙ⁱ_             to _⅋ⁱ_
        ; ∙ⁱ-mono          to ⅋ⁱ-mono
        ; ∙ⁱ-comm          to ⅋ⁱ-comm
        ; ∙ⁱ-assoc         to ⅋ⁱ-assoc
        ; ∙ⁱ-identityˡ     to ⅋ⁱ-identityˡ
        ; ∙ⁱ-identityʳ     to ⅋ⁱ-identityʳ
        )
    open DayEntropic ◁-isPomonoid &-◁-entropy &-tidy public
    open DayDuoidal ⅋-◁-isCommutativeDuoidal ⅋-distrib-& &-◁-entropy &-tidy public

  open I
    public
    using
      ( Ideal
      ; ICarrier
      ; ≤-closed
      ; +-closed
      ; _≤ⁱ_
      ; *≤ⁱ*
      )

  units-iso : I.εⁱ I.≈ⁱ I.ιⁱ
  units-iso .proj₁ = I.εⁱ≤ιⁱ
  units-iso .proj₂ .*≤ⁱ* {x} x≤I = I.leaf x x≤I , refl

  module C where
    open Algebra.Ordered.Construction.Chu.Construction
          I.⊸ⁱ-∙ⁱ-isResiduatedCommutativePomonoid
          I.∧ⁱ-isMeetSemilattice
          I.∨ⁱ-isJoinSemilattice
          I.εⁱ
      public

    K-m : (I.εⁱ I.◁ⁱ I.εⁱ) I.≤ⁱ I.εⁱ
    K-m = I.≤ⁱ-trans (I.◁ⁱ-mono (I.≤ⁱ-reflexive units-iso) I.≤ⁱ-refl) (I.≤ⁱ-reflexive (I.◁ⁱ-identityˡ _))
    
    K-u : I.ιⁱ I.≤ⁱ I.εⁱ
    K-u = I.≤ⁱ-reflexive (I.Eq.sym units-iso)

    open SelfDual I.∙ⁱ-◁ⁱ-isDuoidal K-m K-u public

    mix : ε ≅ ¬ ε
    mix .proj₁ .fpos = I.≤ⁱ-refl
    mix .proj₁ .fneg = I.≤ⁱ-refl
    mix .proj₂ .fpos = I.≤ⁱ-refl
    mix .proj₂ .fneg = I.≤ⁱ-refl

    ε-eq-ι : ε ≅ ι
    ε-eq-ι .proj₁ .fpos = I.≤ⁱ-reflexive units-iso
    ε-eq-ι .proj₁ .fneg = I.≤ⁱ-reflexive (I.Eq.sym units-iso)
    ε-eq-ι .proj₂ .fpos = I.≤ⁱ-reflexive (I.Eq.sym units-iso)
    ε-eq-ι .proj₂ .fneg = I.≤ⁱ-reflexive units-iso

    ⊗-⍮-isCommutativeDuoidal : IsCommutativeDuoidal _≅_ _==>_ _⊗_ _⍮_ ε ι
    ⊗-⍮-isCommutativeDuoidal = record
      { isDuoidal = ⊗-⍮-isDuoidal 
      ; ∙-comm    = ⊗-isCommutativePomonoid .IsCommutativePomonoid.comm 
      }
  
  open C public using (Chu)

  model : Model (suc (suc (a ⊔ ℓ₂))) (a ⊔ ℓ₂) (a ⊔ ℓ₂)
  model .Model.Carrier = C.Chu
  model .Model._≈_ = C._≅_
  model .Model._≲_ = C._==>_
  model .Model.¬ = C.¬
  model .Model.I = C.ε
  model .Model.J = C.ι
  model .Model._⊗_ = C._⊗_
  model .Model._◁_ = C._⍮_
  model .Model._&_ = C._&_
  model .Model.mix = C.mix
  model .Model.&-isMeet = C.&-isMeet
  model .Model.⊗-◁-isCommutativeDuoidal = C.⊗-⍮-isCommutativeDuoidal
  model .Model.I-eq-J = C.ε-eq-ι
  model .Model.◁-self-dual = C.self-dual
  model .Model.⊗-isStarAutonomous = C.⊗-isStarAutonomous

  embed : Carrier → Chu
  embed x = C.embed (I.ηⁱ x)
