{-# OPTIONS --postfix-projections --safe --without-K #-}

module MAV.Frame where

open import Level using (suc; _⊔_)
open import Algebra using (_DistributesOver_)
open import Algebra.Ordered
open import Data.Product as Product using (_×_; _,_)
open import Relation.Binary.Bundles using (Poset)
open import Relation.Binary.Definitions

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
    open DayCommutative ⅋-isCommutativePomonoid public
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
    open DayCommutative ⅋-isCommutativePomonoid ⅋-distrib-& public
      renaming
        ( _∙_             to _⅋_
        ; ∙-mono          to ⅋-mono
        ; ∙-comm          to ⅋-comm
        ; ∙-assoc         to ⅋-assoc
        ; ∙-identityˡ     to ⅋-identityˡ
        ; ∙-identityʳ     to ⅋-identityʳ
        )
    open DayEntropic ◁-isPomonoid &-◁-entropy &-tidy public
    open DayDuoidal ⅋-◁-isCommutativeDuoidal ⅋-distrib-& &-◁-entropy &-tidy public

  open I
    public
    using
      ( Ideal
      ; ICarrier
      ; ≤-closed
      ; ∨-closed
      ; _≤_
      ; *≤*
      )

  units-iso : I.ε I.≈ I.ι
  units-iso .Product.proj₁ = I.ε≤ι
  units-iso .Product.proj₂ .*≤* {x} x≤I = I.leaf x≤I

  module C where
    private
      module C where
        open Algebra.Ordered.Construction.Chu.Construction
              I.⊸-∙-isResiduatedCommutativePomonoid
              I.∧-⊤-isBoundedMeetSemilattice
              I.∨-⊥-isBoundedJoinSemilattice
              I.ε
          public

        K-m : (I.ε I.◁ I.ε) I.≤ I.ε
        K-m = I.≤-trans (I.◁-mono (I.≤-reflexive units-iso) I.≤-refl) (I.≤-reflexive (I.◁-identityˡ _))

        K-u : I.ι I.≤ I.ε
        K-u = I.≤-reflexive (I.Eq.sym units-iso)

        open SelfDual I.∙-◁-isDuoidal K-m K-u public

    open C public

    mix : C.ε C.≈ C.¬ C.ε
    mix .Product.proj₁ .C.fpos = I.≤-refl
    mix .Product.proj₁ .C.fneg = I.≤-refl
    mix .Product.proj₂ .C.fpos = I.≤-refl
    mix .Product.proj₂ .C.fneg = I.≤-refl

    ε-eq-ι : C.ε C.≈ C.ι
    ε-eq-ι .Product.proj₁ .C.fpos = I.≤-reflexive units-iso
    ε-eq-ι .Product.proj₁ .C.fneg = I.≤-reflexive (I.Eq.sym units-iso)
    ε-eq-ι .Product.proj₂ .C.fpos = I.≤-reflexive (I.Eq.sym units-iso)
    ε-eq-ι .Product.proj₂ .C.fneg = I.≤-reflexive units-iso

    ⊗-◁-isCommutativeDuoidal : IsCommutativeDuoidal C._≈_ C._≤_ C._⊗_ C._◁_ C.ε C.ι
    ⊗-◁-isCommutativeDuoidal = record
      { isDuoidal = C.⊗-◁-isDuoidal 
      ; ∙-comm    = C.⊗-isCommutativePomonoid .IsCommutativePomonoid.comm 
      }

  open C public using (Chu)

  model : Model (suc (suc (a ⊔ ℓ₂))) (a ⊔ ℓ₂) (a ⊔ ℓ₂)
  model .Model.Carrier = C.Chu
  model .Model._≈_ = C._≈_
  model .Model._≲_ = C._≤_
  model .Model.¬ = C.¬
  model .Model.I = C.ε
  model .Model.J = C.ι
  model .Model._⊗_ = C._⊗_
  model .Model._◁_ = C._◁_
  model .Model._&_ = C._&_
  model .Model.mix = C.mix
  model .Model.&-isMeet = C.&-isMeet
  model .Model.⊗-◁-isCommutativeDuoidal = C.⊗-◁-isCommutativeDuoidal
  model .Model.I-eq-J = C.ε-eq-ι
  model .Model.◁-self-dual = C.self-dual
  model .Model.⊗-isStarAutonomous = C.⊗-isStarAutonomous

  embed : Carrier → Chu
  embed x = C.embed (I.η x)
