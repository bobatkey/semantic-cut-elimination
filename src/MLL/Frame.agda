{-# OPTIONS --postfix-projections --safe --without-K #-}

module MLL.Frame where

open import Level using (suc; _⊔_; Lift; lift; 0ℓ; lower)
open import Algebra.Ordered
open import Algebra using (_DistributesOver_)
open import Data.Product as Product using (_×_; _,_)
open import Relation.Binary

open import MLL.Model

record Frame c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Carrier : Set c
    _≈_     : Carrier → Carrier → Set ℓ₁
    _≲_     : Carrier → Carrier → Set ℓ₂

    I       : Carrier
    _⅋_     : Carrier → Carrier → Carrier

    ⅋-I-isCommutativePomonoid : IsCommutativePomonoid _≈_ _≲_ _⅋_ I

  open IsCommutativePomonoid ⅋-I-isCommutativePomonoid public
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
      )

  poset : Poset _ _ _
  poset = record { isPartialOrder = isPartialOrder }

module FrameModel {a ℓ₁ ℓ₂} (frame : Frame a ℓ₁ ℓ₂) where

  import Algebra.Ordered.Construction.LowerSet
  import Algebra.Ordered.Construction.Chu

  open Frame frame

  module L where
    open Algebra.Ordered.Construction.LowerSet poset public
    open DayCommutative ⅋-I-isCommutativePomonoid public
      using
        ( _⊸_
        ; ⊸-residual-to
        ; ⊸-residual-from
        ; ⊸-residual
        ; ε
        )
      renaming
        ( ∙-comm                               to ⅋-comm
        ; ∙-isCommutativePomonoid              to ⅋-isCommutativePomonoid
        ; ⊸-∙-isResiduatedCommutativePomonoid to ⊸-⅋-isResiduatedCommutativePomonoid
        ; _∙_                                  to _⅋_
        ; η-preserve-∙⁻¹                       to η-preserve-⅋⁻¹
        ; η-preserve-∙                         to η-preserve-⅋
        ; ∙-mono                               to ⅋-mono
        )

  open L
    public
    using
      ( LowerSet
      ; ICarrier
      ; ≤-closed
      ; _≤_
      ; *≤*
      )

  module C where
    private
      module C where
        open Algebra.Ordered.Construction.Chu.Construction
            L.⊸-⅋-isResiduatedCommutativePomonoid
            L.∧-⊤-isBoundedMeetSemilattice
            L.∨-⊥-isBoundedJoinSemilattice
            L.ε
          public

    open C public hiding (module SelfDual)

    mix : C.ε C.≈ C.¬ C.ε
    mix .Product.proj₁ .C.fpos = L.≤-refl
    mix .Product.proj₁ .C.fneg = L.≤-refl
    mix .Product.proj₂ .C.fpos = L.≤-refl
    mix .Product.proj₂ .C.fneg = L.≤-refl

  open C public using (Chu)

  model : Model (suc (suc (a ⊔ ℓ₂))) (a ⊔ ℓ₂) (a ⊔ ℓ₂)
  model .Model.Carrier = C.Chu
  model .Model._≈_ = C._≈_
  model .Model._≲_ = C._≤_
  model .Model.¬ = C.¬
  model .Model.I = C.ε
  model .Model._⊗_ = C._⊗_
  model .Model.mix = C.mix
  model .Model.⊗-isStarAutonomous = C.⊗-isStarAutonomous

  embed : Carrier → Chu
  embed x = C.embed (L.η x)
