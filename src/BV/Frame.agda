{-# OPTIONS --postfix-projections --safe --without-K #-}

module BV.Frame where

open import Level using (suc; _⊔_; Lift; lift; 0ℓ; lower)
open import Algebra.Ordered
open import Algebra.Ordered.Structures.Duoidal
open import Algebra using (_DistributesOver_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax)
open import Relation.Binary

open import BV.Model

record Frame c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Carrier : Set c
    _≈_     : Carrier → Carrier → Set ℓ₁
    _≲_     : Carrier → Carrier → Set ℓ₂

    I       : Carrier
    _◁_     : Carrier → Carrier → Carrier
    _⅋_     : Carrier → Carrier → Carrier

    ⅋-◁-isCommutativeDuoidal : IsCommutativeDuoidal _≈_ _≲_ _⅋_ _◁_ I I

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

module FrameModel {a ℓ₁ ℓ₂} (frame : Frame a ℓ₁ ℓ₂) where

  import Algebra.Ordered.Construction.LowerSet
  import Algebra.Ordered.Construction.Chu

  open Frame frame

  module L where
    open Algebra.Ordered.Construction.LowerSet poset public
    open LiftIsDuoidal ⅋-◁-isDuoidal public
      using
        ( ε
        ; _◁_
        ; ι
        ; ◁-mono
        ; ◁-monoˡ
        ; ◁-monoʳ
        ; ◁-cong
        ; ◁-congˡ
        ; ◁-congʳ
        ; ◁-assoc
        ; ◁-identity
        ; ◁-identityˡ
        ; ◁-identityʳ
        ; ◁-isPomonoid
        ; η-preserve-◁
        ; η-preserve-◁⁻¹
        ; ε≤ι
        )
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
        ; η-preserve-∙   to η-preserve-⅋
        ; η-preserve-∙⁻¹ to η-preserve-⅋⁻¹
        ; ∙-◁-isDuoidal  to ⅋-◁-isDuoidal
        )
    open LiftIsCommutativePomonoid ⅋-isCommutativePomonoid public
      using
        ( _⊸_
        ; ⊸-residual-to
        ; ⊸-residual-from
        ; ⊸-residual
        )
      renaming
        ( ∙-comm                               to ⅋-comm
        ; ∙-isCommutativePomonoid              to ⅋-isCommutativePomonoid
        ; ⊸-∙-isResiduatedCommutativePomonoid to ⊸-⅋-isResiduatedCommutativePomonoid
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
    units-iso : L.ε L.≈ L.ι
    units-iso .proj₁ = L.ε≤ι
    units-iso .proj₂ .*≤* x≤I = x≤I

    private 
      module C where
        open Algebra.Ordered.Construction.Chu.Construction
            L.⊸-⅋-isResiduatedCommutativePomonoid
            L.∧-isMeetSemilattice
            L.∨-isJoinSemilattice
            L.ε
          public
        
        K-m : (L.ε L.◁ L.ε) L.≤ L.ε
        K-m = L.≤-trans (L.◁-mono (L.≤-reflexive units-iso) L.≤-refl) (L.≤-reflexive (L.◁-identityˡ _))
        
        K-u : L.ι L.≤ L.ε
        K-u = L.≤-reflexive (L.Eq.sym units-iso)

        open SelfDual L.⅋-◁-isDuoidal K-m K-u public

    open C public hiding (module SelfDual)

    mix : C.ε C.≈ C.¬ C.ε
    mix .proj₁ .C.fpos = L.≤-refl
    mix .proj₁ .C.fneg = L.≤-refl
    mix .proj₂ .C.fpos = L.≤-refl
    mix .proj₂ .C.fneg = L.≤-refl

    ε-eq-ι : C.ε C.≈ C.ι
    ε-eq-ι .proj₁ .C.fpos = L.≤-reflexive units-iso
    ε-eq-ι .proj₁ .C.fneg = L.≤-reflexive (L.Eq.sym units-iso)
    ε-eq-ι .proj₂ .C.fpos = L.≤-reflexive (L.Eq.sym units-iso)
    ε-eq-ι .proj₂ .C.fneg = L.≤-reflexive units-iso

    ⊗-⍮-isCommutativeDuoidal : IsCommutativeDuoidal C._≈_ C._≤_ C._⊗_ C._⍮_ C.ε C.ι
    ⊗-⍮-isCommutativeDuoidal = record
      { isDuoidal = C.⊗-⍮-isDuoidal 
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
  model .Model._◁_ = C._⍮_
  model .Model.mix = C.mix
  model .Model.⊗-◁-isCommutativeDuoidal = C.⊗-⍮-isCommutativeDuoidal
  model .Model.I-eq-J = C.ε-eq-ι
  model .Model.◁-self-dual = C.self-dual
  model .Model.⊗-isStarAutonomous = C.⊗-isStarAutonomous

  embed : Carrier → Chu
  embed x = C.embed (L.η x)
