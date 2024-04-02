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
        ( εᵖ
        ; _◁ᵖ_
        ; ιᵖ
        ; ◁ᵖ-mono
        ; ◁ᵖ-monoˡ
        ; ◁ᵖ-monoʳ
        ; ◁ᵖ-cong
        ; ◁ᵖ-congˡ
        ; ◁ᵖ-congʳ
        ; ◁ᵖ-assoc
        ; ◁ᵖ-identity
        ; ◁ᵖ-identityˡ
        ; ◁ᵖ-identityʳ
        ; ◁ᵖ-isPomonoid
        ; ηᵖ-preserve-◁ᵖ
        ; ηᵖ-preserve-◁ᵖ⁻¹
        ; εᵖ≤ιᵖ
        )
      renaming
        ( _∙ᵖ_             to _⅋ᵖ_
        ; ∙ᵖ-mono          to ⅋ᵖ-mono
        ; ∙ᵖ-monoˡ         to ⅋ᵖ-monoˡ
        ; ∙ᵖ-monoʳ         to ⅋ᵖ-monoʳ
        ; ∙ᵖ-cong          to ⅋ᵖ-cong
        ; ∙ᵖ-congˡ         to ⅋ᵖ-congˡ
        ; ∙ᵖ-congʳ         to ⅋ᵖ-congʳ
        ; ∙ᵖ-assoc         to ⅋ᵖ-assoc
        ; ∙ᵖ-identity      to ⅋ᵖ-identity
        ; ∙ᵖ-identityˡ     to ⅋ᵖ-identityˡ
        ; ∙ᵖ-identityʳ     to ⅋ᵖ-identityʳ
        ; ∙ᵖ-isPomonoid    to ⅋ᵖ-isPomonoid
        ; ηᵖ-preserve-∙ᵖ   to ηᵖ-preserve-⅋ᵖ
        ; ηᵖ-preserve-∙ᵖ⁻¹ to ηᵖ-preserve-⅋ᵖ⁻¹
        ; ∙ᵖ-◁ᵖ-isDuoidal  to ⅋ᵖ-◁ᵖ-isDuoidal
        )
    open LiftIsCommutativePomonoid ⅋-isCommutativePomonoid public
      using
        ( _⊸ᵖ_
        ; ⊸ᵖ-residual-to
        ; ⊸ᵖ-residual-from
        ; ⊸ᵖ-residual
        )
      renaming
        ( ∙ᵖ-comm                               to ⅋ᵖ-comm
        ; ∙ᵖ-isCommutativePomonoid              to ⅋ᵖ-isCommutativePomonoid
        ; ⊸ᵖ-∙ᵖ-isResiduatedCommutativePomonoid to ⊸ᵖ-⅋ᵖ-isResiduatedCommutativePomonoid
        )

  open L
    public
    using
      ( LowerSet
      ; ICarrier
      ; ≤-closed
      ; _≤ᵖ_
      ; *≤ᵖ*
      )

  units-iso : L.εᵖ L.≈ᵖ L.ιᵖ
  units-iso .proj₁ = L.εᵖ≤ιᵖ
  units-iso .proj₂ .*≤ᵖ* x≤I = x≤I

  module C where
    open Algebra.Ordered.Construction.Chu.Construction
          L.⊸ᵖ-⅋ᵖ-isResiduatedCommutativePomonoid
          L.∧ᵖ-isMeetSemilattice
          L.∨ᵖ-isJoinSemilattice
          L.εᵖ
      public

    K-m : (L.εᵖ L.◁ᵖ L.εᵖ) L.≤ᵖ L.εᵖ
    K-m = L.≤ᵖ-trans (L.◁ᵖ-mono (L.≤ᵖ-reflexive units-iso) L.≤ᵖ-refl) (L.≤ᵖ-reflexive (L.◁ᵖ-identityˡ _))
    
    K-u : L.ιᵖ L.≤ᵖ L.εᵖ
    K-u = L.≤ᵖ-reflexive (L.Eq.sym units-iso)

    open SelfDual L.⅋ᵖ-◁ᵖ-isDuoidal K-m K-u public

    mix : ε ≅ ¬ ε
    mix .proj₁ .fpos = L.≤ᵖ-refl
    mix .proj₁ .fneg = L.≤ᵖ-refl
    mix .proj₂ .fpos = L.≤ᵖ-refl
    mix .proj₂ .fneg = L.≤ᵖ-refl

    ε-eq-ι : ε ≅ ι
    ε-eq-ι .proj₁ .fpos = L.≤ᵖ-reflexive units-iso
    ε-eq-ι .proj₁ .fneg = L.≤ᵖ-reflexive (L.Eq.sym units-iso)
    ε-eq-ι .proj₂ .fpos = L.≤ᵖ-reflexive (L.Eq.sym units-iso)
    ε-eq-ι .proj₂ .fneg = L.≤ᵖ-reflexive units-iso

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
  model .Model.mix = C.mix
  model .Model.⊗-◁-isCommutativeDuoidal = C.⊗-⍮-isCommutativeDuoidal
  model .Model.I-eq-J = C.ε-eq-ι
  model .Model.◁-self-dual = C.self-dual
  model .Model.⊗-isStarAutonomous = C.⊗-isStarAutonomous

  embed : Carrier → Chu
  embed x = C.embed (L.ηᵖ x)
