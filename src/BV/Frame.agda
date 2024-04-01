{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level using (suc; _⊔_; Lift; lift; 0ℓ; lower)
open import Algebra.Ordered
open import Algebra.Ordered.Structures.Duoidal
open import Algebra using (_DistributesOver_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax)
open import Relation.Binary

module BV.Frame where

open import BV.Model

record Frame c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Carrier : Set c
    _≈_     : Carrier → Carrier → Set ℓ₁
    _≲_     : Carrier → Carrier → Set ℓ₂
    
    I       : Carrier
    _◁_     : Carrier → Carrier → Carrier
    _⅋_     : Carrier → Carrier → Carrier

    ⅋-isCommutativePomonoid : IsCommutativePomonoid _≈_ _≲_ _⅋_ I
    ⅋-◁-isDuoidal           : IsDuoidal _≈_ _≲_ _⅋_ _◁_ I I

  open IsCommutativePomonoid ⅋-isCommutativePomonoid public
  open IsDuoidal ⅋-◁-isDuoidal public
    using (◁-isPomonoid)
    renaming (∙-◁-entropy to ⅋-◁-entropy)


module FrameModel {a ℓ₁ ℓ₂} (F : Frame a ℓ₁ ℓ₂) where

  import Algebra.Ordered.Construction.LowerSet as LowerSet
  import Algebra.Ordered.Construction.Chu as Chu

  open Frame F

  module P = LowerSet (record { isPartialOrder = isPartialOrder })
  module M = P.LiftIsCommutativePomonoid ⅋-isCommutativePomonoid
  module D = P.LiftIsDuoidal ⅋-◁-isDuoidal

  open P._≤ᵖ_
  open P.PreSheaf

  units-iso : M.εᵖ P.≈ᵖ D.ιᵖ
  units-iso .proj₁ = D.εᵖ≤ιᵖ
  units-iso .proj₂ .*≤ᵖ* x≤I = x≤I

  -- FIXME: Separate Chu construction from additives

  -- open Algebra.Ordered.Construction.Chu.Construction
  --               MS.⊸ⁱ-∙ⁱ-isResiduatedCommutativePomonoid
  --               S.∧ⁱ-isMeetSemilattice
  --               S.∨ⁱ-isJoinSemilattice
  --               MS.εⁱ
  --     using (Chu; _==>_; module SelfDual; _≅_;
  --            ==>-trans;
  --            ⊗-isCommutativePomonoid;
  --            ⊗-isStarAutonomous;
  --            &-isMeet)
  --     renaming (_⊗_ to _⟦⊗⟧_;
  --               _&_ to _⟦&⟧_;
  --               I to ⟦I⟧;
  --               ¬ to ⟦¬⟧;
  --               embed to Chu-embed)
  --     public

  -- open Chu
  -- open _==>_
  -- open SelfDual
  --     D.∙ⁱ-◁ⁱ-isDuoidal
  --     (S.≤ⁱ-trans (M◁.◁ⁱ-mono (S.≤ⁱ-reflexive units-iso) S.≤ⁱ-refl)
  --                 (S.≤ⁱ-reflexive (M◁.◁ⁱ-identityˡ _)))
  --     (S.≤ⁱ-reflexive (S.Eq.sym units-iso))

  -- Chu-mix : ⟦I⟧ ≅ ⟦¬⟧ ⟦I⟧
  -- Chu-mix .proj₁ .fpos = S.≤ⁱ-refl
  -- Chu-mix .proj₁ .fneg = S.≤ⁱ-refl
  -- Chu-mix .proj₂ .fpos = S.≤ⁱ-refl
  -- Chu-mix .proj₂ .fneg = S.≤ⁱ-refl

  -- I-eq-J : ⟦I⟧ ≅ J
  -- I-eq-J .proj₁ .fpos = S.≤ⁱ-reflexive units-iso
  -- I-eq-J .proj₁ .fneg = S.≤ⁱ-reflexive (S.Eq.sym units-iso)
  -- I-eq-J .proj₂ .fpos = S.≤ⁱ-reflexive (S.Eq.sym units-iso)
  -- I-eq-J .proj₂ .fneg = S.≤ⁱ-reflexive units-iso

  -- model : Model (suc (suc (a ⊔ ℓ₂))) (a ⊔ ℓ₂) (a ⊔ ℓ₂)
  -- model .Model.Carrier = Chu
  -- model .Model._≈_ = _≅_
  -- model .Model._≲_ = _==>_
  -- model .Model.¬ = ⟦¬⟧
  -- model .Model.I = ⟦I⟧
  -- model .Model.J = J
  -- model .Model._⊗_ = _⟦⊗⟧_
  -- model .Model._◁_ = _⍮_
  -- model .Model._&_ = _⟦&⟧_
  -- model .Model.⊗-isCommutativePomonoid = ⊗-isCommutativePomonoid
  -- model .Model.⊗-isStarAutonomous = ⊗-isStarAutonomous
  -- model .Model.mix = Chu-mix
  -- model .Model.&-isMeet = &-isMeet
  -- model .Model.⊗-◁-isDuoidal = ⊗-⍮-isDuoidal
  -- model .Model.I-eq-J = I-eq-J
  -- model .Model.◁-self-dual = self-dual

  -- embed : Carrier → Chu
  -- embed x = Chu-embed (S.ηⁱ x)
