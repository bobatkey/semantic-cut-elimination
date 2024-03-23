{-# OPTIONS --postfix-projections --safe --without-K #-}

module MAV.Frame where

open import Level using (suc; _⊔_; Lift; lift; 0ℓ)
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
    _⅋_     : Carrier → Carrier → Carrier
    _▷_     : Carrier → Carrier → Carrier
    _&_     : Carrier → Carrier → Carrier

    ⅋-isCommutativePomonoid : IsCommutativePomonoid _≈_ _≲_ _⅋_ I
    &-mono                  : Monotonic₂ _≲_ _≲_ _≲_ _&_
    ⅋-▷-isDuoidal           : IsDuoidal _≈_ _≲_ _⅋_ _▷_ I I
    ⅋-distrib-&             : _DistributesOver_ _≲_ _⅋_ _&_

    -- FIXME: this is half of IsDuoidal when the first operation is only a semigroup
    &-▷-entropy             : Entropy _≲_ _&_ _▷_
    &-tidy                  : (I & I) ≲ I

  open IsCommutativePomonoid ⅋-isCommutativePomonoid public
  open IsDuoidal ⅋-▷-isDuoidal public
    using (▷-isPomonoid)
    renaming (∙-▷-entropy to ⅋-▷-entropy)


module FrameModel {a ℓ₁ ℓ₂} (F : Frame a ℓ₁ ℓ₂) where

  import Algebra.PreSheaf
  import Algebra.Sheaf
  import Algebra.Chu

  open Frame F

  module P = Algebra.PreSheaf (record { isPartialOrder = isPartialOrder })

  module M = P.LiftIsCommutativePomonoid ⅋-isCommutativePomonoid

  module S = Algebra.Sheaf (record { isPomagma = record { isPartialOrder = isPartialOrder
                                                        ; mono = &-mono } })

  module MS = S.LiftIsCommutativePomonoid ⅋-isCommutativePomonoid ⅋-distrib-&

  module M▷ = S.LiftIsPomonoid ▷-isPomonoid &-▷-entropy &-tidy

  module D = S.LiftIsDuoidal ⅋-▷-isDuoidal comm ⅋-distrib-& &-▷-entropy &-tidy

  open S._≤ˢ_
  open S.Sheaf

  units-iso : MS.εˢ S.≈ˢ M▷.ιˢ
  units-iso .proj₁ .*≤ˢ* {x} (t , x≤t) = M▷.ιˢ .≤-closed x≤t (M▷.ιˢ .∨-closed t)
  units-iso .proj₂ .*≤ˢ* {x} x≤I = S.leaf (x , x≤I) , refl

  open Algebra.Chu.Construction
                MS.⊸ˢ-⊗ˢ-isResiduatedCommutativePomonoid
                S.∧ˢ-isMeetSemilattice
                S.∨ˢ-isJoinSemilattice
                MS.εˢ
      using (Chu; _==>_; module SelfDual; _≅_;
             ⊗-isCommutativePomonoid;
             ⊗-isStarAutonomous;
             &-isMeet)
      renaming (_⊗_ to _⟦⊗⟧_;
                _&_ to _⟦&⟧_;
                I to ⟦I⟧;
                ¬ to ⟦¬⟧)
      public

  open Chu
  open _==>_
  open SelfDual
      D.⊗ˢ-▷ˢ-isDuoidal
      (S.≤ˢ-trans (M▷.▷ˢ-mono (S.≤ˢ-reflexive units-iso) S.≤ˢ-refl)
                  (S.≤ˢ-reflexive (M▷.▷ˢ-identityˡ _)))
      (S.≤ˢ-reflexive (S.Eq.sym units-iso))

  Chu-mix : ⟦I⟧ ≅ ⟦¬⟧ ⟦I⟧
  Chu-mix .proj₁ .fpos = S.≤ˢ-refl
  Chu-mix .proj₁ .fneg = S.≤ˢ-refl
  Chu-mix .proj₂ .fpos = S.≤ˢ-refl
  Chu-mix .proj₂ .fneg = S.≤ˢ-refl

  I-eq-J : ⟦I⟧ ≅ J
  I-eq-J .proj₁ .fpos = S.≤ˢ-reflexive units-iso
  I-eq-J .proj₁ .fneg = S.≤ˢ-reflexive (S.Eq.sym units-iso)
  I-eq-J .proj₂ .fpos = S.≤ˢ-reflexive (S.Eq.sym units-iso)
  I-eq-J .proj₂ .fneg = S.≤ˢ-reflexive units-iso

  tidyup-lem : (t : S.Tree (Σ[ P ∈ Carrier ] (Lift a (P ≲ I)))) →
               S.⋁ᵗ t ≲ I
  tidyup-lem (S.leaf (P , lift p⟶⋆I)) = p⟶⋆I
  tidyup-lem (S.node S t) = trans (&-mono (tidyup-lem S) (tidyup-lem t)) &-tidy

  tidyup : ∀ {P} → MS.εˢ .ICarrier P → P ≲ I
  tidyup (t , p⟶⋆t) = trans p⟶⋆t (tidyup-lem t)

  model : Model (suc (suc (a ⊔ ℓ₂))) (a ⊔ ℓ₂) (a ⊔ ℓ₂)
  model .Model.Carrier = Chu
  model .Model._≈_ = _≅_
  model .Model._≲_ = _==>_
  model .Model.¬ = ⟦¬⟧
  model .Model.I = ⟦I⟧
  model .Model.J = J
  model .Model._⊗_ = _⟦⊗⟧_
  model .Model._▷_ = _⍮_
  model .Model._&_ = _⟦&⟧_
  model .Model.⊗-isCommutativePomonoid = ⊗-isCommutativePomonoid
  model .Model.⊗-isStarAutonomous = ⊗-isStarAutonomous
  model .Model.mix = Chu-mix
  model .Model.&-isMeet = &-isMeet
  model .Model.⊗-▷-isDuoidal = ⊗-⍮-isDuoidal
  model .Model.I-eq-J = I-eq-J
  model .Model.▷-self-dual = self-dual

  -- FIXME: move this to Algebra.Chu
  embed : Carrier → Chu
  embed x .pos = S.α (P.ηᵖ x)
  embed x .neg = S.α (P.ηᵖ x) MS.⊸ˢ MS.εˢ
  embed x .int = MS.⊸ˢ-residual-from S.≤ˢ-refl

  embedDual : (a⁺ a⁻ : Carrier) → (a⁺ ⅋ a⁻) ≲ I → Chu
  embedDual a⁺ a⁻ interact .pos = S.α (P.ηᵖ a⁺)
  embedDual a⁺ a⁻ interact .neg = S.α (P.ηᵖ a⁻)
  embedDual a⁺ a⁻ interact .int =
    S.≤ˢ-trans (MS.α-monoidal .proj₁) (S.α-mono interactᵖ)
    where
      interactᵖ : (P.ηᵖ a⁺ M.∙ᵖ P.ηᵖ a⁻) P.≤ᵖ M.εᵖ
      interactᵖ .P.*≤ᵖ* (x₁ , x₂ , x≤x₁x₂ , lift x₁≤a⁺ , lift x₂≤a⁻) =
        lift (trans x≤x₁x₂ (trans (mono x₁≤a⁺ x₂≤a⁻) interact))
