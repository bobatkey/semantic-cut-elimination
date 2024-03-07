{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level using (Level; _⊔_)
open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Definitions using (Congruent₁; Congruent₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; swap)
open import Function using (flip)
open import Relation.Binary using (Rel; Reflexive; Transitive; IsPreorder; IsEquivalence; Setoid)
import Relation.Binary.PropositionalEquality as PropEq

module Relation.Binary.Construct.Core.Symmetric where

import Relation.Binary.Construct.Converse as C
import Relation.Binary.Construct.Intersection as I

module _
    {a ℓ}
    {A : Set a}
  where

  SymCore : Rel A ℓ → Rel A ℓ
  SymCore _∼_ = _∼_ I.∩ (flip _∼_)

  module _ (_∼_ : Rel A ℓ) where

    reflexive : Reflexive _∼_ → Reflexive (SymCore _∼_)
    reflexive refl = I.reflexive _∼_ (flip _∼_) refl (C.refl _∼_ refl)

    transitive : Transitive _∼_ → Transitive (SymCore _∼_)
    transitive trans = I.transitive _∼_ (flip _∼_) trans (C.trans _∼_ trans)

    congruent₁ : {f : Op₁ A} → Congruent₁ _∼_ f → Congruent₁ (SymCore _∼_) f
    congruent₁ cong₁ x = cong₁ (proj₁ x) , cong₁ (proj₂ x)

    congruent₂ : {∙ : Op₂ A} → Congruent₂ _∼_ ∙ → Congruent₂ (SymCore _∼_) ∙
    congruent₂ cong₂ x₁ x₂ = cong₂ (proj₁ x₁) (proj₁ x₂) , cong₂ (proj₂ x₁) (proj₂ x₂)

    module _ {ℓ′} {_≈_ : Rel A ℓ′} where

      isEquivalence : IsPreorder _≈_ _∼_ → IsEquivalence (SymCore _∼_)
      isEquivalence isPreorder .IsEquivalence.refl = reflexive (IsPreorder.refl isPreorder)
      isEquivalence isPreorder .IsEquivalence.sym = swap
      isEquivalence isPreorder .IsEquivalence.trans = transitive (IsPreorder.trans isPreorder)

      isPreorder⇒isPreorder : IsPreorder _≈_ _∼_ → IsPreorder (SymCore _∼_) _∼_
      isPreorder⇒isPreorder isPreorder .IsPreorder.isEquivalence = isEquivalence isPreorder
      isPreorder⇒isPreorder isPreorder .IsPreorder.reflexive x≃y = x≃y .proj₁
      isPreorder⇒isPreorder isPreorder .IsPreorder.trans = IsPreorder.trans isPreorder

      setoid : IsPreorder _≈_ _∼_ →  Setoid a ℓ
      setoid isPreorder .Setoid.Carrier = A 
      setoid isPreorder .Setoid._≈_ = SymCore _∼_
      setoid isPreorder .Setoid.isEquivalence = isEquivalence isPreorder
  
    reflexive-transitive⇒isPreorder : Reflexive _∼_ → Transitive _∼_ → IsPreorder (SymCore _∼_) _∼_
    reflexive-transitive⇒isPreorder refl trans = isPreorder⇒isPreorder ≡-isPreorder
      where
        ≡-isPreorder : IsPreorder PropEq._≡_ _∼_
        ≡-isPreorder .IsPreorder.isEquivalence = PropEq.isEquivalence
        ≡-isPreorder .IsPreorder.reflexive PropEq.refl = reflexive refl .proj₁
        ≡-isPreorder .IsPreorder.trans = trans