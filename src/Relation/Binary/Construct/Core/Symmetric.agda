{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level using (Level; _⊔_)
open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Definitions using (Congruent₁; Congruent₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; swap)
open import Function using (flip)
open import Relation.Binary.Bundles using (Preorder; Poset)
open import Relation.Binary using (Rel; Antisymmetric; Reflexive; Transitive; IsPreorder; IsPartialOrder; IsEquivalence; Setoid)
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

    antisymmetric : Antisymmetric (SymCore _∼_) _∼_
    antisymmetric x₁∼x₂ x₂∼x₁ = (x₁∼x₂ , x₂∼x₁)

    reflexive : Reflexive _∼_ → Reflexive (SymCore _∼_)
    reflexive refl = I.reflexive _∼_ (flip _∼_) refl (C.refl _∼_ refl)

    transitive : Transitive _∼_ → Transitive (SymCore _∼_)
    transitive trans = I.transitive _∼_ (flip _∼_) trans (C.trans _∼_ trans)

    congruent₁ : {f : Op₁ A} → Congruent₁ _∼_ f → Congruent₁ (SymCore _∼_) f
    congruent₁ cong₁ x = cong₁ (proj₁ x) , cong₁ (proj₂ x)

    congruent₂ : {∙ : Op₂ A} → Congruent₂ _∼_ ∙ → Congruent₂ (SymCore _∼_) ∙
    congruent₂ cong₂ x₁ x₂ = cong₂ (proj₁ x₁) (proj₁ x₂) , cong₂ (proj₂ x₁) (proj₂ x₂)

    module _ {ℓ′} {_≈_ : Rel A ℓ′} where

      isPreorder⇒isEquivalence : IsPreorder _≈_ _∼_ → IsEquivalence (SymCore _∼_)
      isPreorder⇒isEquivalence isPreorder .IsEquivalence.refl = reflexive (IsPreorder.refl isPreorder)
      isPreorder⇒isEquivalence isPreorder .IsEquivalence.sym = swap
      isPreorder⇒isEquivalence isPreorder .IsEquivalence.trans = transitive (IsPreorder.trans isPreorder)

      isPreorder⇒isPreorder : IsPreorder _≈_ _∼_ → IsPreorder (SymCore _∼_) _∼_
      isPreorder⇒isPreorder isPreorder .IsPreorder.isEquivalence = isPreorder⇒isEquivalence isPreorder
      isPreorder⇒isPreorder isPreorder .IsPreorder.reflexive x≃y = x≃y .proj₁
      isPreorder⇒isPreorder isPreorder .IsPreorder.trans = IsPreorder.trans isPreorder

      isPreorder⇒setoid : IsPreorder _≈_ _∼_ → Setoid a ℓ
      isPreorder⇒setoid isPreorder .Setoid.Carrier = A 
      isPreorder⇒setoid isPreorder .Setoid._≈_ = SymCore _∼_
      isPreorder⇒setoid isPreorder .Setoid.isEquivalence = isPreorder⇒isEquivalence isPreorder

      isPreorder⇒isPartialOrder : IsPreorder _≈_ _∼_ → IsPartialOrder (SymCore _∼_) _∼_
      isPreorder⇒isPartialOrder isPreorder .IsPartialOrder.isPreorder = isPreorder⇒isPreorder isPreorder
      isPreorder⇒isPartialOrder isPreorder .IsPartialOrder.antisym = antisymmetric
  
    module _
        (refl : Reflexive _∼_)
        (trans : Transitive _∼_)
      where

      refl,trans⇒isPreorder-≡ : IsPreorder PropEq._≡_ _∼_
      refl,trans⇒isPreorder-≡ .IsPreorder.isEquivalence = PropEq.isEquivalence
      refl,trans⇒isPreorder-≡ .IsPreorder.reflexive PropEq.refl = refl
      refl,trans⇒isPreorder-≡ .IsPreorder.trans = trans

      refl,trans⇒isPreorder : IsPreorder (SymCore _∼_) _∼_
      refl,trans⇒isPreorder = isPreorder⇒isPreorder refl,trans⇒isPreorder-≡

      refl,trans⇒preorder : Preorder a ℓ ℓ
      refl,trans⇒preorder .Preorder.Carrier = A
      refl,trans⇒preorder .Preorder._≈_ = SymCore _∼_
      refl,trans⇒preorder .Preorder._∼_ = _∼_
      refl,trans⇒preorder .Preorder.isPreorder = refl,trans⇒isPreorder

      refl,trans⇒isPartialOrder : IsPartialOrder (SymCore _∼_) _∼_
      refl,trans⇒isPartialOrder = isPreorder⇒isPartialOrder refl,trans⇒isPreorder-≡

      refl,trans⇒poset : Poset a ℓ ℓ
      refl,trans⇒poset .Poset.Carrier = A
      refl,trans⇒poset .Poset._≈_ = SymCore _∼_
      refl,trans⇒poset .Poset._≤_ = _∼_
      refl,trans⇒poset .Poset.isPartialOrder = refl,trans⇒isPartialOrder
  
      refl,trans⇒setoid : Setoid a ℓ
      refl,trans⇒setoid = isPreorder⇒setoid refl,trans⇒isPreorder
       