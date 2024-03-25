{-# OPTIONS --safe --without-K #-}

open import Level using (Level; _⊔_)
open import Algebra.Core
open import Algebra.Definitions
open import Data.Product using (_,_; proj₁; proj₂; swap)
open import Function using (flip)
open import Relation.Binary
import Relation.Binary.PropositionalEquality as PropEq
open import Relation.Binary.Construct.Closure.Symmetric using (SymClosure; fwd; bwd)
import Relation.Binary.Construct.Closure.Symmetric as SymClosure
import Relation.Binary.Construct.Flip.EqAndOrd as Flip
import Relation.Binary.Construct.Intersection as Intersection

module Relation.Binary.Construct.Core.Symmetric where

module _ {a ℓ} {A : Set a} where

  SymCore : Rel A ℓ → Rel A ℓ
  SymCore _≲_ = _≲_ Intersection.∩ (flip _≲_)

  module _ (_≲_ : Rel A ℓ) where

    antisymmetric : Antisymmetric (SymCore _≲_) _≲_
    antisymmetric x₁≲x₂ x₂≲x₁ = (x₁≲x₂ , x₂≲x₁)

    reflexive : Reflexive _≲_ → Reflexive (SymCore _≲_)
    reflexive refl = Intersection.reflexive _≲_ (flip _≲_) refl (Flip.refl _≲_ refl)

    transitive : Transitive _≲_ → Transitive (SymCore _≲_)
    transitive trans = Intersection.transitive _≲_ (flip _≲_) trans (Flip.trans _≲_ trans)

    congruent₁ : {f : Op₁ A} → Congruent₁ _≲_ f → Congruent₁ (SymCore _≲_) f
    congruent₁ cong₁ x = cong₁ (proj₁ x) , cong₁ (proj₂ x)

    congruent₂ : {∙ : Op₂ A} → Congruent₂ _≲_ ∙ → Congruent₂ (SymCore _≲_) ∙
    congruent₂ cong₂ x₁ x₂ = cong₂ (proj₁ x₁) (proj₁ x₂) , cong₂ (proj₂ x₁) (proj₂ x₂)

    module _ {ℓ′} {_≈_ : Rel A ℓ′} (isPreorder : IsPreorder _≈_ _≲_) where

      isPreorder⇒isEquivalence : IsEquivalence (SymCore _≲_)
      isPreorder⇒isEquivalence .IsEquivalence.refl = reflexive (IsPreorder.refl isPreorder)
      isPreorder⇒isEquivalence .IsEquivalence.sym = swap
      isPreorder⇒isEquivalence .IsEquivalence.trans = transitive (IsPreorder.trans isPreorder)

      isPreorder⇒setoid : Setoid a ℓ
      isPreorder⇒setoid .Setoid.Carrier = A
      isPreorder⇒setoid .Setoid._≈_ = SymCore _≲_
      isPreorder⇒setoid .Setoid.isEquivalence = isPreorder⇒isEquivalence

      isPreorder⇒isPreorder : IsPreorder (SymCore _≲_) _≲_
      isPreorder⇒isPreorder .IsPreorder.isEquivalence = isPreorder⇒isEquivalence
      isPreorder⇒isPreorder .IsPreorder.reflexive x≃y = x≃y .proj₁
      isPreorder⇒isPreorder .IsPreorder.trans = IsPreorder.trans isPreorder

      isPreorder⇒preorder : Preorder a ℓ ℓ
      isPreorder⇒preorder .Preorder.Carrier = A
      isPreorder⇒preorder .Preorder._≈_ = SymCore _≲_
      isPreorder⇒preorder .Preorder._≲_ = _≲_
      isPreorder⇒preorder .Preorder.isPreorder = isPreorder⇒isPreorder

      isPreorder⇒isPartialOrder : IsPartialOrder (SymCore _≲_) _≲_
      isPreorder⇒isPartialOrder .IsPartialOrder.isPreorder = isPreorder⇒isPreorder
      isPreorder⇒isPartialOrder .IsPartialOrder.antisym = antisymmetric

      isPreorder⇒poset : Poset a ℓ ℓ
      isPreorder⇒poset .Poset.Carrier = A
      isPreorder⇒poset .Poset._≈_ = SymCore _≲_
      isPreorder⇒poset .Poset._≤_ = _≲_
      isPreorder⇒poset .Poset.isPartialOrder = isPreorder⇒isPartialOrder

    module _ (refl : Reflexive _≲_) (trans : Transitive _≲_) where

      refl,trans⇒≡-≲-isPreorder : IsPreorder PropEq._≡_ _≲_
      refl,trans⇒≡-≲-isPreorder .IsPreorder.isEquivalence = PropEq.isEquivalence
      refl,trans⇒≡-≲-isPreorder .IsPreorder.reflexive PropEq.refl = refl
      refl,trans⇒≡-≲-isPreorder .IsPreorder.trans = trans

      refl,trans⇒isEquivalence : IsEquivalence (SymCore _≲_)
      refl,trans⇒isEquivalence = isPreorder⇒isEquivalence refl,trans⇒≡-≲-isPreorder

      refl,trans⇒setoid : Setoid a ℓ
      refl,trans⇒setoid = isPreorder⇒setoid refl,trans⇒≡-≲-isPreorder

      refl,trans⇒isPreorder : IsPreorder (SymCore _≲_) _≲_
      refl,trans⇒isPreorder = isPreorder⇒isPreorder refl,trans⇒≡-≲-isPreorder

      refl,trans⇒preorder : Preorder a ℓ ℓ
      refl,trans⇒preorder = isPreorder⇒preorder refl,trans⇒≡-≲-isPreorder

      refl,trans⇒isPartialOrder : IsPartialOrder (SymCore _≲_) _≲_
      refl,trans⇒isPartialOrder = isPreorder⇒isPartialOrder refl,trans⇒≡-≲-isPreorder

      refl,trans⇒poset : Poset a ℓ ℓ
      refl,trans⇒poset = isPreorder⇒poset refl,trans⇒≡-≲-isPreorder

    SymCore⇒SymClosure : SymCore _≲_ ⇒ SymClosure _≲_
    SymCore⇒SymClosure (x≲y , _y≲x) = fwd x≲y -- or bwd y≲x
