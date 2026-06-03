{-# OPTIONS --postfix-projections --safe --without-K #-}

module MLL.Model where

open import Level using (suc; _⊔_)
open import Algebra using (_DistributesOver_)
open import Algebra.Ordered
open import Algebra.Ordered.Consequences using (supremum∧residuated⇒distrib)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary using (IsEquivalence; IsPartialOrder)
open import Relation.Binary.Lattice using (IsMeetSemilattice; IsJoinSemilattice)

record Model c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Carrier : Set c
    _≈_     : Carrier → Carrier → Set ℓ₁
    _≲_     : Carrier → Carrier → Set ℓ₂

    ¬       : Carrier → Carrier
    I       : Carrier
    _⊗_     : Carrier → Carrier → Carrier

    ⊗-isStarAutonomous       : IsStarAutonomous _≈_ _≲_ _⊗_ I ¬
    mix                      : I ≈ ¬ I

  open IsStarAutonomous ⊗-isStarAutonomous public
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
      ; ⊗-cong
      ; ⊗-congˡ
      ; ⊗-congʳ
      ; ⊗-mono
      ; ⊗-monoˡ
      ; ⊗-monoʳ
      ; ⊗-assoc
      ; ⊗-identity
      ; ⊗-identityˡ
      ; ⊗-identityʳ
      ; ⊗-comm
      ; ¬-involutive
      ; ¬-mono
      ; ¬-cong
      ; _⅋_
      ; ⅋-mono
      ; ⅋-monoˡ
      ; ⅋-monoʳ
      ; ⅋-cong
      ; ⅋-congˡ
      ; ⅋-congʳ
      ; ⅋-assoc
      ; ⅋-comm
      ; ⅋-identity
      ; ⅋-identityˡ
      ; ⅋-identityʳ
      ; ⊗-⊸-residuated
      ; ev
      ; coev
      ; linear-distrib
      )
