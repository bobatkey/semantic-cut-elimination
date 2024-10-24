------------------------------------------------------------------------
-- The Agda standard library
--
-- Ordered algebraic structures (not packed up with sets, orders,
-- operations, etc.)
------------------------------------------------------------------------

-- The contents of this module should be accessed via
-- `Algebra.Ordered`.

{-# OPTIONS --postfix-projections --without-K --safe --cubical-compatible #-}

open import Relation.Binary.Core using (Rel; _⇒_)

module Algebra.Ordered.Structures
  {a ℓ₁ ℓ₂} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ₁)       -- The underlying equality relation
  (_≲_ : Rel A ℓ₂)       -- The underlying order relation
  where

open import Algebra.Core
open import Algebra.Definitions _≈_
open import Algebra.Structures _≈_
open import Algebra.Ordered.Consequences
open import Algebra.Ordered.Definitions _≲_
open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (flip; _$_)
open import Function.EquiInhabited using (_↔_)
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Binary.Consequences using (mono₂⇒cong₂)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
import Relation.Binary.Reasoning.PartialOrder as PosetReasoning

------------------------------------------------------------------------
-- Preordered structures

-- Preordered magmas (promagmas)

record IsPromagma (∙ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPreorder  : IsPreorder _≈_ _≲_
    ∙-cong      : Congruent₂ ∙
    mono        : Monotonic₂ _≲_ _≲_ _≲_ ∙

  open IsPreorder isPreorder public

  monoˡ : ∀ {x} → Monotonic₁ _≲_ _≲_ (flip ∙ x)
  monoˡ y≈z = mono y≈z refl

  monoʳ : ∀ {x} → Monotonic₁ _≲_ _≲_ (∙ x)
  monoʳ y≈z = mono refl y≈z

  isMagma : IsMagma ∙
  isMagma = record { isEquivalence = isEquivalence ; ∙-cong = ∙-cong }

  open IsMagma isMagma public
    using
      ( setoid
      ; ∙-congˡ
      ; ∙-congʳ
      )

-- Preordered semigroups (prosemigroups)

record IsProsemigroup (∙ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPromagma  : IsPromagma ∙
    assoc       : Associative ∙

  open IsPromagma isPromagma public

  isSemigroup : IsSemigroup ∙
  isSemigroup = record { isMagma = isMagma ; assoc = assoc }

-- Preordered monoids (promonoids)

record IsPromonoid (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isProsemigroup : IsProsemigroup ∙
    identity       : Identity ε ∙

  open IsProsemigroup isProsemigroup public

  isMonoid : IsMonoid ∙ ε
  isMonoid = record { isSemigroup = isSemigroup ; identity = identity }

  open IsMonoid isMonoid public using (identityˡ; identityʳ)

-- Preordered commutative monoids (commutative promonoids)

record IsCommutativePromonoid (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPromonoid : IsPromonoid ∙ ε
    comm        : Commutative ∙

  open IsPromonoid isPromonoid public

  isCommutativeMonoid : IsCommutativeMonoid ∙ ε
  isCommutativeMonoid = record { isMonoid = isMonoid ; comm = comm }

  open IsCommutativeMonoid isCommutativeMonoid public
    using (isCommutativeSemigroup)

-- Preordered semirings (prosemirings)

record IsProsemiring (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    +-isCommutativePromonoid : IsCommutativePromonoid + 0#
    *-cong                   : Congruent₂ *
    *-mono                   : Monotonic₂ _≲_ _≲_ _≲_ *
    *-assoc                  : Associative *
    *-identity               : Identity 1# *
    distrib                  : * DistributesOver +
    zero                     : Zero 0# *

  open IsCommutativePromonoid +-isCommutativePromonoid public
    renaming
    ( assoc                  to +-assoc
    ; ∙-cong                 to +-cong
    ; ∙-congˡ                to +-congˡ
    ; ∙-congʳ                to +-congʳ
    ; mono                   to +-mono
    ; monoˡ                  to +-monoˡ
    ; monoʳ                  to +-monoʳ
    ; identity               to +-identity
    ; identityˡ              to +-identityˡ
    ; identityʳ              to +-identityʳ
    ; comm                   to +-comm
    ; isMagma                to +-isMagma
    ; isSemigroup            to +-isSemigroup
    ; isMonoid               to +-isMonoid
    ; isCommutativeSemigroup to +-isCommutativeSemigroup
    ; isCommutativeMonoid    to +-isCommutativeMonoid
    )

  *-isPromonoid : IsPromonoid * 1#
  *-isPromonoid = record
    { isProsemigroup = record
      { isPromagma   = record
        { isPreorder = isPreorder
        ; ∙-cong     = *-cong
        ; mono       = *-mono
        }
      ; assoc        = *-assoc
      }
    ; identity       = *-identity
    }

  open IsPromonoid *-isPromonoid public
    using
      (
      )
    renaming
      ( ∙-congˡ     to *-congˡ
      ; ∙-congʳ     to *-congʳ
      ; monoˡ       to *-monoˡ
      ; monoʳ       to *-monoʳ
      ; identityˡ   to *-identityˡ
      ; identityʳ   to *-identityʳ
      ; isMagma     to *-isMagma
      ; isSemigroup to *-isSemigroup
      ; isMonoid    to *-isMonoid
      )

  isSemiring : IsSemiring + * 0# 1#
  isSemiring = record
    { isSemiringWithoutAnnihilatingZero = record
      { +-isCommutativeMonoid           = +-isCommutativeMonoid
      ; *-cong                          = *-cong
      ; *-assoc                         = *-assoc
      ; *-identity                      = *-identity
      ; distrib                         = distrib
      }
    ; zero                              = zero
    }

  open IsSemiring isSemiring public using (distribˡ; distribʳ; zeroˡ; zeroʳ)

------------------------------------------------------------------------
-- Partially ordered structures

-- Partially ordered magmas (pomagmas)

record IsPomagma (∙ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPartialOrder : IsPartialOrder _≈_ _≲_
    mono           : Monotonic₂ _≲_ _≲_ _≲_ ∙

  open IsPartialOrder isPartialOrder public

  ∙-cong : Congruent₂ ∙
  ∙-cong = mono₂⇒cong₂ _≈_ _≈_ Eq.sym reflexive antisym mono

  isPromagma : IsPromagma ∙
  isPromagma = record
    { isPreorder = isPreorder
    ; ∙-cong     = ∙-cong
    ; mono       = mono
    }

  open IsPromagma isPromagma public
    using
      ( setoid
      ; ∙-congˡ
      ; ∙-congʳ
      ; monoˡ
      ; monoʳ
      ; isMagma
      )

-- Partially ordered semigroups (posemigroups)

record IsPosemigroup (∙ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPomagma : IsPomagma ∙
    assoc     : Associative ∙

  open IsPomagma isPomagma public

  isProsemigroup : IsProsemigroup ∙
  isProsemigroup = record { isPromagma = isPromagma ; assoc = assoc }

  open IsProsemigroup isProsemigroup public using (isSemigroup)

-- Partially ordered monoids (pomonoids)

record IsPomonoid (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPosemigroup : IsPosemigroup ∙
    identity      : Identity ε ∙

  open IsPosemigroup isPosemigroup public

  isPromonoid : IsPromonoid ∙ ε
  isPromonoid = record
    { isProsemigroup = isProsemigroup
    ; identity       = identity
    }

  open IsPromonoid isPromonoid public
    using
      ( isMonoid
      ; identityˡ
      ; identityʳ
      )

-- Partially ordered commutative monoids (commutative pomonoids)

record IsCommutativePomonoid (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPomonoid : IsPomonoid ∙ ε
    comm       : Commutative ∙

  open IsPomonoid isPomonoid public

  isCommutativePromonoid : IsCommutativePromonoid ∙ ε
  isCommutativePromonoid = record { isPromonoid = isPromonoid ; comm = comm }

  open IsCommutativePromonoid isCommutativePromonoid public
    using
      ( isCommutativeMonoid
      ; isCommutativeSemigroup
      )

-- Partially ordered semirings (posemirings)

record IsPosemiring (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    +-isCommutativePomonoid : IsCommutativePomonoid + 0#
    *-mono                  : Monotonic₂ _≲_ _≲_ _≲_ *
    *-assoc                 : Associative *
    *-identity              : Identity 1# *
    distrib                 : * DistributesOver +
    zero                    : Zero 0# *

  open IsCommutativePomonoid +-isCommutativePomonoid public
    renaming
    ( assoc                  to +-assoc
    ; ∙-cong                 to +-cong
    ; ∙-congˡ                to +-congˡ
    ; ∙-congʳ                to +-congʳ
    ; mono                   to +-mono
    ; monoˡ                  to +-monoˡ
    ; monoʳ                  to +-monoʳ
    ; identity               to +-identity
    ; identityˡ              to +-identityˡ
    ; identityʳ              to +-identityʳ
    ; comm                   to +-comm
    ; isMagma                to +-isMagma
    ; isPromagma             to +-isPromagma
    ; isPomagma              to +-isPomagma
    ; isSemigroup            to +-isSemigroup
    ; isProsemigroup         to +-isProsemigroup
    ; isPosemigroup          to +-isPosemigroup
    ; isMonoid               to +-isMonoid
    ; isPromonoid            to +-isPromonoid
    ; isPomonoid             to +-isPomonoid
    ; isCommutativeSemigroup to +-isCommutativeSemigroup
    ; isCommutativeMonoid    to +-isCommutativeMonoid
    ; isCommutativePromonoid to +-isCommutativePromonoid
    )

  *-isPomonoid : IsPomonoid * 1#
  *-isPomonoid = record
    { isPosemigroup      = record
      { isPomagma        = record
        { isPartialOrder = isPartialOrder
        ; mono           = *-mono
        }
      ; assoc            = *-assoc
      }
    ; identity           = *-identity
    }

  open IsPomonoid *-isPomonoid public
    using ()
    renaming
    ( ∙-cong         to *-cong
    ; ∙-congˡ        to *-congˡ
    ; ∙-congʳ        to *-congʳ
    ; monoˡ          to *-monoˡ
    ; monoʳ          to *-monoʳ
    ; identityˡ      to *-identityˡ
    ; identityʳ      to *-identityʳ
    ; isMagma        to *-isMagma
    ; isPromagma     to *-isPromagma
    ; isPomagma      to *-isPomagma
    ; isSemigroup    to *-isSemigroup
    ; isProsemigroup to *-isProsemigroup
    ; isPosemigroup  to *-isPosemigroup
    ; isMonoid       to *-isMonoid
    ; isPromonoid    to *-isPromonoid
    )

  isProsemiring : IsProsemiring + * 0# 1#
  isProsemiring = record
    { +-isCommutativePromonoid = +-isCommutativePromonoid
    ; *-cong                   = *-cong
    ; *-mono                   = *-mono
    ; *-assoc                  = *-assoc
    ; *-identity               = *-identity
    ; distrib                  = distrib
    ; zero                     = zero
    }

  open IsProsemiring isProsemiring public
    using (isSemiring; distribˡ; distribʳ; zeroˡ; zeroʳ)

------------------------------------------------------------------------------
-- Residuated monoids

record IsResiduatedPromagma (∙ ⇦ ⇨ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPromagma : IsPromagma ∙
    residuated : Residuated ∙ ⇦ ⇨

  open IsPromagma isPromagma public

  residualˡ : LeftResidual ∙ ⇦
  residualˡ = proj₁ residuated

  residualʳ : RightResidual ∙ ⇨
  residualʳ = proj₂ residuated

  evalˡ : LeftEval ∙ ⇦
  evalˡ = residualˡ ._↔_.from refl

  evalʳ : RightEval ∙ ⇨
  evalʳ = residualʳ ._↔_.from refl

  mono-antiˡ : MonotonicAntitonic _≲_ _≲_ _≲_ ⇦
  mono-antiˡ w≲x z≲y
    = residualˡ .to
    $ flip trans w≲x
    $ residualʳ .from
    $ trans z≲y
    $ residualʳ .to
    $ residualˡ .from refl
    where open _↔_ using (to; from)

  anti-monoʳ : AntitonicMonotonic _≲_ _≲_ _≲_ ⇨
  anti-monoʳ {w} {x} {y} {z} x≲w y≲z
    = residualʳ .to
    $ flip trans y≲z
    $ residualˡ .from
    $ trans x≲w
    $ residualˡ .to
    $ residualʳ .from refl
    where open _↔_ using (to; from)

record IsResiduatedProsemigroup (∙ ⇦ ⇨ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isProsemigroup : IsProsemigroup ∙
    residuated : Residuated ∙ ⇦ ⇨

  open IsProsemigroup isProsemigroup public

  isResiduatedPromagma : IsResiduatedPromagma ∙ ⇦ ⇨
  isResiduatedPromagma = record { isPromagma = isPromagma ; residuated = residuated }

  open IsResiduatedPromagma isResiduatedPromagma public
    using ( residualˡ
          ; residualʳ
          ; evalˡ
          ; evalʳ
          ; mono-antiˡ
          ; anti-monoʳ
          )

record IsResiduatedPromonoid (∙ ⇦ ⇨ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPromonoid : IsPromonoid ∙ ε
    residuated : Residuated ∙ ⇦ ⇨

  open IsPromonoid isPromonoid public

  isResiduatedProsemigroup : IsResiduatedProsemigroup ∙ ⇦ ⇨
  isResiduatedProsemigroup = record { isProsemigroup = isProsemigroup ; residuated = residuated }

  open IsResiduatedProsemigroup isResiduatedProsemigroup public
    using ( residualˡ
          ; residualʳ
          ; evalˡ
          ; evalʳ
          ; mono-antiˡ
          ; anti-monoʳ
          )

record IsResiduatedCommutativePromonoid (∙ ⇨ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isCommutativePromonoid : IsCommutativePromonoid ∙ ε
    residuated             : Residuated ∙ (flip ⇨) ⇨

  open IsCommutativePromonoid isCommutativePromonoid public

  isResiduatedPromonoid : IsResiduatedPromonoid ∙ (flip ⇨) ⇨ ε
  isResiduatedPromonoid = record { isPromonoid = isPromonoid ; residuated = residuated }

  open IsResiduatedPromonoid isResiduatedPromonoid public
    using ( residualˡ
          ; residualʳ
          ; evalˡ
          ; evalʳ
          ; mono-antiˡ
          ; anti-monoʳ
          )

record IsResiduatedPomagma (∙ ⇦ ⇨ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPomagma  : IsPomagma ∙
    residuated : Residuated ∙ ⇦ ⇨

  open IsPomagma isPomagma public

  isResiduatedPromagma : IsResiduatedPromagma ∙ ⇦ ⇨
  isResiduatedPromagma = record { isPromagma = isPromagma ; residuated = residuated }

  open IsResiduatedPromagma isResiduatedPromagma public
    using ( residualˡ
          ; residualʳ
          ; evalˡ
          ; evalʳ
          ; mono-antiˡ
          ; anti-monoʳ
          )

record IsResiduatedPosemigroup (∙ ⇦ ⇨ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPosemigroup : IsPosemigroup ∙
    residuated : Residuated ∙ ⇦ ⇨

  open IsPosemigroup isPosemigroup public

  isResiduatedProsemigroup : IsResiduatedProsemigroup ∙ ⇦ ⇨
  isResiduatedProsemigroup = record { isProsemigroup = isProsemigroup ; residuated = residuated }

  open IsResiduatedProsemigroup isResiduatedProsemigroup public
    using ( residualˡ
          ; residualʳ
          ; evalˡ
          ; evalʳ
          ; mono-antiˡ
          ; anti-monoʳ
          )

record IsResiduatedPomonoid (∙ ⇦ ⇨ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPomonoid : IsPomonoid ∙ ε
    residuated : Residuated ∙ ⇦ ⇨

  open IsPomonoid isPomonoid public

  isResiduatedPromonoid : IsResiduatedPromonoid ∙ ⇦ ⇨ ε
  isResiduatedPromonoid = record { isPromonoid = isPromonoid ; residuated = residuated }

  open IsResiduatedPromonoid isResiduatedPromonoid public
    using ( residualˡ
          ; residualʳ
          ; evalˡ
          ; evalʳ
          ; mono-antiˡ
          ; anti-monoʳ
          )

record IsResiduatedCommutativePomonoid (∙ ⇨ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isCommutativePomonoid : IsCommutativePomonoid ∙ ε
    residuated : Residuated ∙ (flip ⇨) ⇨

  open IsCommutativePomonoid isCommutativePomonoid public

  isResiduatedCommutativePromonoid : IsResiduatedCommutativePromonoid ∙ ⇨ ε
  isResiduatedCommutativePromonoid = record { isCommutativePromonoid = isCommutativePromonoid ; residuated = residuated }

  open IsResiduatedCommutativePromonoid isResiduatedCommutativePromonoid public
    using ( residualˡ
          ; residualʳ
          ; evalˡ
          ; evalʳ
          ; mono-antiˡ
          ; anti-monoʳ
          )

------------------------------------------------------------------------------
-- Duoidal structures

record IsDuoidal (∙ ◁ : Op₂ A) (ε ι : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    ∙-isPomonoid : IsPomonoid ∙ ε
    ◁-isPomonoid : IsPomonoid ◁ ι
    ∙-◁-entropy  : Entropy ∙ ◁
    ∙-idem-ι     : ∙ SubidempotentOn ι
    ◁-idem-ε     : ◁ SuperidempotentOn ε
    ε≲ι          : ε ≲ ι

  open IsPomonoid ∙-isPomonoid public
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
      ; ∙-cong
      ; ∙-congˡ
      ; ∙-congʳ
      )
    renaming
      ( isMagma        to ∙-isMagma
      ; isSemigroup    to ∙-isSemigroup
      ; isMonoid       to ∙-isMonoid
      ; isPromagma     to ∙-isPromagma
      ; isProsemigroup to ∙-isProsemigroup
      ; isPromonoid    to ∙-isPromonoid
      ; isPomagma      to ∙-isPomagma
      ; isPosemigroup  to ∙-isPosemigroup
      ; assoc          to ∙-assoc
      ; identity       to ∙-identity
      ; identityˡ      to ∙-identityˡ
      ; identityʳ      to ∙-identityʳ
      ; mono           to ∙-mono
      ; monoˡ          to ∙-monoˡ
      ; monoʳ          to ∙-monoʳ
      )
  open IsPomonoid ◁-isPomonoid public
    hiding
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
    renaming
      ( isMagma        to ◁-isMagma
      ; isSemigroup    to ◁-isSemigroup
      ; isMonoid       to ◁-isMonoid
      ; isPromagma     to ◁-isPromagma
      ; isProsemigroup to ◁-isProsemigroup
      ; isPromonoid    to ◁-isPromonoid
      ; isPomagma      to ◁-isPomagma
      ; isPosemigroup  to ◁-isPosemigroup
      ; assoc          to ◁-assoc
      ; identity       to ◁-identity
      ; identityˡ      to ◁-identityˡ
      ; identityʳ      to ◁-identityʳ
      ; mono           to ◁-mono
      ; monoˡ          to ◁-monoˡ
      ; monoʳ          to ◁-monoʳ
      ; ∙-cong         to ◁-cong
      ; ∙-congˡ        to ◁-congˡ
      ; ∙-congʳ        to ◁-congʳ
      )

record IsCommutativeDuoidal (∙ ◁ : Op₂ A) (ε ι : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isDuoidal : IsDuoidal ∙ ◁ ε ι
    ∙-comm    : Commutative ∙

  open IsDuoidal isDuoidal public

  ∙-isCommutativePomonoid : IsCommutativePomonoid ∙ ε
  ∙-isCommutativePomonoid = record
    { isPomonoid = ∙-isPomonoid
    ; comm       = ∙-comm
    }

record IsStarAutonomous (_⊗_ : Op₂ A) (ε : A) (¬ : A → A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isCommutativePomonoid : IsCommutativePomonoid _⊗_ ε
    ¬-mono                : Antitonic₁ _≲_ _≲_ ¬
    ¬-involutive          : Involutive ¬
    *-aut                 : ∀ {x y z} → (x ⊗ y) ≲ ¬ z → x ≲ ¬ (y ⊗ z)
    *-aut⁻¹               : ∀ {x y z} → x ≲ ¬ (y ⊗ z) → (x ⊗ y) ≲ ¬ z

  open IsCommutativePomonoid isCommutativePomonoid public
    using
      ( refl
      ; trans
      ; reflexive
      ; antisym
      ; ≤-resp-≈
      ; ≤-respˡ-≈
      ; ≤-respʳ-≈
      ; module Eq
      ; setoid
      ; isEquivalence
      ; isPreorder
      ; isPartialOrder
      )
    renaming
      ( mono      to ⊗-mono
      ; monoˡ     to ⊗-monoˡ
      ; monoʳ     to ⊗-monoʳ
      ; ∙-cong    to ⊗-cong
      ; ∙-congˡ   to ⊗-congˡ
      ; ∙-congʳ   to ⊗-congʳ
      ; assoc     to ⊗-assoc
      ; comm      to ⊗-comm
      ; identity  to ⊗-identity
      ; identityˡ to ⊗-identityˡ
      ; identityʳ to ⊗-identityʳ
      )

  poset : Poset _ _ _
  poset = record { isPartialOrder = isPartialOrder }

  ¬-cong : ∀ {x y} → x ≈ y → ¬ x ≈ ¬ y
  ¬-cong x≈y = antisym (¬-mono (reflexive (Eq.sym x≈y))) (¬-mono (reflexive x≈y))

  -- NOTE: `*-aut` is the LEFT *-autonomous property.
  *-autʳ : ∀ {x y z} → (x ⊗ y) ≲ ¬ z → y ≲ ¬ (z ⊗ x)
  *-autʳ {x} {y} {z} xy≲¬z =
    begin
      y
    ≤⟨ *-aut (≤-respˡ-≈ (⊗-comm x y) xy≲¬z) ⟩
      ¬ (x ⊗ z)
    ≈⟨ ¬-cong (⊗-comm _ _) ⟩
      ¬ (z ⊗ x)
    ∎
    where open PosetReasoning poset

  -- NOTE: `*-aut⁻¹` is the LEFT inverse *-autonomous property.
  *-autʳ⁻¹ : ∀ {x y z} → y ≲ ¬ (z ⊗ x) → (x ⊗ y) ≲ ¬ z
  *-autʳ⁻¹ {x} {y} {z} y≲¬zx =
    begin
      x ⊗ y
    ≈⟨ ⊗-comm _ _ ⟩
      y ⊗ x
    ≤⟨ *-aut⁻¹ (≤-respʳ-≈ (¬-cong (⊗-comm _ _)) y≲¬zx) ⟩
      ¬ z
    ∎
    where open PosetReasoning poset

  ⊥ : A
  ⊥ = ¬ ε

  _⅋_ : A → A → A
  x ⅋ y = ¬ (¬ x ⊗ ¬ y)

  ⅋-comm : ∀ x y → (x ⅋ y) ≈ (y ⅋ x)
  ⅋-comm x y = ¬-cong (⊗-comm _ _)

  ⅋-mono : Monotonic₂ _≲_ _≲_ _≲_ _⅋_
  ⅋-mono x≲y u≲v = ¬-mono (⊗-mono (¬-mono x≲y) (¬-mono u≲v))

  ⅋-assoc : Associative _⅋_
  ⅋-assoc x y z =
    begin
      (x ⅋ y) ⅋ z
    ≡⟨⟩
      ¬ (¬ (x ⅋ y) ⊗ ¬ z)
    ≈⟨ ¬-cong (⊗-cong (¬-involutive _) Eq.refl) ⟩
      ¬ ((¬ x ⊗ ¬ y) ⊗ ¬ z)
    ≈⟨ ¬-cong (⊗-assoc _ _ _) ⟩
      ¬ (¬ x ⊗ (¬ y ⊗ ¬ z))
    ≈⟨ ¬-cong (⊗-cong Eq.refl (¬-involutive _)) ⟨
      ¬ (¬ x ⊗ ¬ (y ⅋ z))
    ≡⟨⟩
      x ⅋ (y ⅋ z)
    ∎
    where open SetoidReasoning setoid

  ⅋-identityˡ : LeftIdentity ⊥ _⅋_
  ⅋-identityˡ x =
      begin
        ⊥ ⅋ x
      ≡⟨⟩
        ¬ (¬ (¬ ε) ⊗ ¬ x)
      ≈⟨ ¬-cong (⊗-cong (¬-involutive _) Eq.refl) ⟩
        ¬ (ε ⊗ ¬ x)
      ≈⟨ ¬-cong (⊗-identityˡ _) ⟩
        ¬ (¬ x)
      ≈⟨ ¬-involutive _ ⟩
        x
      ∎
      where open SetoidReasoning setoid

  ⅋-identityʳ : RightIdentity ⊥ _⅋_
  ⅋-identityʳ x =
      begin
        x ⅋ ⊥
      ≡⟨⟩
        ¬ (¬ x ⊗ ¬ (¬ ε))
      ≈⟨ ¬-cong (⊗-cong Eq.refl (¬-involutive _)) ⟩
        ¬ (¬ x ⊗ ε)
      ≈⟨ ¬-cong (⊗-identityʳ _) ⟩
        ¬ (¬ x)
      ≈⟨ ¬-involutive _ ⟩
        x
      ∎
      where open SetoidReasoning setoid

  ⅋-isCommutativePomonoid : IsCommutativePomonoid _⅋_ ⊥
  ⅋-isCommutativePomonoid = record
    { isPomonoid = record
      { isPosemigroup = record
        { isPomagma = record
          { isPartialOrder = isPartialOrder
          ; mono = ⅋-mono
          }
        ; assoc = ⅋-assoc
        }
      ; identity = ⅋-identityˡ , ⅋-identityʳ
      }
    ; comm = ⅋-comm
    }

  open IsCommutativePomonoid ⅋-isCommutativePomonoid public
    using
      (
      )
    renaming
      ( monoˡ     to ⅋-monoˡ
      ; monoʳ     to ⅋-monoʳ
      ; ∙-cong    to ⅋-cong
      ; ∙-congˡ   to ⅋-congˡ
      ; ∙-congʳ   to ⅋-congʳ
      ; identity  to ⅋-identity
      )

  _⊸_ : A → A → A
  x ⊸ y = ¬ x ⅋ y

  residualʳ-to : ∀ {x y z} → (x ⊗ y) ≲ z → y ≲ (x ⊸ z)
  residualʳ-to {x} {y} {z} xy≲z = *-aut $
    begin
      y ⊗ ¬ (¬ x)
    ≈⟨ ⊗-congˡ (¬-involutive _) ⟩
      y ⊗ x
    ≈⟨ ⊗-comm _ _ ⟩
      x ⊗ y
    ≤⟨ xy≲z ⟩
      z
    ≈⟨ ¬-involutive _ ⟨
      ¬ (¬ z)
    ∎
    where open PosetReasoning poset

  residualʳ-from : ∀ {x y z} → y ≲ (x ⊸ z) → (x ⊗ y) ≲ z
  residualʳ-from {x} {y} {z} y≲x⊸z =
    begin
      x ⊗ y
    ≈⟨ ⊗-comm _ _ ⟩
      y ⊗ x
    ≤⟨ *-aut⁻¹ (≤-respʳ-≈ (¬-cong (⊗-congʳ (¬-involutive _))) y≲x⊸z) ⟩
      ¬ (¬ z)
    ≈⟨ ¬-involutive _ ⟩
      z
    ∎
    where open PosetReasoning poset

  residualʳ : RightResidual _⊗_ _⊸_
  residualʳ ._↔_.to = residualʳ-to
  residualʳ ._↔_.from = residualʳ-from

  ⊗-⊸-isResiduatedCommutativePomonoid : IsResiduatedCommutativePomonoid _⊗_ _⊸_ ε
  ⊗-⊸-isResiduatedCommutativePomonoid = record
    { isCommutativePomonoid = isCommutativePomonoid
    ; residuated            = comm∧residual⇒residuated isPreorder ⊗-comm residualʳ
    }

  open IsResiduatedCommutativePomonoid ⊗-⊸-isResiduatedCommutativePomonoid public
    using
      ( residualˡ
      ; evalˡ
      ; evalʳ
      ; mono-antiˡ
      ; anti-monoʳ
      )
    renaming
      ( residuated to ⊗-⊸-residuated
      )

  -- FIXME: This is contraction.
  ev : ∀ {x} → (x ⊗ ¬ x) ≲ ⊥
  ev {x} = *-aut⁻¹ $
    begin
      x
    ≈⟨ ¬-involutive x ⟨
      ¬ (¬ x)
    ≈⟨ ¬-cong (⊗-identityʳ (¬ x)) ⟨
      ¬ (¬ x ⊗ ε)
    ∎
    where open PosetReasoning poset

  -- FIXME: This is expansion.
  coev : ∀ {x} → ε ≲ (x ⅋ ¬ x)
  coev {x} =
    begin
      ε
    ≤⟨ residualʳ-to (reflexive (⊗-identityʳ x)) ⟩
      ¬ (¬ (¬ x) ⊗ ¬ x)
    ≈⟨ ⅋-comm _ _ ⟩
      ¬ (¬ x ⊗ ¬ (¬ x))
    ≡⟨⟩
      x ⅋ ¬ x
    ∎
    where open PosetReasoning poset

  linear-distribˡ : ∀ {x y z} → (x ⊗ (z ⅋ y)) ≲ (z ⅋ (x ⊗ y))
  linear-distribˡ {x} {y} {z} = *-aut $
    begin
      (x ⊗ (z ⅋ y)) ⊗ ¬ z
    ≈⟨ ⊗-assoc _ _ _ ⟩
      (x ⊗ ((z ⅋ y) ⊗ ¬ z))
    ≈⟨ ⊗-congˡ (⊗-congʳ (⅋-congʳ (¬-involutive _))) ⟨
      (x ⊗ ((¬ (¬ z) ⅋ y) ⊗ ¬ z))
    ≤⟨ ⊗-monoʳ evalˡ ⟩
      (x ⊗ y)
    ≈⟨ ¬-involutive _ ⟨
      ¬ (¬ (x ⊗ y))
    ∎
    where open PosetReasoning poset

  linear-distribʳ : ∀ {x y z} → ((z ⅋ y) ⊗ x) ≲ ((y ⊗ x) ⅋ z)
  linear-distribʳ {x} {y} {z} = *-autʳ $
    begin
      ¬ z ⊗ ((z ⅋ y) ⊗ x)
    ≈⟨ ⊗-assoc _ _ _ ⟨
      (¬ z ⊗ (z ⅋ y)) ⊗ x
    ≈⟨ ⊗-congʳ (⊗-congˡ (⅋-congʳ (¬-involutive _))) ⟨
      (¬ z ⊗ (¬ (¬ z) ⅋ y)) ⊗ x
    ≤⟨ ⊗-monoˡ (evalʳ {¬ z} {y}) ⟩
      (y ⊗ x)
    ≈⟨ ¬-involutive _ ⟨
      ¬ (¬ (y ⊗ x))
    ∎
    where open PosetReasoning poset

  linear-distrib : ∀ {x y z} → (x ⊗ (y ⅋ z)) ≲ ((x ⊗ y) ⅋ z)
  linear-distrib {x} {y} {z} =
    begin
      (x ⊗ (y ⅋ z))
    ≈⟨ ⊗-congˡ (⅋-comm _ _) ⟩
      (x ⊗ (z ⅋ y))
    ≤⟨ linear-distribˡ ⟩
      (z ⅋ (x ⊗ y))
    ≈⟨ ⅋-comm _ _ ⟩
      ((x ⊗ y) ⅋ z)
    ∎
    where open PosetReasoning poset
