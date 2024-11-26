{-# OPTIONS --postfix-projections --safe --without-K --cubical-compatible #-}

open import Level
open import Algebra
open import Algebra.Ordered
open import Algebra.Ordered.Consequences using (comm∧residual⇒residuated; supremum∧residuated⇒distrib)
open import Function using (flip)
open import Function.EquiInhabited using (_↔_)
open import Data.Empty as Empty using ()
open import Data.Product using (_×_; _,_; proj₁; proj₂; <_,_>; -,_; ∃-syntax; Σ-syntax; swap)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit as Unit using ()
open import Relation.Binary using (Poset; Reflexive; Transitive; IsPartialOrder; IsPreorder; Monotonic₁; Monotonic₂; Minimum)
open import Relation.Binary.Construct.Core.Symmetric as SymCore using (SymCore)
open import Relation.Binary.Lattice
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
import Relation.Binary.Construct.Flip.EqAndOrd as Flip
open import Relation.Unary using (Pred; _⊆_)

module Algebra.Ordered.Construction.LowerSet {c ℓ₁ ℓ₂} (poset : Poset c ℓ₁ ℓ₂) where

private
  module C = Poset poset

open C
  using
    ( Carrier
    )
  renaming
    ( _≈_     to _≈ᶜ_
    ; _≤_     to _≤ᶜ_
    )

private
  variable
    w x y z : Carrier

record LowerSet : Set (suc (c ⊔ ℓ₂)) where
  no-eta-equality
  field
    ICarrier : Pred Carrier (c ⊔ ℓ₂)
    ≤-closed : x ≤ᶜ y → ICarrier y → ICarrier x
open LowerSet public

private
  variable
    F F₁ F₂ : LowerSet
    G G₁ G₂ : LowerSet
    H H₁ H₂ : LowerSet

infix 4 _≤_

record _≤_ (F G : LowerSet) : Set (c ⊔ ℓ₂) where
  no-eta-equality
  constructor mk-≤
  field
    *≤* : F .ICarrier ⊆ G .ICarrier
open _≤_ public

infix 4 _≥_

_≥_ : LowerSet → LowerSet → Set (c ⊔ ℓ₂)
_≥_ = flip _≤_

infix 4 _≈_

_≈_ : LowerSet → LowerSet → Set (c ⊔ ℓ₂)
_≈_ = SymCore _≤_

≤-refl : Reflexive _≤_
≤-refl .*≤* Fx = Fx

≤-trans : Transitive _≤_
≤-trans F≤G G≤H .*≤* Fx = G≤H .*≤* (F≤G .*≤* Fx)

≤-isPartialOrder : IsPartialOrder _≈_ _≤_
≤-isPartialOrder = SymCore.isPreorder⇒isPartialOrder _≤_ ≡-≤-isPreorder
  where
    ≡-≤-isPreorder : IsPreorder _≡_ _≤_
    ≡-≤-isPreorder = record
      { isEquivalence = PropEq.isEquivalence
      ; reflexive = λ { PropEq.refl → ≤-refl }
      ; trans = ≤-trans
      }

open IsPartialOrder ≤-isPartialOrder public
  using
    ( module Eq
    )
  renaming
    ( ≤-respˡ-≈  to ≤-respˡ-≈
    ; reflexive  to ≤-reflexive
    ; isPreorder to ≤-isPreorder
    )

≤-poset : Poset _ _ _
≤-poset = record
  { isPartialOrder = ≤-isPartialOrder
  }

module Reasoning where
  open import Relation.Binary.Reasoning.PartialOrder ≤-poset public
    using
      ( begin_
      ; _∎
      )
    renaming
      ( ≤-go to ≤ˢ-go
      ; ≈-go to ≈ˢ-go
      )
  step-≤ˢ = ≤ˢ-go
  syntax step-≤ˢ x yRz x≤y = x ≤ˢ⟨ x≤y ⟩ yRz
  step-≈ˢ = ≈ˢ-go
  syntax step-≈ˢ x yRz x≈y = x ≈ˢ⟨ x≈y ⟩ yRz

≥-isPartialOrder : IsPartialOrder _≈_ _≥_
≥-isPartialOrder = Flip.isPartialOrder ≤-isPartialOrder

η : Carrier → LowerSet
η x .ICarrier y = Lift c (y ≤ᶜ x)
η x .≤-closed z≤y y≤x = lift (C.trans z≤y (y≤x .lower))

η-mono : x ≤ᶜ y → η x ≤ η y
η-mono x≤y .*≤* (lift z≤x) = lift (C.trans z≤x x≤y)

------------------------------------------------------------------------------
-- Construct a meet semilattice for presheaves

_∧_ : LowerSet → LowerSet → LowerSet
(F ∧ G) .ICarrier x = F .ICarrier x × G .ICarrier x
(F ∧ G) .≤-closed x≤y (Fy , Gy) = (F .≤-closed x≤y Fy , G .≤-closed x≤y Gy)

x∧y≤x : (F ∧ G) ≤ F
x∧y≤x .*≤* = proj₁

x∧y≤y : (F ∧ G) ≤ G
x∧y≤y .*≤* = proj₂

∧-greatest : F ≤ G → F ≤ H → F ≤ (G ∧ H)
∧-greatest H≤F H≤G .*≤* = < H≤F .*≤* , H≤G .*≤* >

∧-infimum : Infimum _≤_ _∧_
∧-infimum F G = (x∧y≤x , x∧y≤y , λ H → ∧-greatest)

∧-isMeetSemilattice : IsMeetSemilattice _≈_ _≤_ _∧_
∧-isMeetSemilattice = record
  { isPartialOrder = ≤-isPartialOrder
  ; infimum        = ∧-infimum
  }

∧-meetSemilattice : MeetSemilattice _ _ _
∧-meetSemilattice = record
  { isMeetSemilattice = ∧-isMeetSemilattice
  }

open import Relation.Binary.Lattice.Properties.MeetSemilattice ∧-meetSemilattice
  using
    (
    )
  renaming
    ( ∧-monotonic to ∧-monotonic
    ; ∧-assoc     to ∧-assoc
    ; ∧-comm      to ∧-comm
    )

∧-⊤-isPosemigroup : IsPosemigroup _≈_ _≤_ _∧_
∧-⊤-isPosemigroup = record
  { isPomagma = record
    { isPartialOrder = ≤-isPartialOrder
    ; mono = ∧-monotonic
    }
  ; assoc = ∧-assoc
  }

⊤ : LowerSet
⊤ .ICarrier x = Lift (c ⊔ ℓ₂) Unit.⊤
⊤ .≤-closed x Fx = Fx

∧-⊤-isBoundedMeetSemilattice : IsBoundedMeetSemilattice _≈_ _≤_ _∧_ ⊤
∧-⊤-isBoundedMeetSemilattice = record
  { isMeetSemilattice = ∧-isMeetSemilattice
  ; maximum           = λ F → mk-≤ (λ Fx → lift Unit.tt)
  }

∧-⊤-boundedMeetSemilattice : BoundedMeetSemilattice _ _ _
∧-⊤-boundedMeetSemilattice = record
  { isBoundedMeetSemilattice = ∧-⊤-isBoundedMeetSemilattice
  }

open import Relation.Binary.Lattice.Properties.BoundedMeetSemilattice ∧-⊤-boundedMeetSemilattice
  using
    (
    )
  renaming
    ( identity to ∧-⊤-identity
    )

∧-⊤-isCommutativePomonoid : IsCommutativePomonoid _≈_ _≤_ _∧_ ⊤
∧-⊤-isCommutativePomonoid = record
  { isPomonoid = record
    { isPosemigroup = ∧-⊤-isPosemigroup
    ; identity = ∧-⊤-identity
    }
  ; comm = ∧-comm
  }

------------------------------------------------------------------------------
-- Construct a join semilattice for presheaves

_∨_ : LowerSet → LowerSet → LowerSet
(F ∨ G) .ICarrier x = F .ICarrier x ⊎ G .ICarrier x
(F ∨ G) .≤-closed x≤y (inj₁ Fy) = inj₁ (F .≤-closed x≤y Fy)
(F ∨ G) .≤-closed x≤y (inj₂ Gy) = inj₂ (G .≤-closed x≤y Gy)

x≤x∨y : F ≤ (F ∨ G)
x≤x∨y .*≤* = inj₁

y≤x∨y : G ≤ (F ∨ G)
y≤x∨y .*≤* = inj₂

∨-least : F ≤ H → G ≤ H → (F ∨ G) ≤ H
∨-least H≥F H≥G .*≤* = [ H≥F .*≤* , H≥G .*≤* ]

∨-supremum : Supremum _≤_ _∨_
∨-supremum F G = (x≤x∨y , y≤x∨y , λ H → ∨-least)

∨-isJoinSemilattice : IsJoinSemilattice _≈_ _≤_ _∨_
∨-isJoinSemilattice = record
  { isPartialOrder = ≤-isPartialOrder
  ; supremum       = ∨-supremum
  }

⊥ : LowerSet
⊥ .ICarrier x = Lift (c ⊔ ℓ₂) Empty.⊥
⊥ .≤-closed _ ()

⊥-minimum : Minimum _≤_ ⊥
⊥-minimum F = mk-≤ λ ()

∨-⊥-isBoundedJoinSemilattice : IsBoundedJoinSemilattice _≈_ _≤_ _∨_ ⊥
∨-⊥-isBoundedJoinSemilattice = record
  { isJoinSemilattice = ∨-isJoinSemilattice
  ; minimum = ⊥-minimum
  }

------------------------------------------------------------------------------
-- Construct a residuated pomonoid for presheaves

_⇒_ : LowerSet → LowerSet → LowerSet
(F ⇒ G) .ICarrier x = ∀ {y} → y ≤ᶜ x → F .ICarrier y → G .ICarrier y
(F ⇒ G) .≤-closed x≤y f z≤x Fz = f (C.trans z≤x x≤y) Fz

⇒-residualʳ-to : (F ∧ G) ≤ H → G ≤ (F ⇒ H)
⇒-residualʳ-to {F} {G} {H} F∧G≤H .*≤* Gx y≤x Fy = F∧G≤H .*≤* (Fy , G .≤-closed y≤x Gx)

⇒-residualʳ-from : G ≤ (F ⇒ H) → (F ∧ G) ≤ H
⇒-residualʳ-from G≤F⇒H .*≤* (Fx , Gx) = G≤F⇒H .*≤* Gx C.refl Fx

⇒-residualʳ : RightResidual _≤_ _∧_ _⇒_
⇒-residualʳ ._↔_.to        = ⇒-residualʳ-to
⇒-residualʳ ._↔_.from      = ⇒-residualʳ-from

⇒-∧-isResiduatedCommutativePomonoid : IsResiduatedCommutativePomonoid _≈_ _≤_ _∧_ _⇒_ ⊤
⇒-∧-isResiduatedCommutativePomonoid = record
  { isCommutativePomonoid = ∧-⊤-isCommutativePomonoid
  ; residuated            = comm∧residual⇒residuated ≤-isPreorder ∧-comm ⇒-residualʳ
  }

------------------------------------------------------------------------------
-- Lift monoids to presheaves

module Day
    {_∙ᶜ_}
    {εᶜ}
    (isPomonoid : IsPomonoid _≈ᶜ_ _≤ᶜ_ _∙ᶜ_ εᶜ)
  where

  private
    module Mon = IsPomonoid isPomonoid

  _∙_ : LowerSet → LowerSet → LowerSet
  (F ∙ G) .ICarrier x =
    ∃[ y ] ∃[ z ] (x ≤ᶜ (y ∙ᶜ z) × F .ICarrier y × G .ICarrier z)
  (F ∙ G) .≤-closed x≤w (y , z , w≤yz , ϕ₁ , ϕ₂) =
    (-, -, C.trans x≤w w≤yz , ϕ₁ , ϕ₂)

  ∙-mono : Monotonic₂ _≤_ _≤_ _≤_ _∙_
  ∙-mono F₁≤F₂ G₁≤G₂ .*≤* (y , z , x≤yz , F₁y , G₁z) =
    (-, -, x≤yz , F₁≤F₂ .*≤* F₁y , G₁≤G₂ .*≤* G₁z)

  η-preserve-∙ : η (x ∙ᶜ y) ≤ η x ∙ η y
  η-preserve-∙ {x} {y} .*≤* {z} (lift z≤xy) = x , y , z≤xy , lift C.refl , lift C.refl

  η-preserve-∙⁻¹ : η x ∙ η y ≤ η (x ∙ᶜ y)
  η-preserve-∙⁻¹ {x} {y} .*≤* {z} (z₁ , z₂ , z≤z₁z₂ , lift z₁≤x , lift z₂≤y) =
    lift (C.trans z≤z₁z₂ (Mon.mono z₁≤x z₂≤y))

  ε : LowerSet
  ε = η εᶜ

  ∙-identityˡ : LeftIdentity _≈_ ε _∙_
  ∙-identityˡ F .proj₁ .*≤* (y , z , x≤yz , lift y≤ε , Fz) =
    F .≤-closed (C.trans x≤yz (C.trans (Mon.mono y≤ε C.refl) (C.≤-respʳ-≈ (Mon.identityˡ z) C.refl) )) Fz
  ∙-identityˡ F .proj₂ .*≤* Fx =
    (-, -, C.≤-respˡ-≈ (Mon.identityˡ _) C.refl , lift C.refl , Fx)

  ∙-identityʳ : RightIdentity _≈_ ε _∙_
  ∙-identityʳ F .proj₁ .*≤* (y , z , x≤yz , Fy , lift z≤ε) =
    F .≤-closed (C.trans x≤yz (C.trans (Mon.mono C.refl z≤ε) (C.≤-respʳ-≈ (Mon.identityʳ y) C.refl) )) Fy
  ∙-identityʳ F .proj₂ .*≤* Fx =
    (-, -, C.≤-respˡ-≈ (Mon.identityʳ _) C.refl , Fx , lift C.refl)

  ∙-identity : Identity _≈_ ε _∙_
  ∙-identity = (∙-identityˡ , ∙-identityʳ)

  ∙-assoc : Associative _≈_ _∙_
  ∙-assoc F G H .proj₁ .*≤* (y , z , x≤yz , (u , v , y≤uv , Fu , Gv) , Hz) =
    let x≤u∙v∙z = C.trans x≤yz (C.trans (Mon.mono y≤uv C.refl) (C.≤-respʳ-≈ (Mon.assoc u v z)  C.refl)) in
      (-, -, x≤u∙v∙z , Fu , (-, -, C.refl , Gv , Hz))

  ∙-assoc F G H .proj₂ .*≤* (y , z , x≤yz , Fy , (u , v , z≤uv , Gu , Hv)) =
    let x≤y∙u∙v = C.trans x≤yz (C.trans (Mon.mono C.refl z≤uv) (C.≤-respˡ-≈ (Mon.assoc y u v) C.refl)) in
      (-, -, x≤y∙u∙v , (-, -, C.refl , Fy , Gu) , Hv)

  ∙-isPomonoid : IsPomonoid _≈_ _≤_ _∙_ ε
  ∙-isPomonoid = record
    { isPosemigroup = record
      { isPomagma = record
        { isPartialOrder = ≤-isPartialOrder
        ; mono = ∙-mono
        }
      ; assoc = ∙-assoc
      }
    ; identity = ∙-identity
    }

  open IsPomonoid ∙-isPomonoid public
    using
      (
      )
    renaming
      ( monoˡ   to ∙-monoˡ
      ; monoʳ   to ∙-monoʳ
      ; ∙-cong  to ∙-cong
      ; ∙-congˡ to ∙-congˡ
      ; ∙-congʳ to ∙-congʳ
      )

module DayCommutative
    {_∙ᶜ_}
    {εᶜ}
    (isCommutativePomonoid : IsCommutativePomonoid _≈ᶜ_ _≤ᶜ_ _∙ᶜ_ εᶜ)
  where

  private
    module Mon = IsCommutativePomonoid isCommutativePomonoid
  open Day Mon.isPomonoid public

  ∙-comm : Commutative _≈_ _∙_
  ∙-comm F G .proj₁ .*≤* (y , z , x≤yz , Fy , Gz) =
    (-, -, C.trans x≤yz (C.≤-respˡ-≈ (Mon.comm z y) C.refl) , Gz , Fy)
  ∙-comm F G .proj₂ .*≤* (y , z , x≤yz , Gy , Fz) =
    (-, -, C.trans x≤yz (C.≤-respˡ-≈ (Mon.comm z y) C.refl) , Fz , Gy)

  ∙-isCommutativePomonoid : IsCommutativePomonoid _≈_ _≤_ _∙_ ε
  ∙-isCommutativePomonoid = record
    { isPomonoid = ∙-isPomonoid
    ; comm       = ∙-comm
    }

  _⊸_ : LowerSet → LowerSet → LowerSet
  (F ⊸ G) .ICarrier x        = ∀ {y} → F .ICarrier y → G .ICarrier (x ∙ᶜ y)
  (F ⊸ G) .≤-closed x≤z f Fy = G .≤-closed (Mon.mono x≤z C.refl) (f Fy)

  ⊸-residual-to : (F ∙ G) ≤ H → G ≤ (F ⊸ H)
  ⊸-residual-to F∙G≤H .*≤* Gx Fy =
    F∙G≤H .*≤* (-, -, C.≤-respˡ-≈ (Mon.comm _ _) C.refl , Fy , Gx)

  ⊸-residual-from : G ≤ (F ⊸ H) → (F ∙ G) ≤ H
  ⊸-residual-from {G} {F} {H} G≤F⊸H .*≤* (_ , _ , x≤y∙z , Fy , Gz) =
    H .≤-closed (C.trans x≤y∙z (C.≤-respˡ-≈ (Mon.comm _ _) C.refl)) (G≤F⊸H .*≤* Gz Fy)

  ⊸-residual : RightResidual _≤_ _∙_ _⊸_
  ⊸-residual ._↔_.to        = ⊸-residual-to
  ⊸-residual ._↔_.from      = ⊸-residual-from

  ⊸-∙-isResiduatedCommutativePomonoid : IsResiduatedCommutativePomonoid _≈_ _≤_ _∙_ _⊸_ ε
  ⊸-∙-isResiduatedCommutativePomonoid = record
    { isCommutativePomonoid = ∙-isCommutativePomonoid
    ; residuated = comm∧residual⇒residuated ≤-isPreorder ∙-comm ⊸-residual
    }

  ∙-∨-distrib : _DistributesOver_ _≤_ _∙_ _∨_
  ∙-∨-distrib = supremum∧residuated⇒distrib ≤-isPreorder ∨-supremum
    (IsResiduatedCommutativePomonoid.residuated ⊸-∙-isResiduatedCommutativePomonoid)

  -- Exponentials
  module FreeExponential where
    ！ : LowerSet → LowerSet
    ！ F .ICarrier x =
        Σ[ z ∈ Carrier ] (x ≤ᶜ z) × (z ≤ᶜ εᶜ) × (z ≤ᶜ (z ∙ᶜ z)) × F .ICarrier z
    ！ F .≤-closed x≤y (z , y≤z , z≤ε , z≤zz , Fz) = z , C.trans x≤y y≤z , z≤ε , z≤zz , Fz

    ！-mono : Monotonic₁ _≤_ _≤_ ！
    ！-mono F≤G .*≤* (z , x≤z , z≤ε , z≤zz , Fz) =
      z , x≤z , z≤ε , z≤zz , F≤G .*≤* Fz

    ！-monoidal : (！ F ∙ ！ G) ≤ ！ (F ∙ G)
    ！-monoidal .*≤* {x} (y , z , x≤yz , (y' , y≤y' , y'≤ε , y'≤y'y' , Fy') ,
                                         (z' , z≤z' , z'≤ε , z'≤z'z' , Gz')) =
       y' ∙ᶜ z' , C.trans x≤yz (Mon.mono y≤y' z≤z') ,
       (C.trans (Mon.mono y'≤ε z'≤ε) (C.reflexive (Mon.identityˡ _))) ,
       C.trans (Mon.mono y'≤y'y' z'≤z'z')
       (C.trans (C.reflexive (Mon.assoc _ _ _))
       (C.trans (Mon.mono C.refl (C.reflexive (C.Eq.sym (Mon.assoc _ _ _))))
       (C.trans (Mon.mono C.refl (Mon.mono (C.reflexive (Mon.comm _ _)) C.refl))
       (C.trans (Mon.mono C.refl (C.reflexive (Mon.assoc _ _ _)))
       (C.reflexive (C.Eq.sym (Mon.assoc _ _ _))))))) ,
       (y' , z' , C.refl , Fy' , Gz')

    ！-discard : ！ F ≤ ε
    ！-discard .*≤* {x} (z , x≤z , z≤ε , z≤zz , Fz) = lift (C.trans x≤z z≤ε)

    ！-duplicate : ！ F ≤ (！ F ∙ ！ F)
    ！-duplicate .*≤* {x} (z , x≤z , z≤ε , z≤zz , Fz) =
      z , z , C.trans x≤z z≤zz ,
      (z , C.refl , z≤ε , z≤zz , Fz) ,
      (z , C.refl , z≤ε , z≤zz , Fz)

    ！-derelict : ！ F ≤ F
    ！-derelict {F} .*≤* {x} (z , x≤z , z≤ε , x≤zz , Fz) = F .≤-closed x≤z Fz

    ！-dig : ！ F ≤ ！ (！ F)
    ！-dig .*≤* {x} (z , x≤z , z≤ε , z≤zz , Fz) =
      z , x≤z , z≤ε , z≤zz , (z , C.refl , z≤ε , z≤zz , Fz)

    η-preserve-！ : ∀ {x} → x ≤ᶜ εᶜ → x ≤ᶜ (x ∙ᶜ x) → η x ≤ ！ (η x)
    η-preserve-！ {x} x≤ε x≤xx .*≤* {y} (lift y≤x) = x , y≤x , x≤ε , x≤xx , lift C.refl

  module Exp (！ᶜ : Op₁ Carrier)
      (！ᶜ-discard   : ∀ {x} → ！ᶜ x ≤ᶜ εᶜ)
      (！ᶜ-duplicate : ∀ {x} → ！ᶜ x ≤ᶜ (！ᶜ x ∙ᶜ ！ᶜ x))
      (！ᶜ-derelict  : ∀ {x} → ！ᶜ x ≤ᶜ x)
      (！ᶜ-dig       : ∀ {x} → ！ᶜ x ≤ᶜ ！ᶜ (！ᶜ x))
      where

    -- x ≤ !z₁ ∙ ... ∙ !zₙ × F(!z₁ ∙ ... ∙ !zₙ)
    data !-context : Carrier → Set (c ⊔ ℓ₂) where
      nil  : !-context εᶜ
      pair : ∀ {y z} → !-context y → !-context z → !-context (y ∙ᶜ z)
      leaf : ∀ {z} → !-context (！ᶜ z)

    ！ : LowerSet → LowerSet
    ！ F .ICarrier x = Σ[ z ∈ Carrier ] (x ≤ᶜ z × !-context z × F .ICarrier z)
    ！ F .≤-closed x≤y (z , y≤z , !z , Fz) = z , C.trans x≤y y≤z , !z , Fz

    ！-monoidal-unit : ε ≤ ！ ε
    ！-monoidal-unit .*≤* (lift x≤ε) = εᶜ , x≤ε , nil , (lift C.refl)

    ！-monoidal : (！ F ∙ ！ G) ≤ ！ (F ∙ G)
    ！-monoidal .*≤* {x} (y , z , x≤xy , (y′ , y≤y′ , !y′ , Fy′) , (z′ , z≤z′ , !z′ , Gz′)) =
      (y′ ∙ᶜ z′) , C.trans x≤xy (Mon.mono y≤y′ z≤z′) ,
      pair !y′ !z′ ,
      y′ , z′ , C.refl , Fy′ , Gz′

    ！-mono : Monotonic₁ _≤_ _≤_ ！
    ！-mono F≤G .*≤* (z , x≤z , !z , Fz) = z , x≤z , !z , F≤G .*≤* Fz

    ！-discard : ！ F ≤ ε
    ！-discard .*≤* {x} (z , x≤z , !z , Fz) = lift (C.trans x≤z (discard !z))
       where discard : ∀ {z} → !-context z → z ≤ᶜ εᶜ
             discard nil = C.refl
             discard (pair c d) = C.trans (Mon.mono (discard c) (discard d)) (C.reflexive (Mon.identityʳ _))
             discard leaf = ！ᶜ-discard

    ！-duplicate : ！ F ≤ (！ F ∙ ！ F)
    ！-duplicate .*≤* {x} (z , x≤z , !z , Fz) =
      z , z , C.trans x≤z (duplicate !z) , (z , C.refl , !z , Fz) , (z , C.refl , !z , Fz)
      where duplicate : ∀ {z} → !-context z → z ≤ᶜ (z ∙ᶜ z)
            duplicate nil = C.reflexive (C.Eq.sym (Mon.identityʳ _))
            duplicate (pair c d) =
              C.trans (Mon.mono (duplicate c) (duplicate d))
              (C.trans (C.reflexive (Mon.assoc _ _ _))
              (C.trans (Mon.mono C.refl (C.reflexive (C.Eq.sym (Mon.assoc _ _ _))))
              (C.trans (Mon.mono C.refl (Mon.mono (C.reflexive (Mon.comm _ _)) C.refl))
              (C.trans (Mon.mono C.refl (C.reflexive (Mon.assoc _ _ _)))
              (C.reflexive (C.Eq.sym (Mon.assoc _ _ _)))))))
            duplicate leaf = ！ᶜ-duplicate

    ！-derelict : ！ F ≤ F
    ！-derelict {F} .*≤* {x} (z , x≤z , !z , Fz) = F .≤-closed x≤z Fz

    ！-dig : ！ F ≤ ！ (！ F)
    ！-dig .*≤* {x} (z , x≤z , !z , Fz) = z , x≤z , !z , (z , C.refl , !z , Fz)

    η-preserve-！ : ∀ {x} → η (！ᶜ x) ≤ ！ (η x)
    η-preserve-！ {x} .*≤* {z} (lift z≤!x) = ！ᶜ x , z≤!x , leaf , lift ！ᶜ-derelict

    -- If ！ᶜ is a monoidal monotone operator, then η preserves it strongly.
    module _
        (！ᶜ-monoidal-unit : εᶜ ≤ᶜ ！ᶜ εᶜ)
        (！ᶜ-monoidal      : ∀ {x y} → (！ᶜ x ∙ᶜ ！ᶜ y) ≤ᶜ ！ᶜ (x ∙ᶜ y))
        (！ᶜ-mono          : ∀ {x y} → (x ≤ᶜ y) → ！ᶜ x ≤ᶜ ！ᶜ y)
        where

      !-context-lemma : ∀ {a} → !-context a → a ≤ᶜ ！ᶜ a
      !-context-lemma nil = ！ᶜ-monoidal-unit
      !-context-lemma (pair !a !b) =
        C.trans (Mon.mono (!-context-lemma !a) (!-context-lemma !b)) ！ᶜ-monoidal
      !-context-lemma leaf = ！ᶜ-dig

      η-preserve-！⁻¹ : ∀ {x} → ！ (η x) ≤ η (！ᶜ x)
      η-preserve-！⁻¹ {x} .*≤* {z} (z' , z≤z' , !z' , lift z'≤x) =
        lift (C.trans z≤z' (C.trans (!-context-lemma !z') (！ᶜ-mono z'≤x)))

  module Dagger0 where
    † : LowerSet → LowerSet
    † F .ICarrier x = Σ[ z ∈ Carrier ] (x ≤ᶜ z × z ≤ᶜ εᶜ × F .ICarrier z)
    † F .≤-closed x≤y (z , y≤z , z≤ε , Fz) = z , C.trans x≤y y≤z , z≤ε , Fz

    monoidal-unit : ε ≤ † ε
    monoidal-unit .*≤* (lift x≤ε) = εᶜ , x≤ε , C.refl , (lift C.refl)



    -- This doesn't work!
    -- duplicate : † F ≤ † F ∙ † F
    -- duplicate .*≤* {x} (z , x≤z , z≤ε , Fz) =
    --   z , z , {!!} ,
    --   {!!} ,
    --   {!!}

    η-preserve-† : x ≤ᶜ εᶜ → η x ≤ † (η x)
    η-preserve-† {x} x≤ε .*≤* {z} (lift z≤x) = x , z≤x , x≤ε , lift C.refl

  module Dagger1 where
    -- “† F” means that this is provable free of its current context.

    † : LowerSet → LowerSet
    † F .ICarrier x = x ≤ᶜ εᶜ × F .ICarrier εᶜ
    † F .≤-closed x≤y (y≤ε , Fε) = C.trans x≤y y≤ε , Fε

    †-mono : (F ≤ G) → † F ≤ † G
    †-mono F≤G .*≤* {x} (x≤ε , Fε) = x≤ε , F≤G .*≤* Fε

    monoidal-unit : ε ≤ † ε
    monoidal-unit .*≤* {x} (lift x≤ε) = x≤ε , lift C.refl

    monoidal : † F ∙ † G ≤ † (F ∙ G)
    monoidal .*≤* {x} (y₁ , y₂ , x≤y₁y₂ , (y₁≤ε , Fε) , (y₂≤ε , Gε)) =
       C.trans x≤y₁y₂ (C.trans (Mon.mono y₁≤ε y₂≤ε) {!!}) ,
       εᶜ , εᶜ , {!!} , Fε , Gε

    discard : † F ≤ ε
    discard .*≤* {x} (x≤ε , Fε) = lift x≤ε

    derelict : † F ≤ F
    derelict {F} .*≤* {x} (x≤ε , Fε) = F .≤-closed x≤ε Fε

    dig : † F ≤ † († F)
    dig {F} .*≤* {x} (x≤ε , Fε) = x≤ε , C.refl , Fε

    duplicate : † F ≤ † F ∙ † F
    duplicate .*≤* {x} (x≤ε , Fε) =
      εᶜ , εᶜ , C.trans x≤ε {!!} ,
      (C.refl , Fε) ,
      (C.refl , Fε)

{-
    η-preserve-† : εᶜ ≤ᶜ x → η x ≤ † (η x)
    η-preserve-† x≤ε .*≤* {z} (lift z≤x) = {!!} , {!!}
-}

  module Dagger2 where
    -- “† F” means that this is provable free of its current context.

    † : LowerSet → LowerSet
    † F .ICarrier x = F .ICarrier εᶜ
    † F .≤-closed x≤y Fε = Fε

    †-mono : (F ≤ G) → † F ≤ † G
    †-mono F≤G .*≤* {x} Fε = F≤G .*≤* Fε

    monoidal-unit : ε ≤ † ε
    monoidal-unit .*≤* {x} (lift x≤ε) = lift C.refl

    monoidal : † F ∙ † G ≤ † (F ∙ G)
    monoidal .*≤* {x} (y₁ , y₂ , x≤y₁y₂ , Fε , Gε) =
       εᶜ , εᶜ , {!!} , Fε , Gε

    discard : † F ≤ ε
    discard .*≤* {x} Fε = {!!}

    derelict : † F ≤ F
    derelict {F} .*≤* {x} Fε = {!!}

    dig : † F ≤ † († F)
    dig {F} .*≤* {x} Fε = Fε


module DayDuoidal
    {_∙ᶜ_}
    {_◁ᶜ_}
    {εᶜ}
    {ιᶜ}
    (isDuoidal : IsDuoidal _≈ᶜ_ _≤ᶜ_ _∙ᶜ_ _◁ᶜ_ εᶜ ιᶜ)
  where

  private
    module Duo = IsDuoidal isDuoidal
  open Day Duo.∙-isPomonoid public
  open Day Duo.◁-isPomonoid public
    renaming
      ( _∙_             to _◁_
      ; ε               to ι
      ; ∙-mono          to ◁-mono
      ; ∙-monoˡ         to ◁-monoˡ
      ; ∙-monoʳ         to ◁-monoʳ
      ; ∙-cong          to ◁-cong
      ; ∙-congˡ         to ◁-congˡ
      ; ∙-congʳ         to ◁-congʳ
      ; ∙-assoc         to ◁-assoc
      ; ∙-identity      to ◁-identity
      ; ∙-identityˡ     to ◁-identityˡ
      ; ∙-identityʳ     to ◁-identityʳ
      ; ∙-isPomonoid    to ◁-isPomonoid
      ; η-preserve-∙   to η-preserve-◁
      ; η-preserve-∙⁻¹ to η-preserve-◁⁻¹
      )

  ∙-◁-entropy : Entropy _≤_ _∙_ _◁_
  ∙-◁-entropy F₁ G₁ F₂ G₂ .*≤*
    (y , z , x≤yz ,
      (y₁ , y₂ , y≤y₁y₂ , F₁y₁ , G₁y₂) ,
      (z₁ , z₂ , z≤z₁z₂ , F₂z₁ , G₂z₂)) =
    (-, -, C.trans x≤yz (C.trans (Duo.∙-mono y≤y₁y₂ z≤z₁z₂) (Duo.∙-◁-entropy y₁ y₂ z₁ z₂)) ,
      (-, -, C.refl , F₁y₁ , F₂z₁) ,
      (-, -, C.refl , G₁y₂ , G₂z₂))

  ∙-idem-ι : _SubidempotentOn_ _≤_ _∙_ ι
  ∙-idem-ι .*≤* (y , z , x≤y∙z , ιy , ιz) .lower =
    C.trans x≤y∙z (C.trans (Duo.∙-mono (ιy .lower) (ιz .lower)) Duo.∙-idem-ι)

  ◁-idem-ε : _SuperidempotentOn_ _≤_ _◁_ ε
  ◁-idem-ε .*≤* εx =
    (-, -, C.trans (εx .lower) Duo.◁-idem-ε , lift C.refl , lift C.refl)

  ε≤ι : ε ≤ ι
  ε≤ι .*≤* εx .lower = C.trans (εx .lower) Duo.ε≲ι

  ∙-◁-isDuoidal : IsDuoidal _≈_ _≤_ _∙_ _◁_ ε ι
  ∙-◁-isDuoidal = record
    { ∙-isPomonoid = ∙-isPomonoid
    ; ◁-isPomonoid = ◁-isPomonoid
    ; ∙-◁-entropy  = ∙-◁-entropy
    ; ∙-idem-ι     = ∙-idem-ι
    ; ◁-idem-ε     = ◁-idem-ε
    ; ε≲ι          = ε≤ι
    }
