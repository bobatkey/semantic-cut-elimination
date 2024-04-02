{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level
open import Algebra
open import Algebra.Ordered.Consequences
open import Algebra.Ordered.Definitions
open import Algebra.Ordered.Structures
open import Algebra.Ordered.Structures.Residuated
open import Algebra.Ordered.Structures.Duoidal
open import Function using (flip)
open import Data.Product as Product using (_×_; _,_; -,_; ∃-syntax; Σ-syntax; swap)
open import Data.Sum as Sum using (_⊎_)
open import Data.Unit as Unit using ()
open import Relation.Binary using (Poset; Reflexive; Transitive; IsPartialOrder; IsPreorder; Monotonic₂)
open import Relation.Binary.Construct.Core.Symmetric as SymCore using (SymCore)
open import Relation.Binary.Lattice
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
import Relation.Binary.Construct.Flip.EqAndOrd as Flip
open import Relation.Unary using (Pred; _⊆_)

module Algebra.Ordered.Construction.LowerSet {c ℓ₁ ℓ₂} (poset : Poset c ℓ₁ ℓ₂) where

private
  module ≤ᶜ = Poset poset
  module ≈ᶜ = ≤ᶜ.Eq
  
open ≤ᶜ
  using
    ( Carrier
    )
  renaming
    ( _≈_   to _≈ᶜ_
    ; _≤_   to _≤ᶜ_
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
η x .≤-closed z≤y y≤x = lift (≤ᶜ.trans z≤y (y≤x .lower))

η-mono : x ≤ᶜ y → η x ≤ η y
η-mono x≤y .*≤* (lift z≤x) = lift (≤ᶜ.trans z≤x x≤y)

------------------------------------------------------------------------------
-- Construct a meet semilattice for presheaves

_∧_ : LowerSet → LowerSet → LowerSet
(F ∧ G) .ICarrier x = F .ICarrier x × G .ICarrier x
(F ∧ G) .≤-closed x≤y (Fy , Gy) = (F .≤-closed x≤y Fy , G .≤-closed x≤y Gy)

proj₁ : (F ∧ G) ≤ F
proj₁ .*≤* = Product.proj₁

proj₂ : (F ∧ G) ≤ G
proj₂ .*≤* = Product.proj₂

⟨_,_⟩ : F ≤ G → F ≤ H → F ≤ (G ∧ H)
⟨ H≤F , H≤G ⟩ .*≤* = Product.< H≤F .*≤* , H≤G .*≤* >

∧-isMeetSemilattice : IsMeetSemilattice _≈_ _≤_ _∧_
∧-isMeetSemilattice = record
  { isPartialOrder = ≤-isPartialOrder
  ; infimum        = λ F G → (proj₁ , proj₂ , λ H → ⟨_,_⟩)
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

-- ------------------------------------------------------------------------------
-- -- Construct a join semilattice for presheaves

_∨_ : LowerSet → LowerSet → LowerSet
(F ∨ G) .ICarrier x = F .ICarrier x ⊎ G .ICarrier x
(F ∨ G) .≤-closed x≤y (Sum.inj₁ Fy) = Sum.inj₁ (F .≤-closed x≤y Fy)
(F ∨ G) .≤-closed x≤y (Sum.inj₂ Gy) = Sum.inj₂ (G .≤-closed x≤y Gy)

inj₁ : F ≤ (F ∨ G)
inj₁ .*≤* = Sum.inj₁

inj₂ : G ≤ (F ∨ G)
inj₂ .*≤* = Sum.inj₂

[_,_] : F ≤ H → G ≤ H → (F ∨ G) ≤ H
[ H≥F , H≥G ] .*≤* = Sum.[ H≥F .*≤* , H≥G .*≤* ]

∨-isJoinSemilattice : IsJoinSemilattice _≈_ _≤_ _∨_
∨-isJoinSemilattice = record
  { isPartialOrder = ≤-isPartialOrder
  ; supremum       = λ F G → (inj₁ , inj₂ , λ H → [_,_])
  }

open IsJoinSemilattice ∨-isJoinSemilattice
  using ()
  renaming
    ( supremum to ∨-supremum
    )

-- ------------------------------------------------------------------------------
-- -- Construct a residuated pomonoid for presheaves

_⇒_ : LowerSet → LowerSet → LowerSet
(F ⇒ G) .ICarrier x = ∀ {y} → y ≤ᶜ x → F .ICarrier y → G .ICarrier y
(F ⇒ G) .≤-closed x≤y f z≤x Fz = f (≤ᶜ.trans z≤x x≤y) Fz

⇒-residualʳ-to : (F ∧ G) ≤ H → G ≤ (F ⇒ H)
⇒-residualʳ-to {F} {G} {H} F∧G≤H .*≤* Gx y≤x Fy = F∧G≤H .*≤* (Fy , G .≤-closed y≤x Gx)

⇒-residualʳ-from : G ≤ (F ⇒ H) → (F ∧ G) ≤ H
⇒-residualʳ-from G≤F⇒H .*≤* (Fx , Gx) = G≤F⇒H .*≤* Gx ≤ᶜ.refl Fx

⇒-residualʳ : RightResidual _≤_ _∧_ _⇒_
⇒-residualʳ .Function.Equivalence.to        = ⇒-residualʳ-to
⇒-residualʳ .Function.Equivalence.from      = ⇒-residualʳ-from
⇒-residualʳ .Function.Equivalence.to-cong   = λ { PropEq.refl → PropEq.refl }
⇒-residualʳ .Function.Equivalence.from-cong = λ { PropEq.refl → PropEq.refl }

⇒-∧-isResiduatedCommutativePomonoid : IsResiduatedCommutativePomonoid _≈_ _≤_ _∧_ _⇒_ ⊤
⇒-∧-isResiduatedCommutativePomonoid = record
  { isCommutativePomonoid = ∧-⊤-isCommutativePomonoid
  ; residuated            = comm∧residual⇒residuated ≤-isPreorder ∧-comm ⇒-residualʳ
  }

------------------------------------------------------------------------------
-- Lift monoids to presheaves

module LiftIsPomonoid
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
    (-, -, ≤ᶜ.trans x≤w w≤yz , ϕ₁ , ϕ₂)

  ∙-mono : Monotonic₂ _≤_ _≤_ _≤_ _∙_
  ∙-mono F₁≤F₂ G₁≤G₂ .*≤* (y , z , x≤yz , F₁y , G₁z) =
    (-, -, x≤yz , F₁≤F₂ .*≤* F₁y , G₁≤G₂ .*≤* G₁z)

  η-preserve-∙ : η (x ∙ᶜ y) ≤ η x ∙ η y
  η-preserve-∙ {x} {y} .*≤* {z} (lift z≤xy) = x , y , z≤xy , lift ≤ᶜ.refl , lift ≤ᶜ.refl

  η-preserve-∙⁻¹ : η x ∙ η y ≤ η (x ∙ᶜ y)
  η-preserve-∙⁻¹ {x} {y} .*≤* {z} (z₁ , z₂ , z≤z₁z₂ , lift z₁≤x , lift z₂≤y) =
    lift (≤ᶜ.trans z≤z₁z₂ (Mon.mono z₁≤x z₂≤y))

  ε : LowerSet
  ε = η εᶜ

  ∙-identityˡ : LeftIdentity _≈_ ε _∙_
  ∙-identityˡ F .Product.proj₁ .*≤* (y , z , x≤yz , lift y≤ε , Fz) =
    F .≤-closed (≤ᶜ.trans x≤yz (≤ᶜ.trans (Mon.mono y≤ε ≤ᶜ.refl) (≤ᶜ.≤-respʳ-≈ (Mon.identityˡ z) ≤ᶜ.refl) )) Fz
  ∙-identityˡ F .Product.proj₂ .*≤* Fx =
    (-, -, ≤ᶜ.≤-respˡ-≈ (Mon.identityˡ _) ≤ᶜ.refl , lift ≤ᶜ.refl , Fx)

  ∙-identityʳ : RightIdentity _≈_ ε _∙_
  ∙-identityʳ F .Product.proj₁ .*≤* (y , z , x≤yz , Fy , lift z≤ε) =
    F .≤-closed (≤ᶜ.trans x≤yz (≤ᶜ.trans (Mon.mono ≤ᶜ.refl z≤ε) (≤ᶜ.≤-respʳ-≈ (Mon.identityʳ y) ≤ᶜ.refl) )) Fy
  ∙-identityʳ F .Product.proj₂ .*≤* Fx =
    (-, -, ≤ᶜ.≤-respˡ-≈ (Mon.identityʳ _) ≤ᶜ.refl , Fx , lift ≤ᶜ.refl)

  ∙-identity : Identity _≈_ ε _∙_
  ∙-identity = (∙-identityˡ , ∙-identityʳ)

  ∙-assoc : Associative _≈_ _∙_
  ∙-assoc F G H .Product.proj₁ .*≤* (y , z , x≤yz , (u , v , y≤uv , Fu , Gv) , Hz) =
    let x≤u∙v∙z = ≤ᶜ.trans x≤yz (≤ᶜ.trans (Mon.mono y≤uv ≤ᶜ.refl) (≤ᶜ.≤-respʳ-≈ (Mon.assoc u v z)  ≤ᶜ.refl)) in
      (-, -, x≤u∙v∙z , Fu , (-, -, ≤ᶜ.refl , Gv , Hz))

  ∙-assoc F G H .Product.proj₂ .*≤* (y , z , x≤yz , Fy , (u , v , z≤uv , Gu , Hv)) =
    let x≤y∙u∙v = ≤ᶜ.trans x≤yz (≤ᶜ.trans (Mon.mono ≤ᶜ.refl z≤uv) (≤ᶜ.≤-respˡ-≈ (Mon.assoc y u v) ≤ᶜ.refl)) in
      (-, -, x≤y∙u∙v , (-, -, ≤ᶜ.refl , Fy , Gu) , Hv)

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

module LiftIsCommutativePomonoid
    {_∙ᶜ_}
    {εᶜ}
    (isCommutativePomonoid : IsCommutativePomonoid _≈ᶜ_ _≤ᶜ_ _∙ᶜ_ εᶜ)
  where

  private
    module Mon = IsCommutativePomonoid isCommutativePomonoid
  open LiftIsPomonoid Mon.isPomonoid public

  ∙-comm : Commutative _≈_ _∙_
  ∙-comm F G .Product.proj₁ .*≤* (y , z , x≤yz , Fy , Gz) = 
    (-, -, ≤ᶜ.trans x≤yz (≤ᶜ.≤-respˡ-≈ (Mon.comm z y) ≤ᶜ.refl) , Gz , Fy)
  ∙-comm F G .Product.proj₂ .*≤* (y , z , x≤yz , Gy , Fz) = 
    (-, -, ≤ᶜ.trans x≤yz (≤ᶜ.≤-respˡ-≈ (Mon.comm z y) ≤ᶜ.refl) , Fz , Gy)

  ∙-isCommutativePomonoid : IsCommutativePomonoid _≈_ _≤_ _∙_ ε
  ∙-isCommutativePomonoid = record
    { isPomonoid = ∙-isPomonoid
    ; comm       = ∙-comm 
    }

  _⊸_ : LowerSet → LowerSet → LowerSet
  (F ⊸ G) .ICarrier x        = ∀ {y} → F .ICarrier y → G .ICarrier (x ∙ᶜ y)
  (F ⊸ G) .≤-closed x≤z f Fy = G .≤-closed (Mon.mono x≤z ≤ᶜ.refl) (f Fy)

  ⊸-residual-to : (F ∙ G) ≤ H → G ≤ (F ⊸ H)
  ⊸-residual-to F∙G≤H .*≤* Gx Fy = 
    F∙G≤H .*≤* (-, -, ≤ᶜ.≤-respˡ-≈ (Mon.comm _ _) ≤ᶜ.refl , Fy , Gx)

  ⊸-residual-from : G ≤ (F ⊸ H) → (F ∙ G) ≤ H
  ⊸-residual-from {G} {F} {H} G≤F⊸H .*≤* (_ , _ , x≤y∙z , Fy , Gz) = 
    H .≤-closed (≤ᶜ.trans x≤y∙z (≤ᶜ.≤-respˡ-≈ (Mon.comm _ _) ≤ᶜ.refl)) (G≤F⊸H .*≤* Gz Fy)

  ⊸-residual : RightResidual _≤_ _∙_ _⊸_
  ⊸-residual .Function.Equivalence.to        = ⊸-residual-to
  ⊸-residual .Function.Equivalence.from      = ⊸-residual-from
  ⊸-residual .Function.Equivalence.to-cong   = λ { PropEq.refl → PropEq.refl }
  ⊸-residual .Function.Equivalence.from-cong = λ { PropEq.refl → PropEq.refl }

  ⊸-∙-isResiduatedCommutativePomonoid : IsResiduatedCommutativePomonoid _≈_ _≤_ _∙_ _⊸_ ε
  ⊸-∙-isResiduatedCommutativePomonoid = record 
    { isCommutativePomonoid = ∙-isCommutativePomonoid 
    ; residuated = comm∧residual⇒residuated ≤-isPreorder ∙-comm ⊸-residual 
    }

  ∙-∨-distrib : _DistributesOver_ _≤_ _∙_ _∨_
  ∙-∨-distrib = supremum∧residuated⇒distrib ≤-isPreorder ∨-supremum 
    (IsResiduatedCommutativePomonoid.residuated ⊸-∙-isResiduatedCommutativePomonoid)

module LiftIsDuoidal
    {_∙ᶜ_} 
    {_◁ᶜ_} 
    {εᶜ} 
    {ιᶜ}
    (isDuoidal : IsDuoidal _≈ᶜ_ _≤ᶜ_ _∙ᶜ_ _◁ᶜ_ εᶜ ιᶜ)
  where

  private
    module Duo = IsDuoidal isDuoidal
  open LiftIsPomonoid Duo.∙-isPomonoid public
  open LiftIsPomonoid Duo.◁-isPomonoid public
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
    (-, -, ≤ᶜ.trans x≤yz (≤ᶜ.trans (Duo.∙-mono y≤y₁y₂ z≤z₁z₂) (Duo.∙-◁-entropy y₁ y₂ z₁ z₂)) ,
      (-, -, ≤ᶜ.refl , F₁y₁ , F₂z₁) ,
      (-, -, ≤ᶜ.refl , G₁y₂ , G₂z₂))

  ∙-idem-ι : _SubidempotentOn_ _≤_ _∙_ ι
  ∙-idem-ι .*≤* (y , z , x≤y∙z , ιy , ιz) .lower =
    ≤ᶜ.trans x≤y∙z (≤ᶜ.trans (Duo.∙-mono (ιy .lower) (ιz .lower)) Duo.∙-idem-ι)

  ◁-idem-ε : _SuperidempotentOn_ _≤_ _◁_ ε
  ◁-idem-ε .*≤* εx =
    (-, -, ≤ᶜ.trans (εx .lower) Duo.◁-idem-ε , lift ≤ᶜ.refl , lift ≤ᶜ.refl)

  ε≤ι : ε ≤ ι
  ε≤ι .*≤* εx .lower = ≤ᶜ.trans (εx .lower) Duo.ε≲ι

  ∙-◁-isDuoidal : IsDuoidal _≈_ _≤_ _∙_ _◁_ ε ι
  ∙-◁-isDuoidal = record
    { ∙-isPomonoid = ∙-isPomonoid
    ; ◁-isPomonoid = ◁-isPomonoid
    ; ∙-◁-entropy  = ∙-◁-entropy
    ; ∙-idem-ι     = ∙-idem-ι
    ; ◁-idem-ε     = ◁-idem-ε
    ; ε≲ι          = ε≤ι
    }
 