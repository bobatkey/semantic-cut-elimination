{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level
open import Algebra
open import Algebra.Ordered
open import Algebra.Ordered.Consequences
open import Function using (flip)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; swap; <_,_>)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit using (⊤; tt)
open import Relation.Binary
open import Relation.Binary.Construct.Core.Symmetric as SymCore using (SymCore)
open import Relation.Binary.Lattice
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
import Relation.Binary.Construct.Flip.EqAndOrd as Flip

module PreSheaf
    {c ℓ₁ ℓ₂}
    {Carrier : Set c}      -- The underlying set
    {_≈_ : Rel Carrier ℓ₁} -- The underlying equality relation
    {_≤_ : Rel Carrier ℓ₂} -- The underlying order relationm
    (isPartialOrder : IsPartialOrder _≈_ _≤_)
    where

open IsPartialOrder isPartialOrder
  using ()
  renaming
    ( refl  to ≤-refl
    ; trans to ≤-trans
    )

private
  variable
    w x y z : Carrier

record PreSheaf : Set (suc (c ⊔ ℓ₂)) where
  no-eta-equality
  field
    ICarrier : Carrier → Set (c ⊔ ℓ₂)
    ≤-closed : x ≤ y → ICarrier y → ICarrier x
open PreSheaf public

private
  variable
    F F₁ F₂ : PreSheaf
    G G₁ G₂ : PreSheaf 
    H H₁ H₂ : PreSheaf

infix 4 _≤ᵖ_

record _≤ᵖ_ (F G : PreSheaf) : Set (c ⊔ ℓ₂) where
  no-eta-equality
  constructor mk-≤ᵖ
  field
    *≤ᵖ* : ∀ x → F .ICarrier x → G .ICarrier x
open _≤ᵖ_ public

infix 4 _≥ᵖ_

_≥ᵖ_ : PreSheaf → PreSheaf → Set (c ⊔ ℓ₂)
_≥ᵖ_ = flip _≤ᵖ_

infix 4 _≈ᵖ_

_≈ᵖ_ : PreSheaf → PreSheaf → Set (c ⊔ ℓ₂)
_≈ᵖ_ = SymCore _≤ᵖ_

≤ᵖ-refl : Reflexive _≤ᵖ_
≤ᵖ-refl .*≤ᵖ* x Fx = Fx

≤ᵖ-trans : Transitive _≤ᵖ_
≤ᵖ-trans F≤G G≤H .*≤ᵖ* x Fx = G≤H .*≤ᵖ* x (F≤G .*≤ᵖ* x Fx)

≤ᵖ-isPartialOrder : IsPartialOrder _≈ᵖ_ _≤ᵖ_
≤ᵖ-isPartialOrder = SymCore.isPreorder⇒isPartialOrder _≤ᵖ_ ≡-≤ᵖ-isPreorder
  where
    ≡-≤ᵖ-isPreorder : IsPreorder _≡_ _≤ᵖ_
    ≡-≤ᵖ-isPreorder = record 
      { isEquivalence = PropEq.isEquivalence 
      ; reflexive = λ { PropEq.refl → ≤ᵖ-refl } 
      ; trans = ≤ᵖ-trans
      }

open IsPartialOrder ≤ᵖ-isPartialOrder
  using ()
  renaming
    ( isPreorder to ≤ᵖ-isPreorder
    )

≥ᵖ-isPartialOrder : IsPartialOrder _≈ᵖ_ _≥ᵖ_
≥ᵖ-isPartialOrder = Flip.isPartialOrder ≤ᵖ-isPartialOrder

η : Carrier → PreSheaf
η x .ICarrier y = Lift c (y ≤ x)
η x .≤-closed z≤y y≤x = lift (≤-trans z≤y (y≤x .lower))

------------------------------------------------------------------------------
-- Construct a meet semilattice for presheaves

_∧ᵖ_ : PreSheaf → PreSheaf → PreSheaf
(F ∧ᵖ G) .ICarrier x = F .ICarrier x × G .ICarrier x
(F ∧ᵖ G) .≤-closed x≤y (Fy , Gy) = (F .≤-closed x≤y Fy , G .≤-closed x≤y Gy)

proj₁ᵖ : (F ∧ᵖ G) ≤ᵖ F
proj₁ᵖ .*≤ᵖ* x = proj₁

proj₂ᵖ : (F ∧ᵖ G) ≤ᵖ G
proj₂ᵖ .*≤ᵖ* x = proj₂

⟨_,_⟩ᵖ : F ≤ᵖ G → F ≤ᵖ H → F ≤ᵖ (G ∧ᵖ H)
⟨ H≤F , H≤G ⟩ᵖ .*≤ᵖ* x = < H≤F .*≤ᵖ* x , H≤G .*≤ᵖ* x >

∧ᵖ-isMeetSemilattice : IsMeetSemilattice _≈ᵖ_ _≤ᵖ_ _∧ᵖ_
∧ᵖ-isMeetSemilattice = record
  { isPartialOrder = ≤ᵖ-isPartialOrder
  ; infimum        = λ F G → (proj₁ᵖ , proj₂ᵖ , λ H → ⟨_,_⟩ᵖ)
  }

∧ᵖ-meetSemilattice : MeetSemilattice _ _ _
∧ᵖ-meetSemilattice = record
  { isMeetSemilattice = ∧ᵖ-isMeetSemilattice
  }

open import Relation.Binary.Lattice.Properties.MeetSemilattice ∧ᵖ-meetSemilattice
  using ()
  renaming
    ( ∧-monotonic to ∧ᵖ-monotonic
    ; ∧-assoc     to ∧ᵖ-assoc
    ; ∧-comm      to ∧ᵖ-comm
    )

∧ᵖ-⊤ᵖ-isPosemigroup : IsPosemigroup _≈ᵖ_ _≤ᵖ_ _∧ᵖ_
∧ᵖ-⊤ᵖ-isPosemigroup = record
  { isPomagma = record 
    { isPartialOrder = ≤ᵖ-isPartialOrder
    ; mono = ∧ᵖ-monotonic
    }
  ; assoc = ∧ᵖ-assoc
  }

⊤ᵖ : PreSheaf
⊤ᵖ .ICarrier x = Lift (c ⊔ ℓ₂) ⊤
⊤ᵖ .≤-closed x Fx = Fx

∧ᵖ-⊤ᵖ-isBoundedMeetSemilattice : IsBoundedMeetSemilattice _≈ᵖ_ _≤ᵖ_ _∧ᵖ_ ⊤ᵖ
∧ᵖ-⊤ᵖ-isBoundedMeetSemilattice = record
  { isMeetSemilattice = ∧ᵖ-isMeetSemilattice
  ; maximum           = λ F → mk-≤ᵖ (λ x Fx → lift tt)
  }

∧ᵖ-⊤ᵖ-boundedMeetSemilattice : BoundedMeetSemilattice _ _ _
∧ᵖ-⊤ᵖ-boundedMeetSemilattice = record
  { isBoundedMeetSemilattice = ∧ᵖ-⊤ᵖ-isBoundedMeetSemilattice
  }

open import Relation.Binary.Lattice.Properties.BoundedMeetSemilattice ∧ᵖ-⊤ᵖ-boundedMeetSemilattice
  using ()
  renaming
    ( identity to ∧ᵖ-⊤ᵖ-identity
    )

∧ᵖ-⊤ᵖ-isCommutativePomonoid : IsCommutativePomonoid _≈ᵖ_ _≤ᵖ_ _∧ᵖ_ ⊤ᵖ
∧ᵖ-⊤ᵖ-isCommutativePomonoid = record 
  { isPomonoid = record
    { isPosemigroup = ∧ᵖ-⊤ᵖ-isPosemigroup 
    ; identity = ∧ᵖ-⊤ᵖ-identity
    }
  ; comm = ∧ᵖ-comm
  }

------------------------------------------------------------------------------
-- Construct a join semilattice for presheaves

_∨ᵖ_ : PreSheaf → PreSheaf → PreSheaf
(F ∨ᵖ G) .ICarrier x = F .ICarrier x ⊎ G .ICarrier x
(F ∨ᵖ G) .≤-closed x≤y (inj₁ Fy) = inj₁ (F .≤-closed x≤y Fy)
(F ∨ᵖ G) .≤-closed x≤y (inj₂ Gy) = inj₂ (G .≤-closed x≤y Gy)

inj₁ᵖ : F ≤ᵖ (F ∨ᵖ G)
inj₁ᵖ .*≤ᵖ* x = inj₁

inj₂ᵖ : G ≤ᵖ (F ∨ᵖ G)
inj₂ᵖ .*≤ᵖ* x = inj₂

[_,_]ᵖ : F ≤ᵖ H → G ≤ᵖ H → (F ∨ᵖ G) ≤ᵖ H
[ H≥F , H≥G ]ᵖ .*≤ᵖ* x = [ H≥F .*≤ᵖ* x , H≥G .*≤ᵖ* x ]

∨ᵖ-isJoinSemilattice : IsJoinSemilattice _≈ᵖ_ _≤ᵖ_ _∨ᵖ_
∨ᵖ-isJoinSemilattice = record
  { isPartialOrder = ≤ᵖ-isPartialOrder
  ; supremum       = λ F G → (inj₁ᵖ , inj₂ᵖ , λ H → [_,_]ᵖ)
  }

open IsJoinSemilattice ∨ᵖ-isJoinSemilattice
  using ()
  renaming
    ( supremum to ∨ᵖ-supremum
    )

------------------------------------------------------------------------------
-- Construct a residuated pomonoid for presheaves

_⇒ᵖ_ : PreSheaf → PreSheaf → PreSheaf
(F ⇒ᵖ G) .ICarrier x = ∀ y → y ≤ x → F .ICarrier y → G .ICarrier y
(F ⇒ᵖ G) .≤-closed x≤y f z z≤x Fz = f z (≤-trans z≤x x≤y) Fz

⇒ᵖ-residual-to : (F ∧ᵖ G) ≤ᵖ H → G ≤ᵖ (F ⇒ᵖ H)
⇒ᵖ-residual-to {F} {G} {H} F∧G≤H .*≤ᵖ* x Gx y y≤x Fy = F∧G≤H .*≤ᵖ* y (Fy , G .≤-closed y≤x Gx)

⇒ᵖ-residual-from : G ≤ᵖ (F ⇒ᵖ H) → (F ∧ᵖ G) ≤ᵖ H
⇒ᵖ-residual-from G≤F⇒H .*≤ᵖ* x (Fx , Gx) = G≤F⇒H .*≤ᵖ* x Gx x ≤-refl Fx

⇒ᵖ-residual : RightResidual _≤ᵖ_ _∧ᵖ_ _⇒ᵖ_
⇒ᵖ-residual .Function.Equivalence.to        = ⇒ᵖ-residual-to
⇒ᵖ-residual .Function.Equivalence.from      = ⇒ᵖ-residual-from
⇒ᵖ-residual .Function.Equivalence.to-cong   = λ { PropEq.refl → PropEq.refl }
⇒ᵖ-residual .Function.Equivalence.from-cong = λ { PropEq.refl → PropEq.refl }

⇒ᵖ-∧ᵖ-isResiduatedCommutativePomonoid : IsResiduatedCommutativePomonoid _≈ᵖ_ _≤ᵖ_ _∧ᵖ_ _⇒ᵖ_ ⊤ᵖ
⇒ᵖ-∧ᵖ-isResiduatedCommutativePomonoid = record
  { isCommutativePomonoid = ∧ᵖ-⊤ᵖ-isCommutativePomonoid 
  ; residuated            = comm∧residual⇒residuated ≤ᵖ-isPreorder ∧ᵖ-comm ⇒ᵖ-residual
  }

------------------------------------------------------------------------------
-- Lift monoids to presheaves

module LiftIsPomonoid {_∙_} {ε} (isPomonoid : IsPomonoid _≈_ _≤_ _∙_ ε) where

  open IsPomonoid isPomonoid

  _∙ᵖ_ : PreSheaf → PreSheaf → PreSheaf
  (F ∙ᵖ G) .ICarrier x = 
    Σ[ y ∈ Carrier ] Σ[ z ∈ Carrier ] (x ≤ (y ∙ z) × F .ICarrier y × G .ICarrier z)
  (F ∙ᵖ G) .≤-closed x≤w (y , z , w≤yz , ϕ₁ , ϕ₂) =
    y , z , ≤-trans x≤w w≤yz , ϕ₁ , ϕ₂

  ∙ᵖ-mono : Monotonic₂ _≤ᵖ_ _≤ᵖ_ _≤ᵖ_ _∙ᵖ_
  ∙ᵖ-mono F₁≤F₂ G₁≤G₂ .*≤ᵖ* x (y , z , x≤yz , F₁y , G₁z) =
    y , z , x≤yz , F₁≤F₂ .*≤ᵖ* y F₁y , G₁≤G₂ .*≤ᵖ* z G₁z

  εᵖ : PreSheaf
  εᵖ = η ε

  ∙ᵖ-identityˡ : LeftIdentity _≈ᵖ_ εᵖ _∙ᵖ_
  ∙ᵖ-identityˡ F .proj₁ .*≤ᵖ* x (y , z , x≤yz , lift y≤ε , Fz) =
    F .≤-closed (≤-trans x≤yz (≤-trans (mono y≤ε ≤-refl) (≤-respʳ-≈ (identityˡ z) ≤-refl) )) Fz
  ∙ᵖ-identityˡ F .proj₂ .*≤ᵖ* x Fx =
    ε , x , ≤-respˡ-≈ (identityˡ x) ≤-refl , lift ≤-refl , Fx

  ∙ᵖ-identityʳ : RightIdentity _≈ᵖ_ εᵖ _∙ᵖ_
  ∙ᵖ-identityʳ F .proj₁ .*≤ᵖ* x (y , z , x≤yz , Fy , lift z≤ε) =
    F .≤-closed (≤-trans x≤yz (≤-trans (mono ≤-refl z≤ε) (≤-respʳ-≈ (identityʳ y) ≤-refl) )) Fy
  ∙ᵖ-identityʳ F .proj₂ .*≤ᵖ* x Fx =
    x , ε , ≤-respˡ-≈ (identityʳ x) ≤-refl , Fx , lift ≤-refl

  ∙ᵖ-identity : Identity _≈ᵖ_ εᵖ _∙ᵖ_
  ∙ᵖ-identity = (∙ᵖ-identityˡ , ∙ᵖ-identityʳ)

  ∙ᵖ-assoc : Associative _≈ᵖ_ _∙ᵖ_
  ∙ᵖ-assoc F G H .proj₁ .*≤ᵖ* x (y , z , x≤yz , (u , v , y≤uv , Fu , Gv) , Hz) = 
    (u , v ∙ z , x≤u∙v∙z , Fu , (v , z , ≤-refl , Gv , Hz))
    where 
      x≤u∙v∙z = ≤-trans x≤yz (≤-trans (mono y≤uv ≤-refl) (≤-respʳ-≈ (assoc u v z)  ≤-refl))
  ∙ᵖ-assoc F G H .proj₂ .*≤ᵖ* x (y , z , x≤yz , Fy , (u , v , z≤uv , Gu , Hv)) = 
    (y ∙ u , v , x≤y∙u∙v , (y , u , ≤-refl , Fy , Gu) , Hv)
    where
      x≤y∙u∙v = ≤-trans x≤yz (≤-trans (mono ≤-refl z≤uv) (≤-respˡ-≈ (assoc y u v) ≤-refl))

  ∙ᵖ-isPomonoid : IsPomonoid _≈ᵖ_ _≤ᵖ_ _∙ᵖ_ εᵖ
  ∙ᵖ-isPomonoid = record 
    { isPosemigroup = record 
      { isPomagma = record
        { isPartialOrder = ≤ᵖ-isPartialOrder 
        ; mono = ∙ᵖ-mono
        } 
      ; assoc = ∙ᵖ-assoc 
      }
    ; identity = ∙ᵖ-identity 
    }

module LiftIsCommutativePomonoid {_∙_} {ε} (isCommutativePomonoid : IsCommutativePomonoid _≈_ _≤_ _∙_ ε) where

  open IsCommutativePomonoid isCommutativePomonoid
  open LiftIsPomonoid isPomonoid public

  ∙ᵖ-comm : Commutative _≈ᵖ_ _∙ᵖ_
  ∙ᵖ-comm F G .proj₁ .*≤ᵖ* x (y , z , x≤yz , Fy , Gz) = (z , y , trans x≤yz (≤-respˡ-≈ (comm z y) ≤-refl) , Gz , Fy)
  ∙ᵖ-comm F G .proj₂ .*≤ᵖ* x (y , z , x≤yz , Gy , Fz) = (z , y , trans x≤yz (≤-respˡ-≈ (comm z y) ≤-refl) , Fz , Gy)

  ∙ᵖ-isCommutativePomonoid : IsCommutativePomonoid _≈ᵖ_ _≤ᵖ_ _∙ᵖ_ εᵖ
  ∙ᵖ-isCommutativePomonoid = record
    { isPomonoid = ∙ᵖ-isPomonoid
    ; comm       = ∙ᵖ-comm 
    }

  _⇨ᵖ_ : PreSheaf → PreSheaf → PreSheaf
  (F ⇨ᵖ G) .ICarrier x = ∀ y → F .ICarrier y → G .ICarrier (x ∙ y)
  (F ⇨ᵖ G) .≤-closed x≤z f y Fy = G .≤-closed (mono x≤z refl) (f y Fy)

  ⇨ᵖ-residual-to : (F ∙ᵖ G) ≤ᵖ H → G ≤ᵖ (F ⇨ᵖ H)
  ⇨ᵖ-residual-to F∙G≤H .*≤ᵖ* x Gx y Fy = 
    F∙G≤H .*≤ᵖ* (x ∙ y) (y , x , ≤-respˡ-≈ (comm y x) ≤-refl , Fy , Gx)

  ⇨ᵖ-residual-from : G ≤ᵖ (F ⇨ᵖ H) → (F ∙ᵖ G) ≤ᵖ H
  ⇨ᵖ-residual-from {G} {F} {H} G≤F⇨H .*≤ᵖ* x (y , z , x≤y∙z , Fy , Gz) = 
    H .≤-closed (trans x≤y∙z (≤-respˡ-≈ (comm z y) ≤-refl)) (G≤F⇨H .*≤ᵖ* z Gz y Fy)

  ⇨ᵖ-residual : RightResidual _≤ᵖ_ _∙ᵖ_ _⇨ᵖ_
  ⇨ᵖ-residual .Function.Equivalence.to        = ⇨ᵖ-residual-to
  ⇨ᵖ-residual .Function.Equivalence.from      = ⇨ᵖ-residual-from
  ⇨ᵖ-residual .Function.Equivalence.to-cong   = λ { PropEq.refl → PropEq.refl }
  ⇨ᵖ-residual .Function.Equivalence.from-cong = λ { PropEq.refl → PropEq.refl }

  ⇨ᵖ-∙ᵖ-isResiduatedCommutativePomonoid : IsResiduatedCommutativePomonoid _≈ᵖ_ _≤ᵖ_ _∙ᵖ_ _⇨ᵖ_ εᵖ
  ⇨ᵖ-∙ᵖ-isResiduatedCommutativePomonoid = record 
    { isCommutativePomonoid = ∙ᵖ-isCommutativePomonoid 
    ; residuated = comm∧residual⇒residuated ≤ᵖ-isPreorder ∙ᵖ-comm ⇨ᵖ-residual 
    }

  ∙ᵖ-∨ᵖ-distrib : _DistributesOver_ _≤ᵖ_ _∙ᵖ_ _∨ᵖ_
  ∙ᵖ-∨ᵖ-distrib = supremum∧residuated⇒distrib ≤ᵖ-isPreorder ∨ᵖ-supremum 
    (IsResiduatedCommutativePomonoid.residuated ⇨ᵖ-∙ᵖ-isResiduatedCommutativePomonoid)

module LiftIsDuoidal {_∙_} {_▷_} {ε} {ι} (isDuoidal : IsDuoidal _≈_ _≤_ _∙_ _▷_ ε ι) where

  open IsDuoidal isDuoidal
  open LiftIsPomonoid ∙-isPomonoid public
  open LiftIsPomonoid ▷-isPomonoid public
    renaming
      ( _∙ᵖ_ to _▷ᵖ_
      ; εᵖ   to ιᵖ
      ; ∙ᵖ-mono to ▷ᵖ-mono
      ; ∙ᵖ-assoc to ▷ᵖ-assoc
      ; ∙ᵖ-identity to ▷ᵖ-identity
      ; ∙ᵖ-identityˡ to ▷ᵖ-identityˡ
      ; ∙ᵖ-identityʳ to ▷ᵖ-identityʳ
      ; ∙ᵖ-isPomonoid to ▷ᵖ-isPomonoid
      )

  ∙ᵖ-▷ᵖ-exchange : Exchange _≤ᵖ_ _∙ᵖ_ _▷ᵖ_
  ∙ᵖ-▷ᵖ-exchange F₁ G₁ F₂ G₂ .*≤ᵖ* x 
    (y , z , x≤yz , 
      (y₁ , y₂ , y≤y₁y₂ , F₁y₁ , G₁y₂) , 
      (z₁ , z₂ , z≤z₁z₂ , F₂z₁ , G₂z₂)) = 
    (y₁ ∙ z₁ , y₂ ∙ z₂ , trans x≤yz (trans (∙-mono y≤y₁y₂ z≤z₁z₂) (∙-▷-exchange y₁ y₂ z₁ z₂)) ,
      (y₁ , z₁ , refl , F₁y₁ , F₂z₁) , 
      (y₂ , z₂ , refl , G₁y₂ , G₂z₂))

  ∙ᵖ-idempotent-ιᵖ : _SubidempotentOn_ _≤ᵖ_ _∙ᵖ_ ιᵖ
  ∙ᵖ-idempotent-ιᵖ .*≤ᵖ* x (y , z , x≤y∙z , ιy , ιz) .lower = 
    trans x≤y∙z (trans (∙-mono (ιy .lower) (ιz .lower)) ∙-idempotent-ι)

  ▷ᵖ-idempotent-εᵖ : _SuperidempotentOn_ _≤ᵖ_ _▷ᵖ_ εᵖ
  ▷ᵖ-idempotent-εᵖ .*≤ᵖ* x εx = 
    (ε , ε , trans (εx .lower) ▷-idempotent-ε , lift refl , lift refl)

  εᵖ≤ιᵖ : εᵖ ≤ᵖ ιᵖ 
  εᵖ≤ιᵖ .*≤ᵖ* x εx .lower = trans (εx .lower) ε≲ι

  ∙ᵖ-▷ᵖ-isDuoidal : IsDuoidal _≈ᵖ_ _≤ᵖ_ _∙ᵖ_ _▷ᵖ_ εᵖ ιᵖ
  ∙ᵖ-▷ᵖ-isDuoidal = record
    { ∙-isPomonoid   = ∙ᵖ-isPomonoid
    ; ▷-isPomonoid   = ▷ᵖ-isPomonoid
    ; ∙-▷-exchange   = ∙ᵖ-▷ᵖ-exchange
    ; ∙-idempotent-ι = ∙ᵖ-idempotent-ιᵖ
    ; ▷-idempotent-ε = ▷ᵖ-idempotent-εᵖ
    ; ε≲ι            = εᵖ≤ιᵖ
    }
