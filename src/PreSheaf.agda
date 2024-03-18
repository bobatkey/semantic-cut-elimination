{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level
open import Algebra
open import Algebra.Definitions
open import Algebra.Ordered
open import Algebra.Ordered.Definitions
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

module PreSheaf {a ℓ₁ ℓ₂} (poset : Poset a ℓ₁ ℓ₂) where

open Poset poset
  using (Carrier; _≈_; _≤_)
  renaming
    ( refl  to ≤-refl
    ; trans to ≤-trans
    )

record PreSheaf : Set (suc (a ⊔ ℓ₂)) where
  no-eta-equality
  field
    ICarrier : Carrier → Set (a ⊔ ℓ₂)
    ≤-closed : ∀ {x y} → x ≤ y → ICarrier y → ICarrier x
open PreSheaf

private
  variable
    F F₁ F₂ : PreSheaf
    G G₁ G₂ : PreSheaf 
    H H₁ H₂ : PreSheaf

infix 4 _≤ᴾ_

record _≤ᴾ_ (F G : PreSheaf) : Set (a ⊔ ℓ₂) where
  no-eta-equality
  constructor mk-≤ᴾ
  field
    *≤ᴾ* : ∀ x → F .ICarrier x → G .ICarrier x
open _≤ᴾ_

infix 4 _≥ᴾ_

_≥ᴾ_ : PreSheaf → PreSheaf → Set (a ⊔ ℓ₂)
_≥ᴾ_ = flip _≤ᴾ_

infix 4 _≈ᴾ_

_≈ᴾ_ : PreSheaf → PreSheaf → Set (a ⊔ ℓ₂)
_≈ᴾ_ = SymCore _≤ᴾ_

≤ᴾ-refl : Reflexive _≤ᴾ_
≤ᴾ-refl .*≤ᴾ* x Fx = Fx

≤ᴾ-trans : Transitive _≤ᴾ_
≤ᴾ-trans F≤G G≤H .*≤ᴾ* x Fx = G≤H .*≤ᴾ* x (F≤G .*≤ᴾ* x Fx) 

≤ᴾ-isPartialOrder : IsPartialOrder _≈ᴾ_ _≤ᴾ_
≤ᴾ-isPartialOrder = SymCore.isPreorder⇒isPartialOrder _≤ᴾ_ ≡-≤ᴾ-isPreorder
  where
    ≡-≤ᴾ-isPreorder : IsPreorder _≡_ _≤ᴾ_
    ≡-≤ᴾ-isPreorder = record 
      { isEquivalence = PropEq.isEquivalence 
      ; reflexive = λ { PropEq.refl → ≤ᴾ-refl } 
      ; trans = ≤ᴾ-trans
      }

open IsPartialOrder ≤ᴾ-isPartialOrder
  using ()
  renaming
    ( isPreorder to ≤ᴾ-isPreorder
    )

≥ᴾ-isPartialOrder : IsPartialOrder _≈ᴾ_ _≥ᴾ_
≥ᴾ-isPartialOrder = Flip.isPartialOrder ≤ᴾ-isPartialOrder

η : Carrier → PreSheaf
η x .ICarrier y = Lift a (y ≤ x)
η x .≤-closed z≤y y≤x = lift (≤-trans z≤y (y≤x .lower))

------------------------------------------------------------------------------
-- Construct a meet semilattice for presheaves

_∧ᴾ_ : PreSheaf → PreSheaf → PreSheaf
(F ∧ᴾ G) .ICarrier x = F .ICarrier x × G .ICarrier x
(F ∧ᴾ G) .≤-closed x≤y (Fy , Gy) = (F .≤-closed x≤y Fy , G .≤-closed x≤y Gy)

proj₁ᴾ : (F ∧ᴾ G) ≤ᴾ F
proj₁ᴾ .*≤ᴾ* x = proj₁

proj₂ᴾ : (F ∧ᴾ G) ≤ᴾ G
proj₂ᴾ .*≤ᴾ* x = proj₂

⟨_,_⟩ᴾ : F ≤ᴾ G → F ≤ᴾ H → F ≤ᴾ (G ∧ᴾ H)
⟨ H≤F , H≤G ⟩ᴾ .*≤ᴾ* x = < H≤F .*≤ᴾ* x , H≤G .*≤ᴾ* x >

∧ᴾ-isMeetSemilattice : IsMeetSemilattice _≈ᴾ_ _≤ᴾ_ _∧ᴾ_
∧ᴾ-isMeetSemilattice = record
  { isPartialOrder = ≤ᴾ-isPartialOrder
  ; infimum        = λ F G → (proj₁ᴾ , proj₂ᴾ , λ H → ⟨_,_⟩ᴾ)
  }

∧ᴾ-meetSemilattice : MeetSemilattice _ _ _
∧ᴾ-meetSemilattice = record
  { isMeetSemilattice = ∧ᴾ-isMeetSemilattice
  }

open import Relation.Binary.Lattice.Properties.MeetSemilattice ∧ᴾ-meetSemilattice
  using ()
  renaming
    ( ∧-monotonic to ∧ᴾ-monotonic
    ; ∧-assoc     to ∧ᴾ-assoc
    ; ∧-comm      to ∧ᴾ-comm
    )

∧ᴾ-⊤ᴾ-isPosemigroup : IsPosemigroup _≈ᴾ_ _≤ᴾ_ _∧ᴾ_
∧ᴾ-⊤ᴾ-isPosemigroup = record
  { isPomagma = record 
    { isPartialOrder = ≤ᴾ-isPartialOrder
    ; mono = ∧ᴾ-monotonic
    }
  ; assoc = ∧ᴾ-assoc
  }

⊤ᴾ : PreSheaf
⊤ᴾ .ICarrier x = Lift (a ⊔ ℓ₂) ⊤
⊤ᴾ .≤-closed x Fx = Fx

∧ᴾ-⊤ᴾ-isBoundedMeetSemilattice : IsBoundedMeetSemilattice _≈ᴾ_ _≤ᴾ_ _∧ᴾ_ ⊤ᴾ
∧ᴾ-⊤ᴾ-isBoundedMeetSemilattice = record
  { isMeetSemilattice = ∧ᴾ-isMeetSemilattice
  ; maximum           = λ F → mk-≤ᴾ (λ x Fx → lift tt)
  }

∧ᴾ-⊤ᴾ-boundedMeetSemilattice : BoundedMeetSemilattice _ _ _
∧ᴾ-⊤ᴾ-boundedMeetSemilattice = record
  { isBoundedMeetSemilattice = ∧ᴾ-⊤ᴾ-isBoundedMeetSemilattice
  }

open import Relation.Binary.Lattice.Properties.BoundedMeetSemilattice ∧ᴾ-⊤ᴾ-boundedMeetSemilattice
  using ()
  renaming
    ( identity to ∧ᴾ-⊤ᴾ-identity
    )

∧ᴾ-⊤ᴾ-isCommutativePomonoid : IsCommutativePomonoid _≈ᴾ_ _≤ᴾ_ _∧ᴾ_ ⊤ᴾ
∧ᴾ-⊤ᴾ-isCommutativePomonoid = record 
  { isPomonoid = record
    { isPosemigroup = ∧ᴾ-⊤ᴾ-isPosemigroup 
    ; identity = ∧ᴾ-⊤ᴾ-identity
    }
  ; comm = ∧ᴾ-comm
  }

------------------------------------------------------------------------------
-- Construct a join semilattice for presheaves

_∨ᴾ_ : PreSheaf → PreSheaf → PreSheaf
(F ∨ᴾ G) .ICarrier x = F .ICarrier x ⊎ G .ICarrier x
(F ∨ᴾ G) .≤-closed x≤y (inj₁ Fy) = inj₁ (F .≤-closed x≤y Fy)
(F ∨ᴾ G) .≤-closed x≤y (inj₂ Gy) = inj₂ (G .≤-closed x≤y Gy)

inj₁ᴾ : F ≤ᴾ (F ∨ᴾ G)
inj₁ᴾ .*≤ᴾ* x = inj₁

inj₂ᴾ : G ≤ᴾ (F ∨ᴾ G)
inj₂ᴾ .*≤ᴾ* x = inj₂

[_,_]ᴾ : F ≤ᴾ H → G ≤ᴾ H → (F ∨ᴾ G) ≤ᴾ H
[ H≥F , H≥G ]ᴾ .*≤ᴾ* x = [ H≥F .*≤ᴾ* x , H≥G .*≤ᴾ* x ]

∨ᴾ-isJoinSemilattice : IsJoinSemilattice _≈ᴾ_ _≤ᴾ_ _∨ᴾ_
∨ᴾ-isJoinSemilattice = record
  { isPartialOrder = ≤ᴾ-isPartialOrder
  ; supremum       = λ F G → (inj₁ᴾ , inj₂ᴾ , λ H → [_,_]ᴾ)
  }

open IsJoinSemilattice ∨ᴾ-isJoinSemilattice
  using ()
  renaming
    ( supremum to ∨ᴾ-supremum
    )

------------------------------------------------------------------------------
-- Construct a residuated pomonoid for presheaves

_⇒ᴾ_ : PreSheaf → PreSheaf → PreSheaf
(F ⇒ᴾ G) .ICarrier x = ∀ y → y ≤ x → F .ICarrier y → G .ICarrier y
(F ⇒ᴾ G) .≤-closed x≤y f z z≤x Fz = f z (≤-trans z≤x x≤y) Fz

⇒ᴾ-residual-to : (F ∧ᴾ G) ≤ᴾ H → G ≤ᴾ (F ⇒ᴾ H)
⇒ᴾ-residual-to {F} {G} {H} F∧G≤H .*≤ᴾ* x Gx y y≤x Fy = F∧G≤H .*≤ᴾ* y (Fy , G .≤-closed y≤x Gx)

⇒ᴾ-residual-from : G ≤ᴾ (F ⇒ᴾ H) → (F ∧ᴾ G) ≤ᴾ H
⇒ᴾ-residual-from G≤F⇒H .*≤ᴾ* x (Fx , Gx) = G≤F⇒H .*≤ᴾ* x Gx x ≤-refl Fx

⇒ᴾ-residual : RightResidual _≤ᴾ_ _∧ᴾ_ _⇒ᴾ_
⇒ᴾ-residual .Function.Equivalence.to        = ⇒ᴾ-residual-to
⇒ᴾ-residual .Function.Equivalence.from      = ⇒ᴾ-residual-from
⇒ᴾ-residual .Function.Equivalence.to-cong   = λ { PropEq.refl → PropEq.refl }
⇒ᴾ-residual .Function.Equivalence.from-cong = λ { PropEq.refl → PropEq.refl }

⇒ᴾ-∧ᴾ-isResiduatedCommutativePomonoid : IsResiduatedCommutativePomonoid _≈ᴾ_ _≤ᴾ_ _∧ᴾ_ _⇒ᴾ_ ⊤ᴾ
⇒ᴾ-∧ᴾ-isResiduatedCommutativePomonoid = record
  { isCommutativePomonoid = ∧ᴾ-⊤ᴾ-isCommutativePomonoid 
  ; residuated            = comm∧residual⇒residuated ≤ᴾ-isPreorder ∧ᴾ-comm ⇒ᴾ-residual
  }

------------------------------------------------------------------------------
-- Lift monoids to presheaves

module LiftIsPomonoid {_∙_} {ε} (isPomonoid : IsPomonoid _≈_ _≤_ _∙_ ε) where

  open IsPomonoid isPomonoid

  _∙ᴾ_ : PreSheaf → PreSheaf → PreSheaf
  (F ∙ᴾ G) .ICarrier x = 
    Σ[ y ∈ Carrier ] Σ[ z ∈ Carrier ] (x ≤ (y ∙ z) × F .ICarrier y × G .ICarrier z)
  (F ∙ᴾ G) .≤-closed x≤w (y , z , w≤yz , ϕ₁ , ϕ₂) =
    y , z , ≤-trans x≤w w≤yz , ϕ₁ , ϕ₂

  ∙ᴾ-mono : Monotonic₂ _≤ᴾ_ _≤ᴾ_ _≤ᴾ_ _∙ᴾ_
  ∙ᴾ-mono F₁≤F₂ G₁≤G₂ .*≤ᴾ* x (y , z , x≤yz , F₁y , G₁z) =
    y , z , x≤yz , F₁≤F₂ .*≤ᴾ* y F₁y , G₁≤G₂ .*≤ᴾ* z G₁z

  εᴾ : PreSheaf
  εᴾ = η ε

  ∙ᴾ-identityˡ : LeftIdentity _≈ᴾ_ εᴾ _∙ᴾ_
  ∙ᴾ-identityˡ F .proj₁ .*≤ᴾ* x (y , z , x≤yz , lift y≤ε , Fz) =
    F .≤-closed (≤-trans x≤yz (≤-trans (mono y≤ε ≤-refl) (≤-respʳ-≈ (identityˡ z) ≤-refl) )) Fz
  ∙ᴾ-identityˡ F .proj₂ .*≤ᴾ* x Fx =
    ε , x , ≤-respˡ-≈ (identityˡ x) ≤-refl , lift ≤-refl , Fx

  ∙ᴾ-identityʳ : RightIdentity _≈ᴾ_ εᴾ _∙ᴾ_
  ∙ᴾ-identityʳ F .proj₁ .*≤ᴾ* x (y , z , x≤yz , Fy , lift z≤ε) =
    F .≤-closed (≤-trans x≤yz (≤-trans (mono ≤-refl z≤ε) (≤-respʳ-≈ (identityʳ y) ≤-refl) )) Fy
  ∙ᴾ-identityʳ F .proj₂ .*≤ᴾ* x Fx =
    x , ε , ≤-respˡ-≈ (identityʳ x) ≤-refl , Fx , lift ≤-refl

  ∙ᴾ-identity : Identity _≈ᴾ_ εᴾ _∙ᴾ_
  ∙ᴾ-identity = (∙ᴾ-identityˡ , ∙ᴾ-identityʳ)

  ∙ᴾ-assoc : Associative _≈ᴾ_ _∙ᴾ_
  ∙ᴾ-assoc F G H .proj₁ .*≤ᴾ* x (y , z , x≤yz , (u , v , y≤uv , Fu , Gv) , Hz) = 
    (u , v ∙ z , x≤u∙v∙z , Fu , (v , z , ≤-refl , Gv , Hz))
    where 
      x≤u∙v∙z = ≤-trans x≤yz (≤-trans (mono y≤uv ≤-refl) (≤-respʳ-≈ (assoc u v z)  ≤-refl))
  ∙ᴾ-assoc F G H .proj₂ .*≤ᴾ* x (y , z , x≤yz , Fy , (u , v , z≤uv , Gu , Hv)) = 
    (y ∙ u , v , x≤y∙u∙v , (y , u , ≤-refl , Fy , Gu) , Hv)
    where
      x≤y∙u∙v = ≤-trans x≤yz (≤-trans (mono ≤-refl z≤uv) (≤-respˡ-≈ (assoc y u v) ≤-refl))

  ∙ᴾ-isPomonoid : IsPomonoid _≈ᴾ_ _≤ᴾ_ _∙ᴾ_ εᴾ
  ∙ᴾ-isPomonoid = record 
    { isPosemigroup = record 
      { isPomagma = record
        { isPartialOrder = ≤ᴾ-isPartialOrder 
        ; mono = ∙ᴾ-mono
        } 
      ; assoc = ∙ᴾ-assoc 
      }
    ; identity = ∙ᴾ-identity 
    }

module LiftIsCommutativePomonoid {_∙_} {ε} (isCommutativePomonoid : IsCommutativePomonoid _≈_ _≤_ _∙_ ε) where

  open IsCommutativePomonoid isCommutativePomonoid
  open LiftIsPomonoid isPomonoid

  ∙ᴾ-comm : Commutative _≈ᴾ_ _∙ᴾ_
  ∙ᴾ-comm F G .proj₁ .*≤ᴾ* x (y , z , x≤yz , Fy , Gz) = (z , y , trans x≤yz (≤-respˡ-≈ (comm z y) ≤-refl) , Gz , Fy)
  ∙ᴾ-comm F G .proj₂ .*≤ᴾ* x (y , z , x≤yz , Gy , Fz) = (z , y , trans x≤yz (≤-respˡ-≈ (comm z y) ≤-refl) , Fz , Gy)

  ∙ᴾ-isCommutativePomonoid : IsCommutativePomonoid _≈ᴾ_ _≤ᴾ_ _∙ᴾ_ εᴾ
  ∙ᴾ-isCommutativePomonoid = record
    { isPomonoid = ∙ᴾ-isPomonoid
    ; comm       = ∙ᴾ-comm 
    }

  _⇨ᴾ_ : PreSheaf → PreSheaf → PreSheaf
  (F ⇨ᴾ G) .ICarrier x = ∀ y → F .ICarrier y → G .ICarrier (x ∙ y)
  (F ⇨ᴾ G) .≤-closed x≤z f y Fy = G .≤-closed (mono x≤z refl) (f y Fy)

  ⇨ᴾ-residual-to : (F ∙ᴾ G) ≤ᴾ H → G ≤ᴾ (F ⇨ᴾ H)
  ⇨ᴾ-residual-to F∙G≤H .*≤ᴾ* x Gx y Fy = 
    F∙G≤H .*≤ᴾ* (x ∙ y) (y , x , ≤-respˡ-≈ (comm y x) ≤-refl , Fy , Gx)

  ⇨ᴾ-residual-from : G ≤ᴾ (F ⇨ᴾ H) → (F ∙ᴾ G) ≤ᴾ H
  ⇨ᴾ-residual-from {G} {F} {H} G≤F⇨H .*≤ᴾ* x (y , z , x≤y∙z , Fy , Gz) = 
    H .≤-closed (trans x≤y∙z (≤-respˡ-≈ (comm z y) ≤-refl)) (G≤F⇨H .*≤ᴾ* z Gz y Fy)

  ⇨ᴾ-residual : RightResidual _≤ᴾ_ _∙ᴾ_ _⇨ᴾ_
  ⇨ᴾ-residual .Function.Equivalence.to        = ⇨ᴾ-residual-to
  ⇨ᴾ-residual .Function.Equivalence.from      = ⇨ᴾ-residual-from
  ⇨ᴾ-residual .Function.Equivalence.to-cong   = λ { PropEq.refl → PropEq.refl }
  ⇨ᴾ-residual .Function.Equivalence.from-cong = λ { PropEq.refl → PropEq.refl }

  ⇨ᴾ-∙ᴾ-isResiduatedCommutativePomonoid : IsResiduatedCommutativePomonoid _≈ᴾ_ _≤ᴾ_ _∙ᴾ_ _⇨ᴾ_ εᴾ
  ⇨ᴾ-∙ᴾ-isResiduatedCommutativePomonoid = record 
    { isCommutativePomonoid = ∙ᴾ-isCommutativePomonoid 
    ; residuated = comm∧residual⇒residuated ≤ᴾ-isPreorder ∙ᴾ-comm ⇨ᴾ-residual 
    }

  ∙ᴾ-∨ᴾ-distrib : _DistributesOver_ _≤ᴾ_ _∙ᴾ_ _∨ᴾ_
  ∙ᴾ-∨ᴾ-distrib = supremum∧residuated⇒distrib ≤ᴾ-isPreorder ∨ᴾ-supremum 
    (IsResiduatedCommutativePomonoid.residuated ⇨ᴾ-∙ᴾ-isResiduatedCommutativePomonoid)

-- -- FIXME: If we have two monoids in a duoidal relationship, then they
-- -- have this relationship on the presheaf preorder. Let's do the
-- -- simple case where they share a unit first.
-- module Duoidal {_∙_ : A → A → A} {_▷_ : A → A → A} {ι : A}
--                (∙-isMonoid : IsMonoid ≤-isPreorder _∙_ ι)
--                (▷-isMonoid : IsMonoid ≤-isPreorder _▷_ ι)
--                (∙-▷-isDuoidal : IsDuoidal ≤-isPreorder ∙-isMonoid ▷-isMonoid)
--   where

--   open Monoid ∙-isMonoid using (_∙_)
--   open Monoid ▷-isMonoid renaming (_∙_ to _⍮_)
--   open IsDuoidal ∙-▷-isDuoidal renaming (exchange to ∙-▷-exchange)
--   open IsMonoid ∙-isMonoid

--   ∙-⍮-exchange : ∀ {w x y z} → ((w ⍮ x) ∙ (y ⍮ z)) ≤ᴾ ((w ∙ y) ⍮ (x ∙ z))
--   ∙-⍮-exchange .*≤ᴾ* x
--       (y , z , x≤yz , (y₁ , y₂ , y≤y₁y₂ , Wy₁ , Xy₂) ,
--                       (z₁ , z₂ , z≤z₁z₂ , Yz₁ , Zz₂)) =
--       (y₁ ∙ z₁) , y₂ ∙ z₂ ,
--       trans x≤yz (trans (mono y≤y₁y₂ z≤z₁z₂) ∙-▷-exchange) ,
--       (y₁ , z₁ , refl , Wy₁ , Yz₁) ,
--       (y₂ , z₂ , refl , Xy₂ , Zz₂)


-- -- FIXME: not sheaves! we do not necessarily know that α : PreSheaf →
-- -- Sheaf defined below preserves finite limits. This is an extra
-- -- property that would turn it into a preorder Grothendieck topos. I
-- -- guess that this would need _&_ to distribute over meets in A (if we
-- -- assume that A has meets)?
-- --
-- -- Alternatively, the closure of the closure operation
-- --     C X x = Σ[ t ∈ Tree (Σ[ x ∈ A ] X .ICarrier x) ] x ≤ join t

-- module Sheaf (_&_ : A → A → A)
--              (&-mono : ∀ {x₁ y₁ x₂ y₂} → x₁ ≤ x₂ → y₁ ≤ y₂ → (x₁ & y₁) ≤ (x₂ & y₂))
--           where -- we have some binary operator that we want to name the joins

--   data Tree {a} (A : Set a) : Set a where
--     lf : A → Tree A
--     br : Tree A → Tree A → Tree A

--   map-Tree : ∀ {a ℓ}{X : A → Set a}{Y : A → Set ℓ} →
--              ((x : A) → X x → Y x) → Tree (Σ[ x ∈ A ] X x) → Tree (Σ[ x ∈ A ] Y x)
--   map-Tree f (lf (a , x)) = lf (a , f a x)
--   map-Tree f (br s t) = br (map-Tree f s) (map-Tree f t)

--   join : ∀ {X : A → Set (a ⊔ ℓ₂)} → Tree (Σ[ x ∈ A ] X x) → A
--   join (lf (x , _)) = x
--   join (br s t) = join s & join t

--   map-join : ∀ {X Y : A → Set (a ⊔ ℓ₂)} →
--              (f : (x : A) → X x → Y x) →
--              (t : Tree (Σ[ x ∈ A ] X x)) →
--              join t ≤ join (map-Tree f t)
--   map-join f (lf x) = refl
--   map-join f (br s t) = &-mono (map-join f s) (map-join f t)

--   flatten : {X : A → Set (a ⊔ ℓ₂)} →
--             Tree (Σ[ x ∈ A ] (Σ[ t ∈ Tree (Σ[ y ∈ A ] X y) ] x ≤ join t)) →
--             Tree (Σ[ y ∈ A ] X y)
--   flatten (lf (x , t , ϕ)) = t
--   flatten (br s t)         = br (flatten s) (flatten t)

--   flatten-join : {X : A → Set (a ⊔ ℓ₂)} →
--                  (t : Tree (Σ[ x ∈ A ] (Σ[ t ∈ Tree (Σ[ y ∈ A ] X y) ] x ≤ join t))) →
--                  join t ≤ join (flatten t)
--   flatten-join (lf (x , t , ϕ)) = ϕ
--   flatten-join (br s t) = &-mono (flatten-join s) (flatten-join t)

--   record Sheaf : Set (suc (a ⊔ ℓ₂)) where
--     no-eta-equality
--     field
--       SCarrier  : A → Set (a ⊔ ℓ₂)
--       S≤-closed : ∀ {x y} → x ≤ y → SCarrier y → SCarrier x
--       Sclosed   : (t : Tree (Σ[ x ∈ A ] SCarrier x)) → SCarrier (join t)
--   open Sheaf

--   record _≤S_ (F G : Sheaf) : Set (a ⊔ ℓ₂) where
--     no-eta-equality
--     field
--       *≤S* : ∀ x → F .SCarrier x → G .SCarrier x
--   open _≤S_

--   ≤S-refl : ∀ {F} → F ≤S F
--   ≤S-refl .*≤S* x Fx = Fx

--   ≤S-trans : ∀ {F G H} → F ≤S G → G ≤S H → F ≤S H
--   ≤S-trans F≤G G≤H .*≤S* = λ x z → G≤H .*≤S* x (F≤G .*≤S* x z)

--   ≤S-isPreorder : IsPreorder _≤S_
--   ≤S-isPreorder .IsPreorder.refl = ≤S-refl
--   ≤S-isPreorder .IsPreorder.trans = ≤S-trans

--   _≃S_ = SymCore _≤S_

--   ------------------------------------------------------------------------------
--   -- Turn a presheaf into a sheaf by closing under imaginary joins
--   α : PreSheaf → Sheaf
--   α F .SCarrier x = Σ[ t ∈ Tree (Σ[ x ∈ A ] F .ICarrier x) ] (x ≤ join t)
--   α F .S≤-closed x≤y (t , ψ) = t , trans x≤y ψ
--   α F .Sclosed t = flatten t , flatten-join t

--   α-mono : ∀ {F G} → F ≤ᴾ G → α F ≤S α G
--   α-mono F≤G .*≤S* x (t , ψ) = map-Tree (F≤G .*≤ᴾ*) t , trans ψ (map-join _ t)

--   α-cong : ∀ {F G} → F ≈ᴾ G → α F ≃S α G
--   α-cong (ϕ , ψ) = α-mono ϕ , α-mono ψ

--   U : Sheaf → PreSheaf
--   U F .ICarrier  = F .SCarrier
--   U F .≤-closed = F .S≤-closed

--   U-mono : ∀ {F G} → F ≤S G → U F ≤ᴾ U G
--   U-mono F≤G .*≤ᴾ* = F≤G .*≤S*

--   U-cong : ∀ {F G} → F ≃S G → U F ≈ᴾ U G
--   U-cong (ϕ , ψ) = (U-mono ϕ) , (U-mono ψ)

--   -- We have a reflective sub order
--   counit : ∀ {F} → α (U F) ≤S F
--   counit {F} .*≤S* x (t , ψ) = F .S≤-closed ψ (F .Sclosed t)

--   counit⁻¹ : ∀ {F} → F ≤S α (U F)
--   counit⁻¹ {F} .*≤S* x ϕ = lf (x , ϕ) , refl

--   counit-≃ : ∀ {F} → F ≃S α (U F)
--   counit-≃ = counit⁻¹ , counit

--   unit : ∀ F → F ≤ᴾ U (α F)
--   unit F .*≤ᴾ* x ϕ = lf (x , ϕ) , refl

--   ------------------------------------------------------------------------------
--   -- The topology is subcanonical if _&_ is sub-idempotent.
--   module _
--       (&-idem : ∀ {x} → (x & x) ≤ x)
--     where

--     joinJ : ∀ x (t : Tree (Σ[ y ∈ A ] Lift a (y ≤ x))) → join t ≤ x
--     joinJ x (lf (y , lift y≤x)) = y≤x
--     joinJ x (br s t) = trans (&-mono (joinJ x s) (joinJ x t)) &-idem

--     ηS : A → Sheaf
--     ηS x .SCarrier y = Lift a (y ≤ x)
--     ηS x .S≤-closed x₁≤y (lift y≤x) = lift (trans x₁≤y y≤x)
--     ηS x .Sclosed t .lower = joinJ _ t

--   ------------------------------------------------------------------------------
--   -- Meets
--   _∧ᴾS_ : Sheaf → Sheaf → Sheaf
--   (F ∧ᴾS G) .SCarrier x = F .SCarrier x × G .SCarrier x
--   (F ∧ᴾS G) .S≤-closed x≤y (Fy , Gy) = (F .S≤-closed x≤y Fy) , (G .S≤-closed x≤y Gy)
--   (F ∧ᴾS G) .Sclosed t =
--     F .S≤-closed (map-join _ t) (F .Sclosed (map-Tree (λ _ → proj₁) t)) ,
--     G .S≤-closed (map-join _ t) (G .Sclosed (map-Tree (λ _ → proj₂) t))

--   ∧ᴾS-isMeet : IsMeet ≤S-isPreorder _∧ᴾS_
--   ∧ᴾS-isMeet .IsMeet.π₁ .*≤S* _ = proj₁
--   ∧ᴾS-isMeet .IsMeet.π₂ .*≤S* _ = proj₂
--   ∧ᴾS-isMeet .IsMeet.⟨_,_⟩ m₁ m₂ .*≤S* x Fx = m₁ .*≤S* x Fx , m₂ .*≤S* x Fx

-- {-
--   module _ where
--     open IsMeet ∧ᴾS-isMeet using (⟨_,_⟩)
--     open IsMeet ∧ᴾ-isMeet using (π₁; π₂)

--     -- FIXME: work out what is needed here; probably going to have to
--     -- work out how to state stability of _&_ under pullbacks.
--     preserveMeets : ∀ {F G} → α (F ∧ᴾ G) ≃S (α F ∧ᴾS α G)
--     preserveMeets .proj₁ = ⟨ (α-mono π₁) , (α-mono π₂) ⟩
--     preserveMeets .proj₂ .*≤S* = {!!} -- this would be true if _&_ distributed across meets, which we are not assuming here
-- -}

--   ------------------------------------------------------------------------------
--   -- Joins
--   _∨S_ : Sheaf → Sheaf → Sheaf
--   F ∨S G = α (U F ∨ U G)

--   inl : ∀ {F G} → F ≤S (F ∨S G)
--   inl = ≤S-trans counit⁻¹ (α-mono (∨-isJoin .IsJoin.inl))

--   inr : ∀ {F G} → G ≤S (F ∨S G)
--   inr = ≤S-trans counit⁻¹ (α-mono (∨-isJoin .IsJoin.inr))

--   [_,_]S : ∀ {F G H} → F ≤S H → G ≤S H → (F ∨S G) ≤S H
--   [_,_]S {F}{G}{H} m₁ m₂ .*≤S* x (t , x≤t) =
--     H .S≤-closed (trans x≤t (map-join _ t))
--       (H .Sclosed (map-Tree (λ x → [ m₁ .*≤S* x ⊎ m₂ .*≤S* x ]) t))

--   ∨S-isJoin : IsJoin ≤S-isPreorder _∨S_
--   ∨S-isJoin .IsJoin.inl = inl
--   ∨S-isJoin .IsJoin.inr = inr
--   ∨S-isJoin .IsJoin.[_,_] = [_,_]S

--   ------------------------------------------------------------------------------
--   -- Monoids 1 : if we have a 'medial'-type monoid, then the
--   -- presheaf monoid definition is already a sheaf. I.e., U (α (F ∙ G)) ≃ U (α F) ∙ U (α G)
--   module SMonoid1 {_∙_ : A → A → A} {ε : A}
--                   (∙-isMonoid : IsMonoid ≤-isPreorder _∙_ ε)
--                   -- this is how it interacts with the 'join'
--                   (medial : ∀ {w x y z} → ((w ∙ x) & (y ∙ z)) ≤ ((w & y) ∙ (x & z)))
--                   (tidy   : (ε & ε) ≤ ε)
--        where

--     open IsMonoid ∙-isMonoid

--     split : ∀ {F G : A → Set (a ⊔ ℓ₂)} →
--             (t : Tree (Σ[ x ∈ A ] Σ[ y ∈ A ] Σ[ z ∈ A ] (x ≤ (y ∙ z)) × F y × G z)) →
--             Σ[ t₁ ∈ Tree (Σ[ x ∈ A ] F x) ]
--             Σ[ t₂ ∈ Tree (Σ[ x ∈ A ] G x) ]
--               (join t ≤ (join t₁ ∙ join t₂))
--     split (lf (x , y , z , x≤yz , Fy , Gz)) = lf (y , Fy) , lf (z , Gz) , x≤yz
--     split (br s t) =
--       let s₁ , s₂ , s≤s₁s₂ = split s
--           t₁ , t₂ , t≤t₁t₂ = split t
--       in
--       br s₁ t₁ , br s₂ t₂ , trans (&-mono s≤s₁s₂ t≤t₁t₂) medial

--     _▷_ : Sheaf → Sheaf → Sheaf
--     (F ▷ G) .SCarrier x =
--       Σ[ y ∈ A ] Σ[ z ∈ A ] (x ≤ (y ∙ z) × F .SCarrier y × G .SCarrier z)
--     (F ▷ G) .S≤-closed x≤x' (y , z , x'≤yz , Fy , Gz) =
--       y , z , trans x≤x' x'≤yz , Fy , Gz
--     (F ▷ G) .Sclosed t =
--       let ft , gt , t≤fg = split t in
--       join ft , join gt , t≤fg , F .Sclosed ft , G .Sclosed gt

--     -- FIXME: this is the same as 'tidyup' in 'bv.agda', and is a
--     -- special case of joinJ above.
--     collapse : (t : Tree (Σ[ x ∈ A ] Lift a (x ≤ ε))) → join t ≤ ε
--     collapse (lf (x , lift x≤ε)) = x≤ε
--     collapse (br s t) = trans (&-mono (collapse s) (collapse t)) tidy

--     I : Sheaf
--     I .SCarrier x = Lift a (x ≤ ε)
--     I .S≤-closed x≤y (lift y≤ε) = lift (trans x≤y y≤ε)
--     I .Sclosed t = lift (collapse t)

--     -- Associativity etc. are now the same as before, because the
--     -- carrier is the same
--     open Monoid ∙-isMonoid renaming (I to J)

--     ▷-mono : ∀ {F₁ G₁ F₂ G₂} → F₁ ≤S F₂ → G₁ ≤S G₂ → (F₁ ▷ G₁) ≤S (F₂ ▷ G₂)
--     ▷-mono {F₁}{G₁}{F₂}{G₂} m₁ m₂ .*≤S* =
--       ∙-mono {U F₁}{U G₁}{U F₂}{U G₂}
--         (record { *≤ᴾ* = m₁ .*≤S* }) (record { *≤ᴾ* = m₂ .*≤S* }) .*≤ᴾ*

--     ▷-assoc : ∀ {F G H} → ((F ▷ G) ▷ H) ≃S (F ▷ (G ▷ H))
--     ▷-assoc {F}{G}{H} .proj₁ .*≤S* = ∙-assoc {U F}{U G}{U H} .proj₁ .*≤ᴾ*
--     ▷-assoc {F}{G}{H} .proj₂ .*≤S* = ∙-assoc {U F}{U G}{U H} .proj₂ .*≤ᴾ*

--     ▷-lunit : ∀ {F} → (I ▷ F) ≃S F
--     ▷-lunit {F} .proj₁ .*≤S* = ∙-lunit {U F} .proj₁ .*≤ᴾ*
--     ▷-lunit {F} .proj₂ .*≤S* = ∙-lunit {U F} .proj₂ .*≤ᴾ*

--     ▷-runit : ∀ {F} → (F ▷ I) ≃S F
--     ▷-runit {F} .proj₁ .*≤S* = ∙-runit {U F} .proj₁ .*≤ᴾ*
--     ▷-runit {F} .proj₂ .*≤S* = ∙-runit {U F} .proj₂ .*≤ᴾ*

--     ▷-isMonoid : IsMonoid ≤S-isPreorder _▷_ I
--     ▷-isMonoid .IsMonoid.mono m₁ m₂ .*≤S* = ∙-mono (U-mono m₁) (U-mono m₂) .*≤ᴾ*
--     ▷-isMonoid .IsMonoid.assoc = ▷-assoc
--     ▷-isMonoid .IsMonoid.lunit = ▷-lunit
--     ▷-isMonoid .IsMonoid.runit = ▷-runit

--     U-monoidal : ∀ {F G} → U (F ▷ G) ≈ᴾ (U F ∙ U G)
--     U-monoidal .proj₁ .*≤ᴾ* x ϕ = ϕ
--     U-monoidal .proj₂ .*≤ᴾ* x ϕ = ϕ

--   -- A commutative monoid that distributes over the 'join' also
--   -- gives a monoid on sheaves.
--   module SMonoid2 {_∙_ : A → A → A} {ε : A}
--                   (∙-isMonoid : IsMonoid ≤-isPreorder _∙_ ε)
--                   (∙-sym : ∀ {x y} → (x ∙ y) ≤ (y ∙ x))
--                   (∙-&-distrib : ∀ {x y z} → ((x & y) ∙ z) ≤ ((x ∙ z) & (y ∙ z)))
--                  where

--     open IsMonoid ∙-isMonoid
--     open Monoid ∙-isMonoid renaming (I to J)

--     _⊗_ : Sheaf → Sheaf → Sheaf
--     F ⊗ G = α (U F ∙ U G)

--     I : Sheaf
--     I = α J

--     -- α is strong monoidal from PreSheaf to Sheaf
--     module _ {F G : PreSheaf} where
--        mul : Tree (Σ[ x ∈ A ] F .ICarrier x) →
--              Tree (Σ[ x ∈ A ] G .ICarrier x) →
--              Tree (Σ[ x ∈ A ] (F ∙ G) .ICarrier x)
--        mul (lf (x , Fx)) (lf (y , Gy)) = lf (x ∙ y , x , y , refl , Fx , Gy)
--        mul (lf x)        (br t₁ t₂)    = br (mul (lf x) t₁) (mul (lf x) t₂)
--        mul (br s₁ s₂)    t             = br (mul s₁ t) (mul s₂ t)

--        mul-join : (t₁ : Tree (Σ[ x ∈ A ] F .ICarrier x)) →
--                   (t₂ : Tree (Σ[ x ∈ A ] G .ICarrier x)) →
--                   (join t₁ ∙ join t₂) ≤ join (mul t₁ t₂)
--        mul-join (lf x) (lf x₁) = refl
--        mul-join (lf x) (br t₂ t₃) =
--          trans ∙-sym
--          (trans ∙-&-distrib
--          (&-mono (trans ∙-sym (mul-join (lf x) t₂))
--                  (trans ∙-sym (mul-join (lf x) t₃))))
--        mul-join (br s₁ s₂) t =
--          trans ∙-&-distrib (&-mono (mul-join s₁ t) (mul-join s₂ t))

--        -- The 2nd and 3rd arguments are unpacked to satisfy the termination checker
--        -- FIXME: this is essentially a map-and-join operation that preserves the first components
--        lemma : ∀ x
--                (t : Tree (Σ[ y ∈ A ] (U (α F) ∙ U (α G)) .ICarrier y)) →
--                x ≤ join t →
--                Σ[ t ∈ Tree (Σ[ x ∈ A ] ((F ∙ G) .ICarrier x)) ] (x ≤ join t)
--        lemma x (lf (y , (y₁ , y₂ , y≤y₁y₂ , (t₁ , y₁≤t₁) , (t₂ , y₂≤t₂)))) x≤y =
--          (mul t₁ t₂) , trans x≤y (trans y≤y₁y₂ (trans (mono y₁≤t₁ y₂≤t₂) (mul-join t₁ t₂)))
--        lemma x (br s t) x≤s&t =
--          let (t₁ , ϕ₁) = lemma (join s) s refl
--              (t₂ , ϕ₂) = lemma (join t) t refl
--          in br t₁ t₂ , trans x≤s&t (&-mono ϕ₁ ϕ₂)

--        α-monoidal : (α F ⊗ α G) ≃S α (F ∙ G)
--        α-monoidal .proj₁ .*≤S* x (t , x≤t) = lemma x t x≤t
--        α-monoidal .proj₂ = α-mono (∙-mono (unit F) (unit G))

--     module _ where
--       open IsMonoid ∙-isMonoid renaming (cong to ∙-cong)
--       open Setoid (IsPreorder.≃-setoid ≤ᴾ-isPreorder) renaming (refl to P-refl)

--       ⊗-mono : ∀ {F₁ G₁ F₂ G₂} → F₁ ≤S F₂ → G₁ ≤S G₂ → (F₁ ⊗ G₁) ≤S (F₂ ⊗ G₂)
--       ⊗-mono m₁ m₂ = α-mono (∙-mono (U-mono m₁) (U-mono m₂))

--       ⊗-assoc : ∀ {F G H} → ((F ⊗ G) ⊗ H) ≃S (F ⊗ (G ⊗ H))
--       ⊗-assoc {F}{G}{H} = begin
--           ((F ⊗ G) ⊗ H)
--         ≡⟨⟩
--           α (U (α (U F ∙ U G)) ∙ U H)
--         ≈⟨ α-cong (∙-cong P-refl (U-cong counit-≃)) ⟩
--           α (U (α (U F ∙ U G)) ∙ U (α (U H)))
--         ≈⟨ α-monoidal ⟩
--           α ((U F ∙ U G) ∙ U H)
--         ≈⟨ α-cong ∙-assoc ⟩
--           α (U F ∙ (U G ∙ U H))
--         ≈˘⟨ α-monoidal ⟩
--           α (U (α (U F)) ∙ U (α (U G ∙ U H)))
--         ≈˘⟨ α-cong (∙-cong (U-cong counit-≃) P-refl) ⟩
--           (F ⊗ (G ⊗ H))
--         ∎
--         where open IsPreorder.≃-SetoidReasoning ≤S-isPreorder

--       ⊗-lunit : ∀ {F} → (I ⊗ F) ≃S F
--       ⊗-lunit {F} = begin
--             I ⊗ F
--           ≡⟨⟩
--             α (U (α J) ∙ U F)
--           ≈⟨ α-cong (∙-cong P-refl (U-cong counit-≃)) ⟩
--             α (U (α J) ∙ U (α (U F)))
--           ≈⟨ α-monoidal ⟩
--             α (J ∙ U F)
--           ≈⟨ α-cong ∙-lunit ⟩
--             α (U F)
--           ≈˘⟨ counit-≃ ⟩
--             F
--           ∎
--           where open IsPreorder.≃-SetoidReasoning ≤S-isPreorder

--       ⊗-runit : ∀ {F} → (F ⊗ I) ≃S F
--       ⊗-runit {F} = begin
--             F ⊗ I
--           ≡⟨⟩
--             α (U F ∙ U (α J))
--           ≈⟨ α-cong (∙-cong (U-cong counit-≃) P-refl) ⟩
--             α (U (α (U F)) ∙ U (α J))
--           ≈⟨ α-monoidal ⟩
--             α (U F ∙ J)
--           ≈⟨ α-cong ∙-runit ⟩
--             α (U F)
--           ≈˘⟨ counit-≃ ⟩
--             F
--           ∎
--           where open IsPreorder.≃-SetoidReasoning ≤S-isPreorder

--     ⊗-isMonoid : IsMonoid ≤S-isPreorder _⊗_ I
--     ⊗-isMonoid .IsMonoid.mono = ⊗-mono
--     ⊗-isMonoid .IsMonoid.assoc = ⊗-assoc
--     ⊗-isMonoid .IsMonoid.lunit = ⊗-lunit
--     ⊗-isMonoid .IsMonoid.runit = ⊗-runit

--     ⊗-sym : ∀ {F G} → (F ⊗ G) ≤S (G ⊗ F)
--     ⊗-sym {F}{G} = α-mono (∙-sym ∙-sym {U F} {U G})

--     -- Residuals are automatically closed, relying on distributivity.
--     -- Is this deducible from strong monoidality of α?
--     ⊸-lemma : ∀ F G →
--               (t : Tree (Σ[ x ∈ A ] (∀ y → F .SCarrier y → G .SCarrier (x ∙ y)))) →
--               (y : A) → F .SCarrier y →
--               Σ[ t' ∈ Tree (Σ[ x ∈ A ] (G .SCarrier x)) ] (join t ∙ y) ≤ join t'
--     ⊸-lemma F G (lf (x , f)) y Fy = (lf (x ∙ y , f y Fy)) , refl
--     ⊸-lemma F G (br s t)     y Fy =
--       let (s' , sy≤s') = ⊸-lemma F G s y Fy
--           (t' , ty≤t') = ⊸-lemma F G t y Fy
--       in br s' t' , trans ∙-&-distrib (&-mono sy≤s' ty≤t')

--     _⊸_ : Sheaf → Sheaf → Sheaf
--     (F ⊸ G) .SCarrier x = ∀ y → F .SCarrier y → G .SCarrier (x ∙ y)
--     (F ⊸ G) .S≤-closed x≤x' f y Fy = G .S≤-closed (mono x≤x' refl) (f y Fy)
--     (F ⊸ G) .Sclosed t y Fy =
--       let t' , ty≤y' = ⊸-lemma F G t y Fy in
--       G .S≤-closed ty≤y' (G .Sclosed t')

--     U⊸ : ∀ {F G} → U (F ⊸ G) ≤ᴾ (U F -∙ U G)
--     U⊸ .*≤ᴾ* x f = f

--     ⊸-isClosure : IsClosure ≤S-isPreorder ⊗-isMonoid _⊸_
--     ⊸-isClosure .IsClosure.lambda {F}{G}{H} m .*≤S* x Fx y Gy =
--       -- FIXME: find a more abstract way of doing this
--       m .*≤S* (x ∙ y) ((lf (x ∙ y , x , y , refl , Fx , Gy)) , refl)
--     ⊸-isClosure .IsClosure.eval =
--        ≤S-trans (α-mono (∙-mono U⊸ (≤ᴾ-isPreorder .IsPreorder.refl)))
--        (≤S-trans (α-mono (-∙-isClosure .IsClosure.eval)) counit)

--   module SDuoidal {_∙_ : A → A → A} {_⍮_ : A → A → A} {ε : A}
--                   (∙-isMonoid : IsMonoid ≤-isPreorder _∙_ ε)
--                   (∙-sym : ∀ {x y} → (x ∙ y) ≤ (y ∙ x))
--                   (∙-&-distrib : ∀ {x y z} → ((x & y) ∙ z) ≤ ((x ∙ z) & (y ∙ z)))
--                   (⍮-isMonoid : IsMonoid ≤-isPreorder _⍮_ ε)
--                   (medial : ∀ {w x y z} → ((w ⍮ x) & (y ⍮ z)) ≤ ((w & y) ⍮ (x & z)))
--                   (tidy   : (ε & ε) ≤ ε)
--                   (∙-⍮-isDuoidal : IsDuoidal ≤-isPreorder ∙-isMonoid ⍮-isMonoid)
--               where

--     open Monoid ∙-isMonoid renaming (_∙_ to _⊛_; ∙-mono to ⊛-mono)
--     open Monoid ⍮-isMonoid renaming (_∙_ to _,-_; ∙-mono to ,--mono)
--     open SMonoid1 ⍮-isMonoid medial tidy renaming (I to J)
--     open SMonoid2 ∙-isMonoid ∙-sym ∙-&-distrib renaming (I to I⊗)

--     open Duoidal ∙-isMonoid ⍮-isMonoid ∙-⍮-isDuoidal

--     units-iso : I⊗ ≃S J
--     units-iso .proj₁ .*≤S* x (t , x≤t) = J .S≤-closed x≤t (J .Sclosed t)
--     units-iso .proj₂ .*≤S* x x≤I = lf (x , x≤I) , refl

--     _>>_ = ≤S-trans

--     ⊗-▷-isDuoidal : IsDuoidal ≤S-isPreorder ⊗-isMonoid ▷-isMonoid
--     ⊗-▷-isDuoidal .IsDuoidal.exchange =
--       α-mono (⊛-mono (U-monoidal .proj₁) (U-monoidal .proj₁)) >>
--       (α-mono ∙-⍮-exchange >>
--       (α-mono (,--mono (unit _) (unit _)) >>
--       (α-mono (U-monoidal .proj₂)
--       >> counit)))
--       --   (w ▷ x) ⊗ (y ▷ z)
--       -- ≡ α (U (w ▷ x) ∙ U(y ▷ z))
--       -- ≃ α ((U w ⍮ U x) ∙ (U y ⍮ U z))
--       -- ≤ α ((U w ∙ U y) ⍮ (U x ∙ U z))
--       -- ≤ α (U (α (U w ∙ U y)) ⍮ U (α (U x ∙ U z)))
--       -- ≃ α (U ((w ⊗ y) ▷ (x ⊗ z))
--       -- ≡ (w ⊗ y) ▷ (x ⊗ z)
--     ⊗-▷-isDuoidal .IsDuoidal.mu = ⊗-mono (units-iso .proj₂) ≤S-refl >> ⊗-lunit .proj₁
   