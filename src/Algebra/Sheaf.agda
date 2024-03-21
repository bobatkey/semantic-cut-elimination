{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level
open import Algebra
open import Algebra.Definitions
open import Algebra.Ordered
open import Algebra.Ordered.Definitions
open import Algebra.Ordered.Consequences
open import Algebra.Ordered.Structures.Residuated
open import Algebra.Ordered.Structures.Duoidal
open import Function using (const; flip)
open import Data.Product using (_×_; _,_; -,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; <_,_>)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit using (⊤; tt)
open import Relation.Binary
open import Relation.Binary.Construct.Core.Symmetric as SymCore using (SymCore)
open import Relation.Binary.Lattice
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
import Relation.Binary.Construct.Flip.EqAndOrd as Flip
open import Relation.Unary using (Pred; _⊆_)
import Relation.Binary.Reasoning.PartialOrder as PosetReasoning
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- FIXME: not sheaves! we do not necessarily know that α : PreSheaf →
-- Sheaf defined below preserves finite limits. This is an extra
-- property that would turn it into a preorder Grothendieck topos. I
-- guess that this would need _∨_ to distribute over meets in A (if we
-- assume that A has meets)?
--
-- Alternatively, the closure of the closure operation
--
--     C X x = Σ[ t ∈ Tree (Σ[ x ∈ A ] X .ICarrier x) ] x ≤ ⋁ᵗ t

module Algebra.Sheaf {c ℓ₁ ℓ₂} (pomagma : Pomagma c ℓ₁ ℓ₂) where

open Pomagma pomagma
  using
    ( Carrier
    ; _≈_
    ; _≤_
    ; poset
    )
  renaming
    ( _∙_        to _∨_
    ; mono       to ∨-mono
    ; monoˡ      to ∨-monoˡ
    ; monoʳ      to ∨-monoʳ
    ; refl       to ≤-refl
    ; trans      to ≤-trans
    )

open import Algebra.PreSheaf poset as P
  using
    ( PreSheaf
    ; ICarrier
    ; ≤-closed
    ; _≤ᵖ_
    ; *≤ᵖ*
    ; ≤ᵖ-refl
    ; ≤ᵖ-trans
    ; _≈ᵖ_
    ; _∨ᵖ_
    ; inj₁ᵖ
    ; inj₂ᵖ
    )

private
  variable
    w x y z : Carrier
    ℓx ℓy ℓz : Level
    X : Pred Carrier ℓx
    Y : Pred Carrier ℓy
    Z : Pred Carrier ℓz
    F F₁ F₂ : PreSheaf
    G G₁ G₂ : PreSheaf
    H H₁ H₂ : PreSheaf

data Tree {a} (A : Set a) : Set a where
  leaf : A → Tree A
  node : Tree A → Tree A → Tree A

∃ᵗ : ∀ {ℓ} (X : Pred Carrier ℓ) → Set (c ⊔ ℓ)
∃ᵗ X = Tree (∃ X)

infix 2 ∃ᵗ-syntax

∃ᵗ-syntax : ∀ {ℓ} (X : Pred Carrier ℓ) → Set (c ⊔ ℓ)
∃ᵗ-syntax = ∃ᵗ

syntax ∃ᵗ-syntax (λ x → B) = ∃ᵗ[ x ] B

∃ᵗᵖ : PreSheaf → Set (c ⊔ ℓ₂)
∃ᵗᵖ F = ∃ᵗ[ x ] (F .ICarrier x)

mapᵗ : (f : X ⊆ Y) → ∃ᵗ X → ∃ᵗ Y
mapᵗ f (leaf (x , Xx)) = leaf (x , f Xx)
mapᵗ f (node l r)      = node (mapᵗ f l) (mapᵗ f r)

⋁ᵗ : ∃ᵗ X → Carrier
⋁ᵗ (leaf (x , _)) = x
⋁ᵗ (node l r)     = ⋁ᵗ l ∨ ⋁ᵗ r

mapᵗ-⋁ᵗ : {f : X ⊆ Y} (t : ∃ᵗ X) → ⋁ᵗ t ≤ ⋁ᵗ (mapᵗ f t)
mapᵗ-⋁ᵗ (leaf _)   = ≤-refl
mapᵗ-⋁ᵗ (node l r) = ∨-mono (mapᵗ-⋁ᵗ l) (mapᵗ-⋁ᵗ r)

joinᵗ : ∃ᵗ[ x ] (Σ[ t ∈ ∃ᵗ X ] x ≤ ⋁ᵗ t) → ∃ᵗ X
joinᵗ (leaf (x , t , ϕ)) = t
joinᵗ (node l r)         = node (joinᵗ l) (joinᵗ r)

joinᵗ-⋁ᵗ : (t : ∃ᵗ[ x ] Σ[ t ∈ ∃ᵗ X ] (x ≤ ⋁ᵗ t)) → ⋁ᵗ t ≤ ⋁ᵗ (joinᵗ t)
joinᵗ-⋁ᵗ (leaf (x , t , x≤⋁t)) = x≤⋁t
joinᵗ-⋁ᵗ (node l r) = ∨-mono (joinᵗ-⋁ᵗ l) (joinᵗ-⋁ᵗ r)

record Sheaf : Set (suc (c ⊔ ℓ₂)) where
  no-eta-equality
  field
    ICarrier : Carrier → Set (c ⊔ ℓ₂)
    ≤-closed : x ≤ y → ICarrier y → ICarrier x
    ∨-closed : (t : ∃ᵗ ICarrier) → ICarrier (⋁ᵗ t)
open Sheaf

private
  variable
    𝓕 𝓕₁ 𝓕₂ : Sheaf
    𝓖 𝓖₁ 𝓖₂ : Sheaf
    𝓗 𝓗₁ 𝓗₂ : Sheaf

infix 4 _≤ˢ_

record _≤ˢ_ (𝓕 𝓖 : Sheaf) : Set (c ⊔ ℓ₂) where
  no-eta-equality
  field
    *≤ˢ* : 𝓕 .ICarrier ⊆ 𝓖 .ICarrier
open _≤ˢ_

∃ᵗˢ : Sheaf → Set (c ⊔ ℓ₂)
∃ᵗˢ 𝓕 = ∃ᵗ[ x ] (𝓕 .ICarrier x)

infix 4 _≥ˢ_

_≥ˢ_ : Sheaf → Sheaf → Set (c ⊔ ℓ₂)
_≥ˢ_ = flip _≤ˢ_

infix 4 _≈ˢ_

_≈ˢ_ : Sheaf → Sheaf → Set (c ⊔ ℓ₂)
_≈ˢ_ = SymCore _≤ˢ_

≤ˢ-refl : 𝓕 ≤ˢ 𝓕
≤ˢ-refl .*≤ˢ* 𝓕x = 𝓕x

≤ˢ-trans : 𝓕 ≤ˢ 𝓖 → 𝓖 ≤ˢ 𝓗 → 𝓕 ≤ˢ 𝓗
≤ˢ-trans 𝓕≤𝓖 𝓖≤𝓗 .*≤ˢ* z = 𝓖≤𝓗 .*≤ˢ* (𝓕≤𝓖 .*≤ˢ* z)

≤ˢ-isPartialOrder : IsPartialOrder _≈ˢ_ _≤ˢ_
≤ˢ-isPartialOrder = SymCore.isPreorder⇒isPartialOrder _≤ˢ_ ≡-≤ˢ-isPreorder
  where
    ≡-≤ˢ-isPreorder : IsPreorder _≡_ _≤ˢ_
    ≡-≤ˢ-isPreorder = record
      { isEquivalence = PropEq.isEquivalence
      ; reflexive = λ { PropEq.refl → ≤ˢ-refl }
      ; trans = ≤ˢ-trans
      }

open IsPartialOrder ≤ˢ-isPartialOrder
  using
    (
    )
  renaming
    ( ≤-respˡ-≈  to ≤ˢ-respˡ-≈ˢ
    ; isPreorder to ≤ˢ-isPreorder
    )

≤ˢ-poset : Poset _ _ _
≤ˢ-poset = record
  { isPartialOrder = ≤ˢ-isPartialOrder
  }

≈ˢ-setoid : Setoid _ _
≈ˢ-setoid = record
  { isEquivalence = Poset.isEquivalence ≤ˢ-poset
  }

------------------------------------------------------------------------------
-- Turn a presheaf into a sheaf by closing under imaginary ⋁ᵗs

α : PreSheaf → Sheaf
α F .ICarrier x = Σ[ t ∈ ∃ᵗᵖ F ] (x ≤ ⋁ᵗ t)
α F .≤-closed x≤y (t , y≤⋁t) = t , ≤-trans x≤y y≤⋁t
α F .∨-closed t = joinᵗ t , joinᵗ-⋁ᵗ t

α-mono : F ≤ᵖ G → α F ≤ˢ α G
α-mono F≤G .*≤ˢ* (t , x≤⋁t) = (mapᵗ (F≤G .*≤ᵖ*) t , ≤-trans x≤⋁t (mapᵗ-⋁ᵗ t))

α-cong : ∀ {F G} → F ≈ᵖ G → α F ≈ˢ α G
α-cong (G≤F , F≤G) = (α-mono G≤F , α-mono F≤G)

------------------------------------------------------------------------------
-- Turn a sheaf into a presheaf

U : Sheaf → PreSheaf
U F .ICarrier = F .ICarrier
U F .≤-closed = F .≤-closed

U-mono : 𝓕 ≤ˢ 𝓖 → U 𝓕 ≤ᵖ U 𝓖
U-mono 𝓕≤𝓖 .*≤ᵖ* = 𝓕≤𝓖 .*≤ˢ*

U-cong : 𝓕 ≈ˢ 𝓖 → U 𝓕 ≈ᵖ U 𝓖
U-cong (𝓖≤𝓕 , 𝓕≤𝓖) = (U-mono 𝓖≤𝓕 , U-mono 𝓕≤𝓖)

-- We have a reflective sub order
counit : α (U 𝓕) ≤ˢ 𝓕
counit {𝓕} .*≤ˢ* (t , x≤⋁t) = 𝓕 .≤-closed x≤⋁t (𝓕 .∨-closed t)

counit⁻¹ : 𝓕 ≤ˢ α (U 𝓕)
counit⁻¹ .*≤ˢ* 𝓕x = (leaf (_ , 𝓕x) , ≤-refl)

counit-≈ˢ : 𝓕 ≈ˢ α (U 𝓕)
counit-≈ˢ = (counit⁻¹ , counit)

unit : F ≤ᵖ U (α F)
unit .*≤ᵖ* Fx = (leaf (-, Fx) , ≤-refl)

------------------------------------------------------------------------------
-- Construct a meet semilattice for presheaves

_∧ˢ_ : Sheaf → Sheaf → Sheaf
(𝓕 ∧ˢ 𝓖) .ICarrier x = 𝓕 .ICarrier x × 𝓖 .ICarrier x
(𝓕 ∧ˢ 𝓖) .≤-closed x≤y (𝓕y , 𝓖y) = (𝓕 .≤-closed x≤y 𝓕y) , (𝓖 .≤-closed x≤y 𝓖y)
(𝓕 ∧ˢ 𝓖) .∨-closed t =
  𝓕 .≤-closed (mapᵗ-⋁ᵗ t) (𝓕 .∨-closed (mapᵗ proj₁ t)) ,
  𝓖 .≤-closed (mapᵗ-⋁ᵗ t) (𝓖 .∨-closed (mapᵗ proj₂ t))

proj₁ˢ : (𝓕 ∧ˢ 𝓖) ≤ˢ 𝓕
proj₁ˢ .*≤ˢ* = proj₁

proj₂ˢ : (𝓕 ∧ˢ 𝓖) ≤ˢ 𝓖
proj₂ˢ .*≤ˢ* = proj₂

⟨_,_⟩ˢ : 𝓕 ≤ˢ 𝓖 → 𝓕 ≤ˢ 𝓗 → 𝓕 ≤ˢ (𝓖 ∧ˢ 𝓗)
⟨ 𝓗≤𝓕 , 𝓗≤𝓖 ⟩ˢ .*≤ˢ* = < 𝓗≤𝓕 .*≤ˢ* , 𝓗≤𝓖 .*≤ˢ* >

∧ˢ-isMeetSemilattice : IsMeetSemilattice _≈ˢ_ _≤ˢ_ _∧ˢ_
∧ˢ-isMeetSemilattice = record
  { isPartialOrder = ≤ˢ-isPartialOrder
  ; infimum        = λ 𝓕 𝓖 → (proj₁ˢ ,  proj₂ˢ , λ 𝓗 → ⟨_,_⟩ˢ)
  }

-- -- FIXME: work out what is needed here; probably going to have to
-- -- work out how to state stability of _∨_ under pullbacks.
-- preserveMeets : ∀ {F G} → α (F ∧ᵖ G) ≈ˢ (α F ∧ᵖS α G)
-- preserveMeets .proj₁ = ⟨ (α-mono proj₁ˢ) , (α-mono proj₂ˢ) ⟩
-- preserveMeets .proj₂ .*≤ˢ* = {!!} -- this would be true if _∨_ distributed across meets, which we are not assuming here

------------------------------------------------------------------------------
-- Construct a joinᵗ semilattice for presheaves

_∨ˢ_ : Sheaf → Sheaf → Sheaf
𝓕 ∨ˢ 𝓖 = α (U 𝓕 ∨ᵖ U 𝓖)

inj₁ˢ : 𝓕 ≤ˢ (𝓕 ∨ˢ 𝓖)
inj₁ˢ = ≤ˢ-trans counit⁻¹ (α-mono inj₁ᵖ)

inj₂ˢ : 𝓖 ≤ˢ (𝓕 ∨ˢ 𝓖)
inj₂ˢ = ≤ˢ-trans counit⁻¹ (α-mono inj₂ᵖ)

[_,_]ˢ : 𝓕 ≤ˢ 𝓗 → 𝓖 ≤ˢ 𝓗 → (𝓕 ∨ˢ 𝓖) ≤ˢ 𝓗
[_,_]ˢ {𝓕} {𝓗} {𝓖} 𝓕≤𝓗 𝓖≤𝓗 .*≤ˢ* (t , x≤t) =
  𝓗 .≤-closed (≤-trans x≤t (mapᵗ-⋁ᵗ t))
    (𝓗 .∨-closed (mapᵗ [ 𝓕≤𝓗 .*≤ˢ* , 𝓖≤𝓗 .*≤ˢ* ] t))

∨ˢ-isJoinSemilattice : IsJoinSemilattice _≈ˢ_ _≤ˢ_ _∨ˢ_
∨ˢ-isJoinSemilattice = record
  { isPartialOrder = ≤ˢ-isPartialOrder
  ; supremum       = λ 𝓕 𝓖 → (inj₁ˢ , inj₂ˢ , λ 𝓗 → [_,_]ˢ)
  }

------------------------------------------------------------------------------
-- The topology is subcanonical if _∨_ is sub-idempotent.

module LiftSubidempotent (∨-idem : Subidempotent _≤_ _∨_) where

  ⋁ˢ : ∀ x → (t : ∃ᵗ[ y ] Lift c (y ≤ x)) → ⋁ᵗ t ≤ x
  ⋁ˢ x (leaf (y , lift y≤x)) = y≤x
  ⋁ˢ x (node l r)            = ≤-trans (∨-mono (⋁ˢ x l) (⋁ˢ x r)) (∨-idem _)

  ηˢ : Carrier → Sheaf
  ηˢ x .ICarrier y              = Lift c (y ≤ x)
  ηˢ x .≤-closed z≤y (lift y≤x) = lift (≤-trans z≤y y≤x)
  ηˢ x .∨-closed t .lower       = ⋁ˢ _ t

------------------------------------------------------------------------------
-- Lift entropic pomonoids to presheaves
--
-- If we have an entropic monoid, then the presheaf monoid is already a sheaf:
--
--   U (α (F ∙ᵖ G)) ≈ᵖ U (α F) ∙ᵖ U (α G)
--
module LiftIsPomonoid
    {_∙_} {ε}
    (isPomonoid : IsPomonoid _≈_ _≤_ _∙_ ε)
    (∨-entropy : Entropy _≤_ _∨_ _∙_)
    (∨-tidy    : ε ∨ ε ≤ ε)
  where

    ⋁ˢ : (t : ∃ᵗ[ y ] Lift c (y ≤ ε)) → ⋁ᵗ t ≤ ε
    ⋁ˢ (leaf (y , lift y≤x)) = y≤x
    ⋁ˢ (node l r)            = ≤-trans (∨-mono (⋁ˢ l) (⋁ˢ r)) ∨-tidy

    split : (t : ∃ᵗ[ x ] ∃[ y ] ∃[ z ] (x ≤ (y ∙ z)) × Y y × Z z) →
            Σ[ t₁ ∈ ∃ᵗ Y ] Σ[ t₂ ∈ ∃ᵗ Z ] (⋁ᵗ t ≤ (⋁ᵗ t₁ ∙ ⋁ᵗ t₂))
    split (leaf (x , y , z , x≤yz , Fy , Gz)) =
      (leaf (-, Fy) , leaf (-, Gz) , x≤yz)
    split (node l r) =
      let (l₁ , l₂ , l≤l₁l₂) , (r₁ , r₂ , r≤r₁r₂) = split l , split r
      in  (node l₁ r₁ , node l₂ r₂ , ≤-trans (∨-mono l≤l₁l₂ r≤r₁r₂) (∨-entropy _ _ _ _))

    _▷ˢ_ : Sheaf → Sheaf → Sheaf
    (𝓕 ▷ˢ 𝓖) .ICarrier x =
      ∃[ y ] ∃[ z ] (x ≤ (y ∙ z) × 𝓕 .ICarrier y × 𝓖 .ICarrier z)
    (𝓕 ▷ˢ 𝓖) .≤-closed x≤w (y , z , w≤yz , 𝓕y , 𝓖z) =
      (-, -, ≤-trans x≤w w≤yz , 𝓕y , 𝓖z)
    (𝓕 ▷ˢ 𝓖) .∨-closed t =
      let (t𝓕 , t𝓖 , ⋁t≤⋁t𝓕∙⋁t𝓖) = split t
      in  (⋁ᵗ t𝓕 , ⋁ᵗ t𝓖 , ⋁t≤⋁t𝓕∙⋁t𝓖 , 𝓕 .∨-closed t𝓕 , 𝓖 .∨-closed t𝓖)

    ιˢ : Sheaf
    ιˢ .ICarrier x              = Lift c (x ≤ ε)
    ιˢ .≤-closed x≤y (lift y≤ε) = lift (≤-trans x≤y y≤ε)
    ιˢ .∨-closed t              = lift (⋁ˢ t)

    open P.LiftIsPomonoid isPomonoid

    ▷ˢ-mono : Monotonic₂ _≤ˢ_ _≤ˢ_ _≤ˢ_ _▷ˢ_
    ▷ˢ-mono 𝓕₁≤𝓖₁ 𝓕₂≤𝓖₂ .*≤ˢ* = ∙ᵖ-mono (U-mono 𝓕₁≤𝓖₁) (U-mono 𝓕₂≤𝓖₂) .*≤ᵖ*

    ▷ˢ-assoc : Associative _≈ˢ_ _▷ˢ_
    ▷ˢ-assoc 𝓕 𝓖 𝓗 .proj₁ .*≤ˢ* = ∙ᵖ-assoc (U 𝓕) (U 𝓖) (U 𝓗) .proj₁ .*≤ᵖ*
    ▷ˢ-assoc 𝓕 𝓖 𝓗 .proj₂ .*≤ˢ* = ∙ᵖ-assoc (U 𝓕) (U 𝓖) (U 𝓗) .proj₂ .*≤ᵖ*

    ▷ˢ-identityˡ : LeftIdentity _≈ˢ_ ιˢ _▷ˢ_
    ▷ˢ-identityˡ 𝓕 .proj₁ .*≤ˢ* = ∙ᵖ-identityˡ (U 𝓕) .proj₁ .*≤ᵖ*
    ▷ˢ-identityˡ 𝓕 .proj₂ .*≤ˢ* = ∙ᵖ-identityˡ (U 𝓕) .proj₂ .*≤ᵖ*

    ▷ˢ-identityʳ : RightIdentity _≈ˢ_ ιˢ _▷ˢ_
    ▷ˢ-identityʳ 𝓕 .proj₁ .*≤ˢ* = ∙ᵖ-identityʳ (U 𝓕) .proj₁ .*≤ᵖ*
    ▷ˢ-identityʳ 𝓕 .proj₂ .*≤ˢ* = ∙ᵖ-identityʳ (U 𝓕) .proj₂ .*≤ᵖ*

    ▷ˢ-identity : Identity _≈ˢ_ ιˢ _▷ˢ_
    ▷ˢ-identity = (▷ˢ-identityˡ , ▷ˢ-identityʳ)

    ▷ˢ-isPomonoid : IsPomonoid _≈ˢ_ _≤ˢ_ _▷ˢ_ ιˢ
    ▷ˢ-isPomonoid = record
      { isPosemigroup = record
        { isPomagma = record
          { isPartialOrder = ≤ˢ-isPartialOrder
          ; mono = ▷ˢ-mono
          }
        ; assoc = ▷ˢ-assoc
        }
      ; identity = ▷ˢ-identity
      }

    U-monoidal : U (𝓕 ▷ˢ 𝓖) ≈ᵖ (U 𝓕 ∙ᵖ U 𝓖)
    U-monoidal .proj₁ .*≤ᵖ* 𝓕x = 𝓕x
    U-monoidal .proj₂ .*≤ᵖ* 𝓕x = 𝓕x

    U-monoidal-ι : U ιˢ ≈ᵖ εᵖ
    U-monoidal-ι .proj₁ .*≤ᵖ* x≤ε = x≤ε
    U-monoidal-ι .proj₂ .*≤ᵖ* x≤ε = x≤ε

------------------------------------------------------------------------------
-- Lift commutative pomonoids that distribute with the join to presheaves
module LiftIsCommutativePomonoid
    {_∙_} {ε}
    (isCommutativePomonoid : IsCommutativePomonoid _≈_ _≤_ _∙_ ε)
    (distrib : _DistributesOver_ _≤_ _∙_ _∨_)
  where

  open IsCommutativePomonoid isCommutativePomonoid
  open P.LiftIsCommutativePomonoid isCommutativePomonoid

  distribˡ = distrib .proj₁
  distribʳ = distrib .proj₂

  _⊗ˢ_ : Sheaf → Sheaf → Sheaf
  𝓕 ⊗ˢ 𝓖 = α (U 𝓕 ∙ᵖ U 𝓖)

  εˢ : Sheaf
  εˢ = α εᵖ

  -- α is strong monoidal from PreSheaf to Sheaf
  module _ {F G : PreSheaf} where

    _∙ᵗ_ : ∃ᵗᵖ F → ∃ᵗᵖ G → ∃ᵗᵖ (F ∙ᵖ G)
    (leaf (x , Fx)) ∙ᵗ (leaf (y , Gy)) = leaf (-, -, -, refl , Fx , Gy)
    (leaf ∃F)       ∙ᵗ (node l r)      = node (leaf ∃F ∙ᵗ l) (leaf ∃F ∙ᵗ r)
    (node l r)      ∙ᵗ t               = node (l ∙ᵗ t) (r ∙ᵗ t)

    ∙ᵗ-⋁ᵗ-distrib : (t₁ : ∃ᵗᵖ F) (t₂ : ∃ᵗᵖ G) → (⋁ᵗ t₁ ∙ ⋁ᵗ t₂) ≤ ⋁ᵗ (t₁ ∙ᵗ t₂)
    ∙ᵗ-⋁ᵗ-distrib (leaf _) (leaf _) = refl
    ∙ᵗ-⋁ᵗ-distrib (leaf ∃F@(x , _)) (node l r) =
      begin
        x ∙ (⋁ᵗ l ∨ ⋁ᵗ r)
      ≤⟨ distribˡ x  (⋁ᵗ l) (⋁ᵗ r) ⟩
        (x ∙ ⋁ᵗ l) ∨ (x ∙ ⋁ᵗ r)
      ≤⟨ ∨-monoˡ (∙ᵗ-⋁ᵗ-distrib (leaf ∃F) l) ⟩
        ⋁ᵗ (leaf ∃F ∙ᵗ l) ∨ (x ∙ ⋁ᵗ r)
      ≤⟨ ∨-monoʳ (∙ᵗ-⋁ᵗ-distrib (leaf ∃F) r) ⟩
        ⋁ᵗ (leaf ∃F ∙ᵗ l) ∨ ⋁ᵗ (leaf ∃F ∙ᵗ r)
      ∎
      where open PosetReasoning poset
    ∙ᵗ-⋁ᵗ-distrib (node l r) t =
      begin
        ⋁ᵗ (node l r) ∙ ⋁ᵗ t
      ≡⟨⟩
        (⋁ᵗ l ∨ ⋁ᵗ r) ∙ ⋁ᵗ t
      ≤⟨ distribʳ (⋁ᵗ t) (⋁ᵗ l) (⋁ᵗ r) ⟩
        (⋁ᵗ l ∙ ⋁ᵗ t) ∨ (⋁ᵗ r ∙ ⋁ᵗ t)
      ≤⟨ ∨-monoˡ (∙ᵗ-⋁ᵗ-distrib l t) ⟩
        ⋁ᵗ (l ∙ᵗ t) ∨ (⋁ᵗ r ∙ ⋁ᵗ t)
      ≤⟨ ∨-monoʳ (∙ᵗ-⋁ᵗ-distrib r t) ⟩
        ⋁ᵗ (l ∙ᵗ t) ∨ ⋁ᵗ (r ∙ᵗ t)
      ≡⟨⟩
        ⋁ᵗ (node l r ∙ᵗ t)
      ∎
      where open PosetReasoning poset

    -- FIXME: This is essentially a map-and-⋁ operation that preserves the first components.
    α-monoidal-helper
      : Σ[ t  ∈ ∃ᵗᵖ (U (α F) ∙ᵖ U (α G)) ] (x ≤ ⋁ᵗ t) →
        Σ[ t′ ∈ ∃ᵗᵖ (F ∙ᵖ G) ] (x ≤ ⋁ᵗ t′)
    α-monoidal-helper (t , x≤⋁t) = go t x≤⋁t
      where
        -- The first argument is unpacked to satisty the termination checker.
        go : (t : ∃ᵗᵖ ((U (α F) ∙ᵖ U (α G)))) → x ≤ ⋁ᵗ t →  Σ[ t′ ∈ ∃ᵗᵖ (F ∙ᵖ G) ] (x ≤ ⋁ᵗ t′)
        go {x} (leaf (y , y₁ , y₂ , y≤y₁y₂ , (t₁ , y₁≤⋁t₁) , (t₂ , y₂≤⋁t₂))) x≤y =
          (t₁ ∙ᵗ t₂ , x≤⋁[t₁∙t₂])
          where
            x≤⋁[t₁∙t₂] =
              begin
                x
              ≤⟨ x≤y ⟩
                y
              ≤⟨ y≤y₁y₂ ⟩
                y₁ ∙ y₂
              ≤⟨ monoˡ y₁≤⋁t₁ ⟩
                (⋁ᵗ t₁) ∙ y₂
              ≤⟨ monoʳ y₂≤⋁t₂ ⟩
                (⋁ᵗ t₁) ∙ (⋁ᵗ t₂)
              ≤⟨ ∙ᵗ-⋁ᵗ-distrib t₁ t₂ ⟩
                ⋁ᵗ (t₁ ∙ᵗ t₂)
              ∎
              where open PosetReasoning poset
        go (node l r) x≤⋁l∨r =
          let (t₁ , ⋁l≤⋁t₁) , (t₂ , ⋁l≤⋁t₂) = go l refl , go r refl
          in (node t₁ t₂ , trans x≤⋁l∨r (∨-mono ⋁l≤⋁t₁ ⋁l≤⋁t₂))

    α-monoidal : (α F ⊗ˢ α G) ≈ˢ α (F ∙ᵖ G)
    α-monoidal .proj₁ .*≤ˢ* = α-monoidal-helper
    α-monoidal .proj₂ = α-mono (∙ᵖ-mono unit unit)

  ⊗ˢ-mono : Monotonic₂ _≤ˢ_ _≤ˢ_ _≤ˢ_ _⊗ˢ_
  ⊗ˢ-mono 𝓕₁≤𝓕₂ 𝓖₁≤𝓖₂ = α-mono (∙ᵖ-mono (U-mono 𝓕₁≤𝓕₂) (U-mono 𝓖₁≤𝓖₂))

  ⊗ˢ-assoc : Associative _≈ˢ_ _⊗ˢ_
  ⊗ˢ-assoc 𝓕 𝓖 𝓗 =
    begin
      (𝓕 ⊗ˢ 𝓖) ⊗ˢ 𝓗
    ≡⟨⟩
      α (U (α (U 𝓕 ∙ᵖ U 𝓖)) ∙ᵖ U 𝓗)
    ≈⟨ α-cong (∙ᵖ-congˡ (U-cong counit-≈ˢ)) ⟩
      α (U (α (U 𝓕 ∙ᵖ U 𝓖)) ∙ᵖ U (α (U 𝓗)))
    ≈⟨ α-monoidal ⟩
      α ((U 𝓕 ∙ᵖ U 𝓖) ∙ᵖ U 𝓗)
    ≈⟨ α-cong (∙ᵖ-assoc (U 𝓕) (U 𝓖) (U 𝓗)) ⟩
      α (U 𝓕 ∙ᵖ (U 𝓖 ∙ᵖ U 𝓗))
    ≈⟨ α-monoidal ⟨
      α (U (α (U 𝓕)) ∙ᵖ U (α (U 𝓖 ∙ᵖ U 𝓗)))
    ≈⟨ α-cong (∙ᵖ-congʳ (U-cong counit-≈ˢ)) ⟨
      α (U 𝓕 ∙ᵖ U (α (U 𝓖 ∙ᵖ U 𝓗)))
    ≡⟨⟩
      𝓕 ⊗ˢ (𝓖 ⊗ˢ 𝓗)
    ∎
    where open SetoidReasoning ≈ˢ-setoid

  ⊗ˢ-identityˡ : LeftIdentity _≈ˢ_ εˢ _⊗ˢ_
  ⊗ˢ-identityˡ 𝓕 =
    begin
      εˢ ⊗ˢ 𝓕
    ≡⟨⟩
      α (U (α εᵖ) ∙ᵖ U 𝓕)
    ≈⟨ α-cong (∙ᵖ-congˡ (U-cong counit-≈ˢ)) ⟩
      α (U (α εᵖ) ∙ᵖ U (α (U 𝓕)))
    ≈⟨ α-monoidal ⟩
      α (εᵖ ∙ᵖ U 𝓕)
    ≈⟨ α-cong (∙ᵖ-identityˡ (U 𝓕)) ⟩
      α (U 𝓕)
    ≈⟨ counit-≈ˢ ⟨
      𝓕
    ∎
    where open SetoidReasoning ≈ˢ-setoid

  ⊗ˢ-identityʳ : RightIdentity _≈ˢ_ εˢ _⊗ˢ_
  ⊗ˢ-identityʳ 𝓕 =
    begin
      𝓕 ⊗ˢ εˢ
    ≡⟨⟩
      α (U 𝓕 ∙ᵖ U (α εᵖ))
    ≈⟨ α-cong (∙ᵖ-congʳ (U-cong counit-≈ˢ)) ⟩
      α (U (α (U 𝓕)) ∙ᵖ U (α εᵖ))
    ≈⟨ α-monoidal ⟩
      α (U 𝓕 ∙ᵖ εᵖ)
    ≈⟨ α-cong (∙ᵖ-identityʳ (U 𝓕)) ⟩
      α (U 𝓕)
    ≈⟨ counit-≈ˢ ⟨
      𝓕
    ∎
    where open SetoidReasoning ≈ˢ-setoid

  ⊗ˢ-comm : Commutative _≈ˢ_ _⊗ˢ_
  ⊗ˢ-comm 𝓕 𝓖 = α-cong (∙ᵖ-comm (U 𝓕) (U 𝓖))

  ⊗ˢ-isCommutativePomonoid : IsCommutativePomonoid _≈ˢ_ _≤ˢ_ _⊗ˢ_ εˢ
  ⊗ˢ-isCommutativePomonoid = record
    { isPomonoid = record
      { isPosemigroup = record
        { isPomagma = record
          { isPartialOrder = ≤ˢ-isPartialOrder
          ; mono = ⊗ˢ-mono
          }
        ; assoc = ⊗ˢ-assoc
        }
      ; identity = ⊗ˢ-identityˡ , ⊗ˢ-identityʳ
      }
      ; comm = ⊗ˢ-comm
    }

  commutativePomonoid : CommutativePomonoid (suc (c ⊔ ℓ₂)) (c ⊔ ℓ₂) (c ⊔ ℓ₂)
  commutativePomonoid =
    record { isCommutativePomonoid = ⊗ˢ-isCommutativePomonoid }

  module _ {𝓕 𝓖 : Sheaf} where

    -- Residuals are automatically closed, relying on distributivity.
    -- BOB: Is this deducible from strong monoidality of α?
    ⊸ˢ-helper : (t : ∃ᵗ[ x ] (∀ {y} → 𝓕 .ICarrier y → 𝓖 .ICarrier (x ∙ y))) →
              ∀ {y} → 𝓕 .ICarrier y →
              Σ[ t′ ∈ ∃ᵗˢ 𝓖 ] (⋁ᵗ t ∙ y) ≤ ⋁ᵗ t′
    ⊸ˢ-helper (leaf (x , f)) 𝓕y = leaf (-, f 𝓕y) , refl
    ⊸ˢ-helper (node l r)     𝓕y =
      let (l′ , ⋁l∙y≤⋁l′) , (r′ , ⋁r∙y≤⋁r′) = ⊸ˢ-helper l 𝓕y , ⊸ˢ-helper r 𝓕y
      in node l′ r′ , trans (distribʳ _ (⋁ᵗ l) (⋁ᵗ r)) (∨-mono ⋁l∙y≤⋁l′ ⋁r∙y≤⋁r′)

  _⊸ˢ_ : Sheaf → Sheaf → Sheaf
  (𝓕 ⊸ˢ 𝓖) .ICarrier x = ∀ {y} → 𝓕 .ICarrier y → 𝓖 .ICarrier (x ∙ y)
  (𝓕 ⊸ˢ 𝓖) .≤-closed x≤z f 𝓕y = 𝓖 .≤-closed (monoˡ x≤z) (f 𝓕y)
  (𝓕 ⊸ˢ 𝓖) .∨-closed t {y} 𝓕y =
    let (t′ , ⋁t∙y≤⋁t′) = ⊸ˢ-helper {𝓕} {𝓖} t {y} 𝓕y in
      𝓖 .≤-closed ⋁t∙y≤⋁t′ (𝓖 .∨-closed t′)

  U⊸ˢ : U (𝓕 ⊸ˢ 𝓖) ≤ᵖ (U 𝓕 ⇨ᵖ U 𝓖)
  U⊸ˢ .*≤ᵖ* f = f

  U⊸ˢ⁻¹ : (U 𝓕 ⇨ᵖ U 𝓖) ≤ᵖ U (𝓕 ⊸ˢ 𝓖)
  U⊸ˢ⁻¹ .*≤ᵖ* f = f

  U⊸ˢ-≈ᵖ : U (𝓕 ⊸ˢ 𝓖) ≈ᵖ (U 𝓕 ⇨ᵖ U 𝓖)
  U⊸ˢ-≈ᵖ = (U⊸ˢ , U⊸ˢ⁻¹)

  -- FIXME: Find a more abstract way of doing this.
  ⊸ˢ-residual-to : (𝓕 ⊗ˢ 𝓖) ≤ˢ 𝓗 → 𝓖 ≤ˢ (𝓕 ⊸ˢ 𝓗)
  ⊸ˢ-residual-to {𝓕} {𝓖} {𝓗} 𝓕∙𝓖≤𝓗 .*≤ˢ* 𝓖x 𝓕y =
    𝓖∙𝓕≤𝓗 .*≤ˢ* (leaf (-, -, -, refl , 𝓖x , 𝓕y) , refl)
    where
      𝓖∙𝓕≤𝓗 = ≤ˢ-trans (≤ˢ-respˡ-≈ˢ (⊗ˢ-comm 𝓕 𝓖) ≤ˢ-refl) 𝓕∙𝓖≤𝓗

  ⊸ˢ-residual-from : 𝓖 ≤ˢ (𝓕 ⊸ˢ 𝓗) → (𝓕 ⊗ˢ 𝓖) ≤ˢ 𝓗
  ⊸ˢ-residual-from {𝓖} {𝓕} {𝓗} 𝓖≤𝓕⇨𝓗 =
    begin
      𝓕 ⊗ˢ 𝓖
    ≡⟨⟩
      α (U 𝓕 ∙ᵖ U 𝓖)
    ≤⟨ α-mono (⇨ᵖ-residual-from (≤ᵖ-trans (U-mono 𝓖≤𝓕⇨𝓗) U⊸ˢ)) ⟩
      α (U 𝓗)
    ≈⟨ counit-≈ˢ ⟨
      𝓗
    ∎
    where open PosetReasoning ≤ˢ-poset

  ⊸ˢ-residual : RightResidual _≤ˢ_ _⊗ˢ_ _⊸ˢ_
  ⊸ˢ-residual .Function.Equivalence.to        = ⊸ˢ-residual-to
  ⊸ˢ-residual .Function.Equivalence.from      = ⊸ˢ-residual-from
  ⊸ˢ-residual .Function.Equivalence.to-cong   = λ { PropEq.refl → PropEq.refl }
  ⊸ˢ-residual .Function.Equivalence.from-cong = λ { PropEq.refl → PropEq.refl }

  ⊸ˢ-⊗ˢ-isResiduatedCommutativePomonoid : IsResiduatedCommutativePomonoid _≈ˢ_ _≤ˢ_ _⊗ˢ_ _⊸ˢ_ εˢ
  ⊸ˢ-⊗ˢ-isResiduatedCommutativePomonoid = record
    { isCommutativePomonoid = ⊗ˢ-isCommutativePomonoid
    ; residuated = comm∧residual⇒residuated ≤ˢ-isPreorder ⊗ˢ-comm ⊸ˢ-residual
    }

------------------------------------------------------------------------------
-- Lift duoidals to sheaves
module LiftIsDuoidal
    {_∙_} {_▷_} {ε} {ι}
    (isDuoidal : IsDuoidal _≈_ _≤_ _∙_ _▷_ ε ι)
    (comm : Commutative _≈_ _∙_)
    (distrib : _DistributesOver_ _≤_ _∙_ _∨_)
    (∨-entropy : Entropy _≤_ _∨_ _▷_)
    (∨-tidy : ι ∨ ι ≤ ι)
  where

  open IsDuoidal isDuoidal

  ∙-isCommutativePomonoid : IsCommutativePomonoid _≈_ _≤_ _∙_ ε
  ∙-isCommutativePomonoid = record
    { isPomonoid = ∙-isPomonoid
    ; comm       = comm
    }

  open LiftIsCommutativePomonoid ∙-isCommutativePomonoid distrib
  open LiftIsPomonoid ▷-isPomonoid ∨-entropy ∨-tidy
  open P.LiftIsDuoidal isDuoidal

  ⊗ˢ-▷ˢ-entropy : Entropy _≤ˢ_ _⊗ˢ_ _▷ˢ_
  ⊗ˢ-▷ˢ-entropy 𝓕₁ 𝓖₁ 𝓕₂ 𝓖₂ =
    begin
      (𝓕₁ ▷ˢ 𝓖₁) ⊗ˢ (𝓕₂ ▷ˢ 𝓖₂)
    ≡⟨⟩
      α (U (𝓕₁ ▷ˢ 𝓖₁) ∙ᵖ U (𝓕₂ ▷ˢ 𝓖₂))
    ≈⟨ α-cong (∙ᵖ-cong U-monoidal U-monoidal) ⟩
      α ((U 𝓕₁ ▷ᵖ U 𝓖₁) ∙ᵖ (U 𝓕₂ ▷ᵖ U 𝓖₂))
    ≤⟨ α-mono (∙ᵖ-▷ᵖ-entropy (U 𝓕₁) (U 𝓖₁) (U 𝓕₂) (U 𝓖₂)) ⟩
      α ((U 𝓕₁ ∙ᵖ U 𝓕₂) ▷ᵖ (U 𝓖₁ ∙ᵖ U 𝓖₂))
    ≤⟨ α-mono (▷ᵖ-mono unit unit) ⟩
      α (U (α (U 𝓕₁ ∙ᵖ U 𝓕₂)) ▷ᵖ U (α (U 𝓖₁ ∙ᵖ U 𝓖₂)))
    ≈⟨ α-cong U-monoidal ⟨
      α (U (α (U 𝓕₁ ∙ᵖ U 𝓕₂) ▷ˢ α (U 𝓖₁ ∙ᵖ U 𝓖₂)))
    ≈⟨ counit-≈ˢ ⟨
      α (U 𝓕₁ ∙ᵖ U 𝓕₂) ▷ˢ α (U 𝓖₁ ∙ᵖ U 𝓖₂)
    ≡⟨⟩
      (𝓕₁ ⊗ˢ 𝓕₂) ▷ˢ (𝓖₁ ⊗ˢ 𝓖₂)
    ∎
    where open PosetReasoning ≤ˢ-poset

  εˢ≤ιˢ : εˢ ≤ˢ ιˢ
  εˢ≤ιˢ .*≤ˢ* (t , x≤t) =
    lift (≤-trans x≤t
         (≤-trans (mapᵗ-⋁ᵗ t)
                  (⋁ˢ (mapᵗ (λ (lift y≤ε) → lift (≤-trans y≤ε ε≲ι)) t))))

  ⊗ˢ-▷ˢ-isDuoidal : IsDuoidal _≈ˢ_ _≤ˢ_ _⊗ˢ_ _▷ˢ_ εˢ ιˢ
  ⊗ˢ-▷ˢ-isDuoidal = record
    { ∙-isPomonoid = IsCommutativePomonoid.isPomonoid ⊗ˢ-isCommutativePomonoid
    ; ▷-isPomonoid = ▷ˢ-isPomonoid
    ; ∙-▷-entropy = ⊗ˢ-▷ˢ-entropy
    ; ∙-idem-ι = ≤ˢ-trans (α-mono (∙ᵖ-mono (U-monoidal-ι .proj₁) (U-monoidal-ι .proj₁)))
                (≤ˢ-trans (α-mono ∙ᵖ-idem-ιᵖ)
                (≤ˢ-trans (α-mono (U-monoidal-ι .proj₂))
                          counit))
    ; ▷-idem-ε = ≤ˢ-trans (α-mono ▷ᵖ-idem-εᵖ)
                (≤ˢ-trans (α-mono (▷ᵖ-mono unit unit))
                (≤ˢ-trans (α-mono (U-monoidal .proj₂))
                counit))
    ; ε≲ι = εˢ≤ιˢ
    }
