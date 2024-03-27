{-# OPTIONS --postfix-projections --safe --without-K --no-exact-split #-}

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

module Algebra.Ordered.Construction.Ideal {c ℓ₁ ℓ₂} (pomagma : Pomagma c ℓ₁ ℓ₂) where

open Pomagma pomagma
  using
    ( Carrier
    ; _≈_
    ; _≤_
    ; poset
    )
  renaming
    ( _∙_        to _+_
    ; mono       to +-mono
    ; monoˡ      to +-monoˡ
    ; monoʳ      to +-monoʳ
    ; refl       to ≤-refl
    ; trans      to ≤-trans
    )

open import Algebra.Ordered.Construction.LowerSet poset as P
  using
    ( PreSheaf
    ; ICarrier
    ; ≤-closed
    ; _≤ᵖ_
    ; *≤ᵖ*
    ; ≤ᵖ-refl
    ; ≤ᵖ-trans
    ; _≈ᵖ_
    ; ηᵖ
    ; ηᵖ-mono
    ; _∨ᵖ_
    ; inj₁ᵖ
    ; inj₂ᵖ
    ; [_,_]ᵖ
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

record Ideal : Set (suc (c ⊔ ℓ₂)) where
  no-eta-equality
  field
    ICarrier : Carrier → Set (c ⊔ ℓ₂)
    ≤-closed : x ≤ y → ICarrier y → ICarrier x
    +-closed : ICarrier x → ICarrier y → ICarrier (x + y)
open Ideal

private
  variable
    𝓕 𝓕₁ 𝓕₂ : Ideal
    𝓖 𝓖₁ 𝓖₂ : Ideal
    𝓗 𝓗₁ 𝓗₂ : Ideal

infix 4 _≤ⁱ_

record _≤ⁱ_ (𝓕 𝓖 : Ideal) : Set (c ⊔ ℓ₂) where
  no-eta-equality
  field
    *≤ⁱ* : 𝓕 .ICarrier ⊆ 𝓖 .ICarrier
open _≤ⁱ_

infix 4 _≈ⁱ_

_≈ⁱ_ : Ideal → Ideal → Set (c ⊔ ℓ₂)
_≈ⁱ_ = SymCore _≤ⁱ_

≤ⁱ-refl : 𝓕 ≤ⁱ 𝓕
≤ⁱ-refl .*≤ⁱ* 𝓕x = 𝓕x

≤ⁱ-trans : 𝓕 ≤ⁱ 𝓖 → 𝓖 ≤ⁱ 𝓗 → 𝓕 ≤ⁱ 𝓗
≤ⁱ-trans 𝓕≤𝓖 𝓖≤𝓗 .*≤ⁱ* z = 𝓖≤𝓗 .*≤ⁱ* (𝓕≤𝓖 .*≤ⁱ* z)

-- FIXME: get rid of the propositional equality here
≤ⁱ-isPartialOrder : IsPartialOrder _≈ⁱ_ _≤ⁱ_
≤ⁱ-isPartialOrder = SymCore.isPreorder⇒isPartialOrder _≤ⁱ_ ≡-≤ⁱ-isPreorder
  where
    ≡-≤ⁱ-isPreorder : IsPreorder _≡_ _≤ⁱ_
    ≡-≤ⁱ-isPreorder = record
      { isEquivalence = PropEq.isEquivalence
      ; reflexive = λ { PropEq.refl → ≤ⁱ-refl }
      ; trans = ≤ⁱ-trans
      }

open IsPartialOrder ≤ⁱ-isPartialOrder
  using
    ( module Eq
    )
  renaming
    ( ≤-respˡ-≈  to ≤ⁱ-respˡ-≈ⁱ
    ; reflexive to ≤ⁱ-reflexive
    ; isPreorder to ≤ⁱ-isPreorder
    )
  public

≤ⁱ-poset : Poset _ _ _
≤ⁱ-poset = record
  { isPartialOrder = ≤ⁱ-isPartialOrder
  }

≈ⁱ-setoid : Setoid _ _
≈ⁱ-setoid = record
  { isEquivalence = Poset.isEquivalence ≤ⁱ-poset
  }

------------------------------------------------------------------------------
-- From ideals to lower sets
U : Ideal → PreSheaf
U 𝓕 .ICarrier = 𝓕 .ICarrier
U 𝓕 .≤-closed = 𝓕 .≤-closed

U-mono : 𝓕 ≤ⁱ 𝓖 → U 𝓕 ≤ᵖ U 𝓖
U-mono 𝓕≤𝓖 .*≤ᵖ* = 𝓕≤𝓖 .*≤ⁱ*

U-cong : 𝓕 ≈ⁱ 𝓖 → U 𝓕 ≈ᵖ U 𝓖
U-cong (𝓖≤𝓕 , 𝓕≤𝓖) = U-mono 𝓖≤𝓕 , U-mono 𝓕≤𝓖

------------------------------------------------------------------------------
-- Turn a lower set into an ideal by closing under +

data ctxt (F : PreSheaf) : Set (c ⊔ ℓ₂) where
  leaf : (x : Carrier) → F .ICarrier x → ctxt F
  node : ctxt F → ctxt F → ctxt F

sum : ctxt F → Carrier
sum (leaf x _) = x
sum (node c d) = sum c + sum d

ctxt-map : F ≤ᵖ G → ctxt F → ctxt G
ctxt-map F≤G (leaf x Fx) = leaf x (F≤G .*≤ᵖ* Fx)
ctxt-map F≤G (node c d)  = node (ctxt-map F≤G c) (ctxt-map F≤G d)

ctxt-map-sum : (F≤G : F ≤ᵖ G) (c : ctxt F) → sum c ≤ sum (ctxt-map F≤G c)
ctxt-map-sum F≤G (leaf x Fx) = ≤-refl
ctxt-map-sum F≤G (node c d) = +-mono (ctxt-map-sum F≤G c) (ctxt-map-sum F≤G d)

α : PreSheaf → Ideal
α F .ICarrier x = Σ[ t ∈ ctxt F ] (x ≤ sum t)
α F .≤-closed x≤y (t , y≤t) = t , ≤-trans x≤y y≤t
α F .+-closed (s , x≤s) (t , y≤t) = node s t , +-mono x≤s y≤t

α-mono : F ≤ᵖ G → α F ≤ⁱ α G
α-mono F≤G .*≤ⁱ* (t , x≤t) = ctxt-map F≤G t , ≤-trans x≤t (ctxt-map-sum F≤G t)

α-cong : ∀ {F G} → F ≈ᵖ G → α F ≈ⁱ α G
α-cong (G≤F , F≤G) = (α-mono G≤F , α-mono F≤G)

------------------------------------------------------------------------------
ηⁱ : Carrier → Ideal
ηⁱ x = α (ηᵖ x)

ηⁱ-mono : x ≤ y → ηⁱ x ≤ⁱ ηⁱ y
ηⁱ-mono x≤y = α-mono (ηᵖ-mono x≤y)

------------------------------------------------------------------------------
-- U and α form a Galois connection

ideal-ctxt-closed : (t : ctxt (U 𝓕)) → 𝓕 .ICarrier (sum t)
ideal-ctxt-closed {𝓕} (leaf x ϕ) = ϕ
ideal-ctxt-closed {𝓕} (node c d) = 𝓕 .+-closed (ideal-ctxt-closed c) (ideal-ctxt-closed d)

counit : α (U 𝓕) ≤ⁱ 𝓕
counit {𝓕} .*≤ⁱ* (t , x≤t) = 𝓕 .≤-closed x≤t (ideal-ctxt-closed t)

counit⁻¹ : 𝓕 ≤ⁱ α (U 𝓕)
counit⁻¹ .*≤ⁱ* 𝓕x = leaf _ 𝓕x , ≤-refl

counit-≈ⁱ : 𝓕 ≈ⁱ α (U 𝓕)
counit-≈ⁱ = counit⁻¹ , counit

unit : F ≤ᵖ U (α F)
unit .*≤ᵖ* Fx = leaf _ Fx , ≤-refl

------------------------------------------------------------------------------
-- Binary meets

_∧ⁱ_ : Ideal → Ideal → Ideal
(𝓕 ∧ⁱ 𝓖) .ICarrier x = 𝓕 .ICarrier x × 𝓖 .ICarrier x
(𝓕 ∧ⁱ 𝓖) .≤-closed x≤y (𝓕y , 𝓖y) = 𝓕 .≤-closed x≤y 𝓕y , 𝓖 .≤-closed x≤y 𝓖y
(𝓕 ∧ⁱ 𝓖) .+-closed (𝓕x , 𝓖x) (𝓕y , 𝓖y) = (𝓕 .+-closed 𝓕x 𝓕y) , (𝓖 .+-closed 𝓖x 𝓖y)

proj₁ⁱ : (𝓕 ∧ⁱ 𝓖) ≤ⁱ 𝓕
proj₁ⁱ .*≤ⁱ* = proj₁

proj₂ⁱ : (𝓕 ∧ⁱ 𝓖) ≤ⁱ 𝓖
proj₂ⁱ .*≤ⁱ* = proj₂

⟨_,_⟩ⁱ : 𝓕 ≤ⁱ 𝓖 → 𝓕 ≤ⁱ 𝓗 → 𝓕 ≤ⁱ (𝓖 ∧ⁱ 𝓗)
⟨ 𝓗≤𝓕 , 𝓗≤𝓖 ⟩ⁱ .*≤ⁱ* = < 𝓗≤𝓕 .*≤ⁱ* , 𝓗≤𝓖 .*≤ⁱ* >

∧ⁱ-isMeetSemilattice : IsMeetSemilattice _≈ⁱ_ _≤ⁱ_ _∧ⁱ_
∧ⁱ-isMeetSemilattice = record
  { isPartialOrder = ≤ⁱ-isPartialOrder
  ; infimum        = λ 𝓕 𝓖 → (proj₁ⁱ ,  proj₂ⁱ , λ 𝓗 → ⟨_,_⟩ⁱ)
  }

-- FIXME: under what conditions does α preserve meets?

------------------------------------------------------------------------------
-- Binary joins

_∨ⁱ_ : Ideal → Ideal → Ideal
𝓕 ∨ⁱ 𝓖 = α (U 𝓕 ∨ᵖ U 𝓖)

inj₁ⁱ : 𝓕 ≤ⁱ (𝓕 ∨ⁱ 𝓖)
inj₁ⁱ = ≤ⁱ-trans counit⁻¹ (α-mono inj₁ᵖ)

inj₂ⁱ : 𝓖 ≤ⁱ (𝓕 ∨ⁱ 𝓖)
inj₂ⁱ = ≤ⁱ-trans counit⁻¹ (α-mono inj₂ᵖ)

[_,_]ⁱ : 𝓕 ≤ⁱ 𝓗 → 𝓖 ≤ⁱ 𝓗 → (𝓕 ∨ⁱ 𝓖) ≤ⁱ 𝓗
[_,_]ⁱ {𝓕} {𝓗} {𝓖} 𝓕≤𝓗 𝓖≤𝓗 .*≤ⁱ* (t , x≤t) =
  𝓗 .≤-closed (≤-trans x≤t (ctxt-map-sum _ t)) (ideal-ctxt-closed (ctxt-map [ U-mono 𝓕≤𝓗 , U-mono 𝓖≤𝓗 ]ᵖ t))

∨ⁱ-isJoinSemilattice : IsJoinSemilattice _≈ⁱ_ _≤ⁱ_ _∨ⁱ_
∨ⁱ-isJoinSemilattice = record
  { isPartialOrder = ≤ⁱ-isPartialOrder
  ; supremum       = λ 𝓕 𝓖 → (inj₁ⁱ , inj₂ⁱ , λ 𝓗 → [_,_]ⁱ)
  }


hulp : (c : ctxt (ηᵖ (x + y))) → Σ[ d ∈ ctxt (U (α (ηᵖ x) ∨ⁱ α (ηᵖ y))) ] (sum c ≤ sum d)
hulp {x}{y} (leaf z (lift z≤x+y)) =
  (node (leaf x (inj₁ⁱ .*≤ⁱ* ((leaf x (lift ≤-refl)) , ≤-refl)))
        (leaf y (inj₂ⁱ .*≤ⁱ* ((leaf y (lift ≤-refl)) , ≤-refl)))) ,
  z≤x+y
hulp (node c₁ c₂) =
  let (d₁ , c₁≤d₁) , (d₂ , c₂≤d₂) = hulp c₁ , hulp c₂
  in node d₁ d₂ , +-mono c₁≤d₁ c₂≤d₂

η-preserve-+ : α (ηᵖ (x + y)) ≤ⁱ α (ηᵖ x) ∨ⁱ α (ηᵖ y)
η-preserve-+ {x}{y} .*≤ⁱ* {z} (c , z≤c) =
  let d , c≤d = hulp c in down-closed (≤-trans z≤c c≤d) (ideal-ctxt-closed d)
  where open Ideal (α (ηᵖ x) ∨ⁱ α (ηᵖ y)) renaming (≤-closed to down-closed)


------------------------------------------------------------------------------
module DayEntropic {_∙_ ε}
    (isPomonoid : IsPomonoid _≈_ _≤_ _∙_ ε)
    (+-entropy : Entropy _≤_ _+_ _∙_)
    (+-tidy    : ε + ε ≤ ε)
    where

  _◁ⁱ_ : Ideal → Ideal → Ideal
  (𝓕 ◁ⁱ 𝓖) .ICarrier x =
    ∃[ y ] ∃[ z ] (x ≤ (y ∙ z) × 𝓕 .ICarrier y × 𝓖 .ICarrier z)
  (𝓕 ◁ⁱ 𝓖) .≤-closed x≤w (y , z , w≤yz , 𝓕y , 𝓖z) =
    (-, -, ≤-trans x≤w w≤yz , 𝓕y , 𝓖z)
  (𝓕 ◁ⁱ 𝓖) .+-closed (y₁ , z₁ , x₁≤y₁z₁ , ϕ₁ , ψ₁) (y₂ , z₂ , x₂≤y₂z₂ , ϕ₂ , ψ₂) =
    y₁ + y₂ , z₁ + z₂ ,
    ≤-trans (+-mono x₁≤y₁z₁ x₂≤y₂z₂) (+-entropy _ _ _ _) ,
    𝓕 .+-closed ϕ₁ ϕ₂ ,
    𝓖 .+-closed ψ₁ ψ₂

  ιⁱ : Ideal
  ιⁱ .ICarrier x = Lift c (x ≤ ε)
  ιⁱ .≤-closed x≤y (lift y≤ε) = lift (≤-trans x≤y y≤ε)
  ιⁱ .+-closed (lift x≤ε) (lift y≤ε) = lift (≤-trans (+-mono x≤ε y≤ε) +-tidy)

  open P.LiftIsPomonoid isPomonoid

  ◁ⁱ-mono : Monotonic₂ _≤ⁱ_ _≤ⁱ_ _≤ⁱ_ _◁ⁱ_
  ◁ⁱ-mono 𝓕₁≤𝓖₁ 𝓕₂≤𝓖₂ .*≤ⁱ* = ∙ᵖ-mono (U-mono 𝓕₁≤𝓖₁) (U-mono 𝓕₂≤𝓖₂) .*≤ᵖ*

  ◁ⁱ-assoc : Associative _≈ⁱ_ _◁ⁱ_
  ◁ⁱ-assoc 𝓕 𝓖 𝓗 .proj₁ .*≤ⁱ* = ∙ᵖ-assoc (U 𝓕) (U 𝓖) (U 𝓗) .proj₁ .*≤ᵖ*
  ◁ⁱ-assoc 𝓕 𝓖 𝓗 .proj₂ .*≤ⁱ* = ∙ᵖ-assoc (U 𝓕) (U 𝓖) (U 𝓗) .proj₂ .*≤ᵖ*

  ◁ⁱ-identityˡ : LeftIdentity _≈ⁱ_ ιⁱ _◁ⁱ_
  ◁ⁱ-identityˡ 𝓕 .proj₁ .*≤ⁱ* = ∙ᵖ-identityˡ (U 𝓕) .proj₁ .*≤ᵖ*
  ◁ⁱ-identityˡ 𝓕 .proj₂ .*≤ⁱ* = ∙ᵖ-identityˡ (U 𝓕) .proj₂ .*≤ᵖ*

  ◁ⁱ-identityʳ : RightIdentity _≈ⁱ_ ιⁱ _◁ⁱ_
  ◁ⁱ-identityʳ 𝓕 .proj₁ .*≤ⁱ* = ∙ᵖ-identityʳ (U 𝓕) .proj₁ .*≤ᵖ*
  ◁ⁱ-identityʳ 𝓕 .proj₂ .*≤ⁱ* = ∙ᵖ-identityʳ (U 𝓕) .proj₂ .*≤ᵖ*

  ◁ⁱ-identity : Identity _≈ⁱ_ ιⁱ _◁ⁱ_
  ◁ⁱ-identity = (◁ⁱ-identityˡ , ◁ⁱ-identityʳ)

  ◁ⁱ-isPomonoid : IsPomonoid _≈ⁱ_ _≤ⁱ_ _◁ⁱ_ ιⁱ
  ◁ⁱ-isPomonoid = record
    { isPosemigroup = record
      { isPomagma = record
        { isPartialOrder = ≤ⁱ-isPartialOrder
        ; mono = ◁ⁱ-mono
        }
      ; assoc = ◁ⁱ-assoc
      }
    ; identity = ◁ⁱ-identity
    }

  U-monoidal : U (𝓕 ◁ⁱ 𝓖) ≈ᵖ (U 𝓕 ∙ᵖ U 𝓖)
  U-monoidal .proj₁ .*≤ᵖ* 𝓕x = 𝓕x
  U-monoidal .proj₂ .*≤ᵖ* 𝓕x = 𝓕x

  U-monoidal-ι : U ιⁱ ≈ᵖ εᵖ
  U-monoidal-ι .proj₁ .*≤ᵖ* x≤ε = x≤ε
  U-monoidal-ι .proj₂ .*≤ᵖ* x≤ε = x≤ε

  ηⁱ-preserve-◁ : ηⁱ (x ∙ y) ≤ⁱ ηⁱ x ◁ⁱ ηⁱ y
  ηⁱ-preserve-◁ {x}{y} .*≤ⁱ* {z} (c , z≤c) =
    down-closed
      (≤-trans z≤c (ctxt-map-sum _ c))
      (ideal-ctxt-closed {α (ηᵖ x) ◁ⁱ α (ηᵖ y)}
         (ctxt-map (≤ᵖ-trans η-preserve-∙ (≤ᵖ-trans (∙ᵖ-mono unit unit) (U-monoidal .proj₂))) c))
    where open Ideal (α (ηᵖ x) ◁ⁱ α (ηᵖ y)) renaming (≤-closed to down-closed)

{-
  -- FIXME: this doesn't work
  module _ (idem : ∀ {x} → x + x ≤ x) where

    open IsPomonoid isPomonoid using (mono)

    -- FIXME: this is the same combination function as below
    _∙ᶜ'_ : ctxt F → ctxt G → ctxt (F ∙ᵖ G)
    leaf x Fx  ∙ᶜ' leaf y Gy  = leaf (x ∙ y) (x , y , ≤-refl , Fx , Gy)
    leaf x Fx  ∙ᶜ' node d₁ d₂ = node (leaf x Fx ∙ᶜ' d₁) (leaf x Fx ∙ᶜ' d₂)
    node c₁ c₂ ∙ᶜ' d          = node (c₁ ∙ᶜ' d) (c₂ ∙ᶜ' d)

    ∙ᶜ-sum : (c : ctxt F)(d : ctxt G) → sum (c ∙ᶜ' d) ≤ sum c ∙ sum d
    ∙ᶜ-sum (leaf x Fx)  (leaf y Gy)  = ≤-refl
    ∙ᶜ-sum (leaf x Fx)  (node d₁ d₂) =
       ≤-trans (+-mono (∙ᶜ-sum (leaf x Fx) d₁) (∙ᶜ-sum (leaf x Fx) d₂))
      (≤-trans (+-entropy _ _ _ _)
               (mono idem ≤-refl))
    ∙ᶜ-sum (node c₁ c₂) d =
      ≤-trans (+-mono (∙ᶜ-sum c₁ d) (∙ᶜ-sum c₂ d))
      (≤-trans (+-entropy _ _ _ _)
      (mono ≤-refl idem))

    ηⁱ-preserve-◁⁻¹ : α (ηᵖ x) ◁ⁱ α (ηᵖ y) ≤ⁱ α (ηᵖ (x ∙ y))
    ηⁱ-preserve-◁⁻¹ {x}{y} .*≤ⁱ* {z} (z₁ , z₂ , z≤z₁z₂ , (c₁ , z₁≤c) , (c₂ , z₂≤c)) =
      ctxt-map η-preserve-∙⁻¹ (c₁ ∙ᶜ' c₂) ,
      ≤-trans z≤z₁z₂ {!!}
-}

module DayDistributive
    {_∙_} {ε}
    (isCommutativePomonoid : IsCommutativePomonoid _≈_ _≤_ _∙_ ε)
    (distrib : _DistributesOver_ _≤_ _∙_ _+_)
  where

  open IsCommutativePomonoid isCommutativePomonoid
  open P.LiftIsCommutativePomonoid isCommutativePomonoid

  distribˡ = distrib .proj₁
  distribʳ = distrib .proj₂

  _∙ⁱ_ : Ideal → Ideal → Ideal
  𝓕 ∙ⁱ 𝓖 = α (U 𝓕 ∙ᵖ U 𝓖)

  εⁱ : Ideal
  εⁱ = α εᵖ

  _∙ᶜ_ : ctxt F → ctxt G → ctxt (F ∙ᵖ G)
  leaf x Fx  ∙ᶜ leaf y Gy  = leaf (x ∙ y) (x , y , ≤-refl , Fx , Gy)
  leaf x Fx  ∙ᶜ node d₁ d₂ = node (leaf x Fx ∙ᶜ d₁) (leaf x Fx ∙ᶜ d₂)
  node c₁ c₂ ∙ᶜ d          = node (c₁ ∙ᶜ d) (c₂ ∙ᶜ d)

  ∙ᶜ-sum : (c : ctxt F)(d : ctxt G) → sum c ∙ sum d ≤ sum (c ∙ᶜ d)
  ∙ᶜ-sum (leaf x Fx)  (leaf y Gy)  = ≤-refl
  ∙ᶜ-sum (leaf x Fx)  (node d₁ d₂) = ≤-trans (distribˡ _ _ _) (+-mono (∙ᶜ-sum (leaf x Fx) d₁) (∙ᶜ-sum (leaf x Fx) d₂))
  ∙ᶜ-sum (node c₁ c₂) d            = ≤-trans (distribʳ _ _ _) (+-mono (∙ᶜ-sum c₁ d) (∙ᶜ-sum c₂ d))

  α-helper : (c : ctxt (U (α F) ∙ᵖ U (α G))) → x ≤ sum c → Σ[ d ∈ ctxt (F ∙ᵖ G) ] (x ≤ sum d)
  α-helper (leaf y (y₁ , y₂ , y≤y₁y₂ , (c , y₁≤c) , (d , y₂≤d))) x≤y =
    (c ∙ᶜ d) , ≤-trans x≤y (≤-trans y≤y₁y₂ (≤-trans (mono y₁≤c y₂≤d) (∙ᶜ-sum c d)))
  α-helper (node c d) x≤cd =
    let (c' , c≤c') , (d' , d≤d') = α-helper c ≤-refl , α-helper d ≤-refl
    in (node c' d') , (≤-trans x≤cd (+-mono c≤c' d≤d'))

  α-monoidal : (α F ∙ⁱ α G) ≈ⁱ α (F ∙ᵖ G)
  α-monoidal .proj₁ .*≤ⁱ* (c , x≤c)  = α-helper c x≤c
  α-monoidal .proj₂ = α-mono (∙ᵖ-mono unit unit)

  ∙ⁱ-mono : Monotonic₂ _≤ⁱ_ _≤ⁱ_ _≤ⁱ_ _∙ⁱ_
  ∙ⁱ-mono 𝓕₁≤𝓕₂ 𝓖₁≤𝓖₂ = α-mono (∙ᵖ-mono (U-mono 𝓕₁≤𝓕₂) (U-mono 𝓖₁≤𝓖₂))

  ηⁱ-preserve-∙ : ηⁱ (x ∙ y) ≤ⁱ ηⁱ x ∙ⁱ ηⁱ y
  ηⁱ-preserve-∙ = α-mono (≤ᵖ-trans η-preserve-∙ (∙ᵖ-mono unit unit))

  ηⁱ-preserve-∙⁻¹ : ηⁱ x ∙ⁱ ηⁱ y ≤ⁱ ηⁱ (x ∙ y)
  ηⁱ-preserve-∙⁻¹ = ≤ⁱ-trans (α-monoidal .proj₁) (α-mono η-preserve-∙⁻¹)

  ∙ⁱ-assoc : Associative _≈ⁱ_ _∙ⁱ_
  ∙ⁱ-assoc 𝓕 𝓖 𝓗 =
    begin
      (𝓕 ∙ⁱ 𝓖) ∙ⁱ 𝓗
    ≡⟨⟩
      α (U (α (U 𝓕 ∙ᵖ U 𝓖)) ∙ᵖ U 𝓗)
    ≈⟨ α-cong (∙ᵖ-congˡ (U-cong counit-≈ⁱ)) ⟩
      α (U (α (U 𝓕 ∙ᵖ U 𝓖)) ∙ᵖ U (α (U 𝓗)))
    ≈⟨ α-monoidal ⟩
      α ((U 𝓕 ∙ᵖ U 𝓖) ∙ᵖ U 𝓗)
    ≈⟨ α-cong (∙ᵖ-assoc (U 𝓕) (U 𝓖) (U 𝓗)) ⟩
      α (U 𝓕 ∙ᵖ (U 𝓖 ∙ᵖ U 𝓗))
    ≈⟨ α-monoidal ⟨
      α (U (α (U 𝓕)) ∙ᵖ U (α (U 𝓖 ∙ᵖ U 𝓗)))
    ≈⟨ α-cong (∙ᵖ-congʳ (U-cong counit-≈ⁱ)) ⟨
      α (U 𝓕 ∙ᵖ U (α (U 𝓖 ∙ᵖ U 𝓗)))
    ≡⟨⟩
      𝓕 ∙ⁱ (𝓖 ∙ⁱ 𝓗)
    ∎
    where open SetoidReasoning ≈ⁱ-setoid

  ∙ⁱ-identityˡ : LeftIdentity _≈ⁱ_ εⁱ _∙ⁱ_
  ∙ⁱ-identityˡ 𝓕 =
    begin
      εⁱ ∙ⁱ 𝓕
    ≡⟨⟩
      α (U (α εᵖ) ∙ᵖ U 𝓕)
    ≈⟨ α-cong (∙ᵖ-congˡ (U-cong counit-≈ⁱ)) ⟩
      α (U (α εᵖ) ∙ᵖ U (α (U 𝓕)))
    ≈⟨ α-monoidal ⟩
      α (εᵖ ∙ᵖ U 𝓕)
    ≈⟨ α-cong (∙ᵖ-identityˡ (U 𝓕)) ⟩
      α (U 𝓕)
    ≈⟨ counit-≈ⁱ ⟨
      𝓕
    ∎
    where open SetoidReasoning ≈ⁱ-setoid

  ∙ⁱ-identityʳ : RightIdentity _≈ⁱ_ εⁱ _∙ⁱ_
  ∙ⁱ-identityʳ 𝓕 =
    begin
      𝓕 ∙ⁱ εⁱ
    ≡⟨⟩
      α (U 𝓕 ∙ᵖ U (α εᵖ))
    ≈⟨ α-cong (∙ᵖ-congʳ (U-cong counit-≈ⁱ)) ⟩
      α (U (α (U 𝓕)) ∙ᵖ U (α εᵖ))
    ≈⟨ α-monoidal ⟩
      α (U 𝓕 ∙ᵖ εᵖ)
    ≈⟨ α-cong (∙ᵖ-identityʳ (U 𝓕)) ⟩
      α (U 𝓕)
    ≈⟨ counit-≈ⁱ ⟨
      𝓕
    ∎
    where open SetoidReasoning ≈ⁱ-setoid

  ∙ⁱ-comm : Commutative _≈ⁱ_ _∙ⁱ_
  ∙ⁱ-comm 𝓕 𝓖 = α-cong (∙ᵖ-comm (U 𝓕) (U 𝓖))

  ∙ⁱ-isCommutativePomonoid : IsCommutativePomonoid _≈ⁱ_ _≤ⁱ_ _∙ⁱ_ εⁱ
  ∙ⁱ-isCommutativePomonoid = record
    { isPomonoid = record
      { isPosemigroup = record
        { isPomagma = record
          { isPartialOrder = ≤ⁱ-isPartialOrder
          ; mono = ∙ⁱ-mono
          }
        ; assoc = ∙ⁱ-assoc
        }
      ; identity = ∙ⁱ-identityˡ , ∙ⁱ-identityʳ
      }
      ; comm = ∙ⁱ-comm
    }

  commutativePomonoid : CommutativePomonoid (suc (c ⊔ ℓ₂)) (c ⊔ ℓ₂) (c ⊔ ℓ₂)
  commutativePomonoid =
    record { isCommutativePomonoid = ∙ⁱ-isCommutativePomonoid }

  ------------------------------------------------------------------------------
  -- Residuals

  _⊸ⁱ_ : Ideal → Ideal → Ideal
  (𝓕 ⊸ⁱ 𝓖) .ICarrier x = ∀ {y} → 𝓕 .ICarrier y → 𝓖 .ICarrier (x ∙ y)
  (𝓕 ⊸ⁱ 𝓖) .≤-closed x≤z f 𝓕y = 𝓖 .≤-closed (monoˡ x≤z) (f 𝓕y)
  (𝓕 ⊸ⁱ 𝓖) .+-closed 𝓕⊸𝓖x 𝓕⊸𝓖y {z} 𝓕z =
    𝓖 .≤-closed (distribʳ _ _ _) (𝓖 .+-closed (𝓕⊸𝓖x 𝓕z) (𝓕⊸𝓖y 𝓕z))

  U⊸ⁱ : U (𝓕 ⊸ⁱ 𝓖) ≤ᵖ (U 𝓕 ⇨ᵖ U 𝓖)
  U⊸ⁱ .*≤ᵖ* f = f

  U⊸ⁱ⁻¹ : (U 𝓕 ⇨ᵖ U 𝓖) ≤ᵖ U (𝓕 ⊸ⁱ 𝓖)
  U⊸ⁱ⁻¹ .*≤ᵖ* f = f

  U⊸ⁱ-≈ᵖ : U (𝓕 ⊸ⁱ 𝓖) ≈ᵖ (U 𝓕 ⇨ᵖ U 𝓖)
  U⊸ⁱ-≈ᵖ = (U⊸ⁱ , U⊸ⁱ⁻¹)

  ⊸ⁱ-residual-to : (𝓕 ∙ⁱ 𝓖) ≤ⁱ 𝓗 → 𝓖 ≤ⁱ (𝓕 ⊸ⁱ 𝓗)
  ⊸ⁱ-residual-to 𝓕𝓖≤𝓗 =
    ≤ⁱ-trans counit⁻¹
   (≤ⁱ-trans (α-mono (⇨ᵖ-residual-to (≤ᵖ-trans unit (U-mono 𝓕𝓖≤𝓗))))
   (≤ⁱ-trans (α-mono U⊸ⁱ⁻¹)
             counit))

  ⊸ⁱ-residual-from : 𝓖 ≤ⁱ (𝓕 ⊸ⁱ 𝓗) → (𝓕 ∙ⁱ 𝓖) ≤ⁱ 𝓗
  ⊸ⁱ-residual-from {𝓖} {𝓕} {𝓗} 𝓖≤𝓕⇨𝓗 =
    begin
      𝓕 ∙ⁱ 𝓖
    ≡⟨⟩
      α (U 𝓕 ∙ᵖ U 𝓖)
    ≤⟨ α-mono (⇨ᵖ-residual-from (≤ᵖ-trans (U-mono 𝓖≤𝓕⇨𝓗) U⊸ⁱ)) ⟩
      α (U 𝓗)
    ≈⟨ counit-≈ⁱ ⟨
      𝓗
    ∎
    where open PosetReasoning ≤ⁱ-poset

  ⊸ⁱ-residual : RightResidual _≤ⁱ_ _∙ⁱ_ _⊸ⁱ_
  ⊸ⁱ-residual .Function.Equivalence.to        = ⊸ⁱ-residual-to
  ⊸ⁱ-residual .Function.Equivalence.from      = ⊸ⁱ-residual-from
  ⊸ⁱ-residual .Function.Equivalence.to-cong   = λ { PropEq.refl → PropEq.refl }
  ⊸ⁱ-residual .Function.Equivalence.from-cong = λ { PropEq.refl → PropEq.refl }

  ⊸ⁱ-∙ⁱ-isResiduatedCommutativePomonoid : IsResiduatedCommutativePomonoid _≈ⁱ_ _≤ⁱ_ _∙ⁱ_ _⊸ⁱ_ εⁱ
  ⊸ⁱ-∙ⁱ-isResiduatedCommutativePomonoid = record
    { isCommutativePomonoid = ∙ⁱ-isCommutativePomonoid
    ; residuated = comm∧residual⇒residuated ≤ⁱ-isPreorder ∙ⁱ-comm ⊸ⁱ-residual
    }

module DayDuoidal
    {_∙_} {_◁_} {ε} {ι}
    (isDuoidal : IsDuoidal _≈_ _≤_ _∙_ _◁_ ε ι)
    (comm : Commutative _≈_ _∙_)
    (distrib : _DistributesOver_ _≤_ _∙_ _+_)
    (+-entropy : Entropy _≤_ _+_ _◁_)
    (+-tidy : ι + ι ≤ ι)
  where

  open IsDuoidal isDuoidal

  ∙-isCommutativePomonoid : IsCommutativePomonoid _≈_ _≤_ _∙_ ε
  ∙-isCommutativePomonoid = record
    { isPomonoid = ∙-isPomonoid
    ; comm       = comm
    }

  open DayDistributive ∙-isCommutativePomonoid distrib
  open DayEntropic ◁-isPomonoid +-entropy +-tidy
  open P.LiftIsDuoidal isDuoidal

  ∙ⁱ-◁ⁱ-entropy : Entropy _≤ⁱ_ _∙ⁱ_ _◁ⁱ_
  ∙ⁱ-◁ⁱ-entropy 𝓕₁ 𝓖₁ 𝓕₂ 𝓖₂ =
    begin
      (𝓕₁ ◁ⁱ 𝓖₁) ∙ⁱ (𝓕₂ ◁ⁱ 𝓖₂)
    ≡⟨⟩
      α (U (𝓕₁ ◁ⁱ 𝓖₁) ∙ᵖ U (𝓕₂ ◁ⁱ 𝓖₂))
    ≈⟨ α-cong (∙ᵖ-cong U-monoidal U-monoidal) ⟩
      α ((U 𝓕₁ ◁ᵖ U 𝓖₁) ∙ᵖ (U 𝓕₂ ◁ᵖ U 𝓖₂))
    ≤⟨ α-mono (∙ᵖ-◁ᵖ-entropy (U 𝓕₁) (U 𝓖₁) (U 𝓕₂) (U 𝓖₂)) ⟩
      α ((U 𝓕₁ ∙ᵖ U 𝓕₂) ◁ᵖ (U 𝓖₁ ∙ᵖ U 𝓖₂))
    ≤⟨ α-mono (◁ᵖ-mono unit unit) ⟩
      α (U (α (U 𝓕₁ ∙ᵖ U 𝓕₂)) ◁ᵖ U (α (U 𝓖₁ ∙ᵖ U 𝓖₂)))
    ≈⟨ α-cong U-monoidal ⟨
      α (U (α (U 𝓕₁ ∙ᵖ U 𝓕₂) ◁ⁱ α (U 𝓖₁ ∙ᵖ U 𝓖₂)))
    ≈⟨ counit-≈ⁱ ⟨
      α (U 𝓕₁ ∙ᵖ U 𝓕₂) ◁ⁱ α (U 𝓖₁ ∙ᵖ U 𝓖₂)
    ≡⟨⟩
      (𝓕₁ ∙ⁱ 𝓕₂) ◁ⁱ (𝓖₁ ∙ⁱ 𝓖₂)
    ∎
    where open PosetReasoning ≤ⁱ-poset

  tidy : (c : ctxt ιᵖ) → sum c ≤ ι
  tidy (leaf x (lift x≤ι)) = x≤ι
  tidy (node c d) = ≤-trans (+-mono (tidy c) (tidy d)) +-tidy

  εⁱ≤ιⁱ : εⁱ ≤ⁱ ιⁱ
  εⁱ≤ιⁱ .*≤ⁱ* (t , x≤t) = lift (≤-trans x≤t (≤-trans (ctxt-map-sum εᵖ≤ιᵖ t) (tidy (ctxt-map εᵖ≤ιᵖ t))))

  ∙ⁱ-◁ⁱ-isDuoidal : IsDuoidal _≈ⁱ_ _≤ⁱ_ _∙ⁱ_ _◁ⁱ_ εⁱ ιⁱ
  ∙ⁱ-◁ⁱ-isDuoidal = record
    { ∙-isPomonoid = IsCommutativePomonoid.isPomonoid ∙ⁱ-isCommutativePomonoid
    ; ◁-isPomonoid = ◁ⁱ-isPomonoid
    ; ∙-◁-entropy = ∙ⁱ-◁ⁱ-entropy
    ; ∙-idem-ι = ≤ⁱ-trans (α-mono (∙ᵖ-mono (U-monoidal-ι .proj₁) (U-monoidal-ι .proj₁)))
                (≤ⁱ-trans (α-mono ∙ᵖ-idem-ιᵖ)
                (≤ⁱ-trans (α-mono (U-monoidal-ι .proj₂))
                          counit))
    ; ◁-idem-ε = ≤ⁱ-trans (α-mono ◁ᵖ-idem-εᵖ)
                (≤ⁱ-trans (α-mono (◁ᵖ-mono unit unit))
                (≤ⁱ-trans (α-mono (U-monoidal .proj₂))
                counit))
    ; ε≲ι = εⁱ≤ιⁱ
    }
