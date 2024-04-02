{-# OPTIONS --postfix-projections --safe --without-K --no-exact-split #-}

open import Level
open import Algebra
open import Algebra.Definitions
open import Algebra.Ordered
open import Algebra.Ordered.Definitions
open import Algebra.Ordered.Consequences
import Algebra.Ordered.Construction.LowerSet
open import Algebra.Ordered.Structures.Residuated
open import Algebra.Ordered.Structures.Duoidal
open import Function using (const; flip)
open import Data.Product as Product using (_×_; _,_; -,_; Σ-syntax; ∃; ∃-syntax)
open import Data.Sum as Sum using (_⊎_)
open import Data.Unit as Unit using ()
open import Relation.Binary
open import Relation.Binary.Construct.Core.Symmetric as SymCore using (SymCore)
open import Relation.Binary.Lattice
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
import Relation.Binary.Construct.Flip.EqAndOrd as Flip
open import Relation.Unary using (Pred; _⊆_)
import Relation.Binary.Reasoning.PartialOrder as PosetReasoning
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

module Algebra.Ordered.Construction.Ideal {c ℓ₁ ℓ₂} (pomagma : Pomagma c ℓ₁ ℓ₂) where

private
  module +ᶜ = Pomagma pomagma
  module ≤ᶜ = Poset +ᶜ.poset
  module ≈ᶜ = ≤ᶜ.Eq

open +ᶜ 
  using
    ( Carrier
    ) 
  renaming
    ( _∙_ to _+ᶜ_
    ; _≤_ to _≤ᶜ_
    ; _≈_ to _≈ᶜ_
    )

private
  module L = Algebra.Ordered.Construction.LowerSet +ᶜ.poset

open L using
  ( LowerSet
  ; ICarrier
  ; ≤-closed
  ; _≤_
  ; *≤*
  ; ≤-refl
  ; ≤-trans
  ; _≈_
  ; η
  ; η-mono
  ; _∨_
  ; inj₁
  ; inj₂
  ; [_,_]
  )

private
  variable
    w x y z : Carrier
    ℓx ℓy ℓz : Level
    X : Pred Carrier ℓx
    Y : Pred Carrier ℓy
    Z : Pred Carrier ℓz
    F F₁ F₂ : LowerSet
    G G₁ G₂ : LowerSet
    H H₁ H₂ : LowerSet

record Ideal : Set (suc (c ⊔ ℓ₂)) where
  no-eta-equality
  field
    ICarrier : Carrier → Set (c ⊔ ℓ₂)
    ≤-closed : x ≤ᶜ y → ICarrier y → ICarrier x
    +-closed : ICarrier x → ICarrier y → ICarrier (x +ᶜ y)
open Ideal public

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
open _≤ⁱ_ public

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
    ; reflexive  to ≤ⁱ-reflexive
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
U : Ideal → LowerSet
U 𝓕 .ICarrier = 𝓕 .ICarrier
U 𝓕 .≤-closed = 𝓕 .≤-closed

U-mono : 𝓕 ≤ⁱ 𝓖 → U 𝓕 ≤ U 𝓖
U-mono 𝓕≤𝓖 .*≤* = 𝓕≤𝓖 .*≤ⁱ*

U-cong : 𝓕 ≈ⁱ 𝓖 → U 𝓕 ≈ U 𝓖
U-cong (𝓖≤𝓕 , 𝓕≤𝓖) = U-mono 𝓖≤𝓕 , U-mono 𝓕≤𝓖

------------------------------------------------------------------------------
-- Turn a lower set into an ideal by closing under +

data Tree (F : LowerSet) : Set (c ⊔ ℓ₂) where
  leaf : (x : Carrier) → F .ICarrier x → Tree F
  node : Tree F → Tree F → Tree F

sum : Tree F → Carrier
sum (leaf x _) = x
sum (node c d) = sum c +ᶜ sum d

mapᵗ : F ≤ G → Tree F → Tree G
mapᵗ F≤G (leaf x Fx) = leaf x (F≤G .*≤* Fx)
mapᵗ F≤G (node c d)  = node (mapᵗ F≤G c) (mapᵗ F≤G d)

map-sumᵗ : (F≤G : F ≤ G) (c : Tree F) → sum c ≤ᶜ sum (mapᵗ F≤G c)
map-sumᵗ F≤G (leaf x Fx) = ≤ᶜ.refl
map-sumᵗ F≤G (node c d) = +ᶜ.mono (map-sumᵗ F≤G c) (map-sumᵗ F≤G d)

α : LowerSet → Ideal
α F .ICarrier x = Σ[ t ∈ Tree F ] (x ≤ᶜ sum t)
α F .≤-closed x≤y (t , y≤t) = t , ≤ᶜ.trans x≤y y≤t
α F .+-closed (s , x≤s) (t , y≤t) = node s t , +ᶜ.mono x≤s y≤t

α-mono : F ≤ G → α F ≤ⁱ α G
α-mono F≤G .*≤ⁱ* (t , x≤t) = mapᵗ F≤G t , ≤ᶜ.trans x≤t (map-sumᵗ F≤G t)

α-cong : ∀ {F G} → F ≈ G → α F ≈ⁱ α G
α-cong (G≤F , F≤G) = (α-mono G≤F , α-mono F≤G)

------------------------------------------------------------------------------
ηⁱ : Carrier → Ideal
ηⁱ x = α (η x)

ηⁱ-mono : x ≤ᶜ y → ηⁱ x ≤ⁱ ηⁱ y
ηⁱ-mono x≤y = α-mono (η-mono x≤y)

------------------------------------------------------------------------------
-- U and α form a Galois connection

ideal-Tree-closed : (t : Tree (U 𝓕)) → 𝓕 .ICarrier (sum t)
ideal-Tree-closed {𝓕} (leaf x ϕ) = ϕ
ideal-Tree-closed {𝓕} (node c d) = 𝓕 .+-closed (ideal-Tree-closed c) (ideal-Tree-closed d)

counit : α (U 𝓕) ≤ⁱ 𝓕
counit {𝓕} .*≤ⁱ* (t , x≤t) = 𝓕 .≤-closed x≤t (ideal-Tree-closed t)

counit⁻¹ : 𝓕 ≤ⁱ α (U 𝓕)
counit⁻¹ .*≤ⁱ* 𝓕x = leaf _ 𝓕x , ≤ᶜ.refl

counit-≈ⁱ : 𝓕 ≈ⁱ α (U 𝓕)
counit-≈ⁱ = counit⁻¹ , counit

unit : F ≤ U (α F)
unit .*≤* Fx = leaf _ Fx , ≤ᶜ.refl

------------------------------------------------------------------------------
-- Binary meets

_∧ⁱ_ : Ideal → Ideal → Ideal
(𝓕 ∧ⁱ 𝓖) .ICarrier x = 𝓕 .ICarrier x × 𝓖 .ICarrier x
(𝓕 ∧ⁱ 𝓖) .≤-closed x≤y (𝓕y , 𝓖y) = 𝓕 .≤-closed x≤y 𝓕y , 𝓖 .≤-closed x≤y 𝓖y
(𝓕 ∧ⁱ 𝓖) .+-closed (𝓕x , 𝓖x) (𝓕y , 𝓖y) = (𝓕 .+-closed 𝓕x 𝓕y) , (𝓖 .+-closed 𝓖x 𝓖y)

proj₁ⁱ : (𝓕 ∧ⁱ 𝓖) ≤ⁱ 𝓕
proj₁ⁱ .*≤ⁱ* = Product.proj₁

proj₂ⁱ : (𝓕 ∧ⁱ 𝓖) ≤ⁱ 𝓖
proj₂ⁱ .*≤ⁱ* = Product.proj₂

⟨_,_⟩ⁱ : 𝓕 ≤ⁱ 𝓖 → 𝓕 ≤ⁱ 𝓗 → 𝓕 ≤ⁱ (𝓖 ∧ⁱ 𝓗)
⟨ 𝓗≤𝓕 , 𝓗≤𝓖 ⟩ⁱ .*≤ⁱ* = Product.< 𝓗≤𝓕 .*≤ⁱ* , 𝓗≤𝓖 .*≤ⁱ* >

∧ⁱ-isMeetSemilattice : IsMeetSemilattice _≈ⁱ_ _≤ⁱ_ _∧ⁱ_
∧ⁱ-isMeetSemilattice = record
  { isPartialOrder = ≤ⁱ-isPartialOrder
  ; infimum        = λ 𝓕 𝓖 → (proj₁ⁱ ,  proj₂ⁱ , λ 𝓗 → ⟨_,_⟩ⁱ)
  }

-- FIXME: under what conditions does α preserve meets?

------------------------------------------------------------------------------
-- Binary joins

_∨ⁱ_ : Ideal → Ideal → Ideal
𝓕 ∨ⁱ 𝓖 = α (U 𝓕 ∨ U 𝓖)

inj₁ⁱ : 𝓕 ≤ⁱ (𝓕 ∨ⁱ 𝓖)
inj₁ⁱ = ≤ⁱ-trans counit⁻¹ (α-mono inj₁)

inj₂ⁱ : 𝓖 ≤ⁱ (𝓕 ∨ⁱ 𝓖)
inj₂ⁱ = ≤ⁱ-trans counit⁻¹ (α-mono inj₂)

[_,_]ⁱ : 𝓕 ≤ⁱ 𝓗 → 𝓖 ≤ⁱ 𝓗 → (𝓕 ∨ⁱ 𝓖) ≤ⁱ 𝓗
[_,_]ⁱ {𝓕} {𝓗} {𝓖} 𝓕≤𝓗 𝓖≤𝓗 .*≤ⁱ* (t , x≤t) =
  𝓗 .≤-closed (≤ᶜ.trans x≤t (map-sumᵗ _ t)) (ideal-Tree-closed (mapᵗ [ U-mono 𝓕≤𝓗 , U-mono 𝓖≤𝓗 ] t))

∨ⁱ-isJoinSemilattice : IsJoinSemilattice _≈ⁱ_ _≤ⁱ_ _∨ⁱ_
∨ⁱ-isJoinSemilattice = record
  { isPartialOrder = ≤ⁱ-isPartialOrder
  ; supremum       = λ 𝓕 𝓖 → (inj₁ⁱ , inj₂ⁱ , λ 𝓗 → [_,_]ⁱ)
  }


hulp : (c : Tree (η (x +ᶜ y))) → Σ[ d ∈ Tree (U (α (η x) ∨ⁱ α (η y))) ] (sum c ≤ᶜ sum d)
hulp {x}{y} (leaf z (lift z≤x+y)) =
  (node (leaf x (inj₁ⁱ .*≤ⁱ* ((leaf x (lift ≤ᶜ.refl)) , ≤ᶜ.refl)))
        (leaf y (inj₂ⁱ .*≤ⁱ* ((leaf y (lift ≤ᶜ.refl)) , ≤ᶜ.refl)))) ,
  z≤x+y
hulp (node c₁ c₂) =
  let (d₁ , c₁≤d₁) , (d₂ , c₂≤d₂) = hulp c₁ , hulp c₂
  in node d₁ d₂ , +ᶜ.mono c₁≤d₁ c₂≤d₂

η-preserve-∨ⁱ : α (η (x +ᶜ y)) ≤ⁱ α (η x) ∨ⁱ α (η y)
η-preserve-∨ⁱ {x}{y} .*≤ⁱ* {z} (c , z≤c) =
  let d , c≤d = hulp c in down-closed (≤ᶜ.trans z≤c c≤d) (ideal-Tree-closed d)
  where open Ideal (α (η x) ∨ⁱ α (η y)) renaming (≤-closed to down-closed)


------------------------------------------------------------------------------
module DayEntropic
    {_∙ᶜ_}
    {εᶜ}
    (isPomonoid : IsPomonoid _≈ᶜ_ _≤ᶜ_ _∙ᶜ_ εᶜ)
    (+-entropy : Entropy _≤ᶜ_ _+ᶜ_ _∙ᶜ_)
    (+-tidy    : εᶜ +ᶜ εᶜ ≤ᶜ εᶜ)
    where

  private
    module LMon = L.LiftIsPomonoid isPomonoid

  _◁ⁱ_ : Ideal → Ideal → Ideal
  (𝓕 ◁ⁱ 𝓖) .ICarrier x =
    ∃[ y ] ∃[ z ] (x ≤ᶜ (y ∙ᶜ z) × 𝓕 .ICarrier y × 𝓖 .ICarrier z)
  (𝓕 ◁ⁱ 𝓖) .≤-closed x≤w (y , z , w≤yz , 𝓕y , 𝓖z) =
    (-, -, ≤ᶜ.trans x≤w w≤yz , 𝓕y , 𝓖z)
  (𝓕 ◁ⁱ 𝓖) .+-closed (y₁ , z₁ , x₁≤y₁z₁ , ϕ₁ , ψ₁) (y₂ , z₂ , x₂≤y₂z₂ , ϕ₂ , ψ₂) =
    y₁ +ᶜ y₂ , z₁ +ᶜ z₂ ,
    ≤ᶜ.trans (+ᶜ.mono x₁≤y₁z₁ x₂≤y₂z₂) (+-entropy _ _ _ _) ,
    𝓕 .+-closed ϕ₁ ϕ₂ ,
    𝓖 .+-closed ψ₁ ψ₂

  ιⁱ : Ideal
  ιⁱ .ICarrier x = Lift c (x ≤ᶜ εᶜ)
  ιⁱ .≤-closed x≤y (lift y≤ε) = lift (≤ᶜ.trans x≤y y≤ε)
  ιⁱ .+-closed (lift x≤ε) (lift y≤ε) = lift (≤ᶜ.trans (+ᶜ.mono x≤ε y≤ε) +-tidy)

  ◁ⁱ-mono : Monotonic₂ _≤ⁱ_ _≤ⁱ_ _≤ⁱ_ _◁ⁱ_
  ◁ⁱ-mono 𝓕₁≤𝓖₁ 𝓕₂≤𝓖₂ .*≤ⁱ* = LMon.∙-mono (U-mono 𝓕₁≤𝓖₁) (U-mono 𝓕₂≤𝓖₂) .*≤*

  ◁ⁱ-assoc : Associative _≈ⁱ_ _◁ⁱ_
  ◁ⁱ-assoc 𝓕 𝓖 𝓗 .Product.proj₁ .*≤ⁱ* = LMon.∙-assoc (U 𝓕) (U 𝓖) (U 𝓗) .Product.proj₁ .*≤*
  ◁ⁱ-assoc 𝓕 𝓖 𝓗 .Product.proj₂ .*≤ⁱ* = LMon.∙-assoc (U 𝓕) (U 𝓖) (U 𝓗) .Product.proj₂ .*≤*

  ◁ⁱ-identityˡ : LeftIdentity _≈ⁱ_ ιⁱ _◁ⁱ_
  ◁ⁱ-identityˡ 𝓕 .Product.proj₁ .*≤ⁱ* = LMon.∙-identityˡ (U 𝓕) .Product.proj₁ .*≤*
  ◁ⁱ-identityˡ 𝓕 .Product.proj₂ .*≤ⁱ* = LMon.∙-identityˡ (U 𝓕) .Product.proj₂ .*≤*

  ◁ⁱ-identityʳ : RightIdentity _≈ⁱ_ ιⁱ _◁ⁱ_
  ◁ⁱ-identityʳ 𝓕 .Product.proj₁ .*≤ⁱ* = LMon.∙-identityʳ (U 𝓕) .Product.proj₁ .*≤*
  ◁ⁱ-identityʳ 𝓕 .Product.proj₂ .*≤ⁱ* = LMon.∙-identityʳ (U 𝓕) .Product.proj₂ .*≤*

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

  U-monoidal : U (𝓕 ◁ⁱ 𝓖) ≈ (U 𝓕 LMon.∙ U 𝓖)
  U-monoidal .Product.proj₁ .*≤* 𝓕x = 𝓕x
  U-monoidal .Product.proj₂ .*≤* 𝓕x = 𝓕x

  U-monoidal-ι : U ιⁱ ≈ LMon.ε
  U-monoidal-ι .Product.proj₁ .*≤* x≤ε = x≤ε
  U-monoidal-ι .Product.proj₂ .*≤* x≤ε = x≤ε

  ηⁱ-preserve-◁ : ηⁱ (x ∙ᶜ y) ≤ⁱ ηⁱ x ◁ⁱ ηⁱ y
  ηⁱ-preserve-◁ {x} {y} .*≤ⁱ* {z} (c , z≤c) =
    down-closed
      (≤ᶜ.trans z≤c (map-sumᵗ _ c))
      (ideal-Tree-closed {α (η x) ◁ⁱ α (η y)} 
        (mapᵗ 
          (≤-trans LMon.η-preserve-∙ 
            (≤-trans (LMon.∙-mono unit unit) (U-monoidal .Product.proj₂))) c))
    where
      open Ideal (α (η x) ◁ⁱ α (η y)) renaming (≤-closed to down-closed)

{-
  -- FIXME: this doesn't work
  module _ (idem : ∀ {x} → x +ᶜ x ≤ᶜ x) where

    open IsPomonoid isPomonoid using (mono)

    -- FIXME: this is the same combination function as below
    _∙ᶜ'_ : Tree F → Tree G → Tree (F LMon.∙ G)
    leaf x Fx  ∙ᶜ' leaf y Gy  = leaf (x ∙ᶜ y) (x , y , ≤ᶜ.refl , Fx , Gy)
    leaf x Fx  ∙ᶜ' node d₁ d₂ = node (leaf x Fx ∙ᶜ' d₁) (leaf x Fx ∙ᶜ' d₂)
    node c₁ c₂ ∙ᶜ' d          = node (c₁ ∙ᶜ' d) (c₂ ∙ᶜ' d)

    ∙ᵗ-sum : (c : Tree F)(d : Tree G) → sum (c ∙ᶜ' d) ≤ᶜ sum c ∙ᶜ sum d
    ∙ᵗ-sum (leaf x Fx)  (leaf y Gy)  = ≤ᶜ.refl
    ∙ᵗ-sum (leaf x Fx)  (node d₁ d₂) =
       ≤ᶜ.trans (+ᶜ.mono (∙ᵗ-sum (leaf x Fx) d₁) (∙ᵗ-sum (leaf x Fx) d₂))
      (≤ᶜ.trans (+-entropy _ _ _ _)
               (mono idem ≤ᶜ.refl))
    ∙ᵗ-sum (node c₁ c₂) d =
      ≤ᶜ.trans (+ᶜ.mono (∙ᵗ-sum c₁ d) (∙ᵗ-sum c₂ d))
      (≤ᶜ.trans (+-entropy _ _ _ _)
      (mono ≤ᶜ.refl idem))

    ηⁱ-preserve-◁⁻¹ : α (η x) ◁ⁱ α (η y) ≤ⁱ α (η (x ∙ᶜ y))
    ηⁱ-preserve-◁⁻¹ {x}{y} .*≤ⁱ* {z} (z₁ , z₂ , z≤z₁z₂ , (c₁ , z₁≤c) , (c₂ , z₂≤c)) =
      mapᵗ η-preserve-∙⁻¹ (c₁ ∙ᶜ' c₂) ,
      ≤ᶜ.trans z≤z₁z₂ {!!}
-}

module DayDistributive
    {_∙ᶜ_}
    {εᶜ}
    (isCommutativePomonoid : IsCommutativePomonoid _≈ᶜ_ _≤ᶜ_ _∙ᶜ_ εᶜ)
    (distrib : _DistributesOver_ _≤ᶜ_ _∙ᶜ_ _+ᶜ_)
  where

  private
    module Mon = IsCommutativePomonoid isCommutativePomonoid
    module LMon = L.LiftIsCommutativePomonoid isCommutativePomonoid

  distribˡ = distrib .Product.proj₁
  distribʳ = distrib .Product.proj₂

  _∙ⁱ_ : Ideal → Ideal → Ideal
  𝓕 ∙ⁱ 𝓖 = α (U 𝓕 LMon.∙ U 𝓖)

  εⁱ : Ideal
  εⁱ = α LMon.ε

  _∙ᵗ_ : Tree F → Tree G → Tree (F LMon.∙ G)
  leaf x Fx  ∙ᵗ leaf y Gy  = leaf (x ∙ᶜ y) (x , y , ≤ᶜ.refl , Fx , Gy)
  leaf x Fx  ∙ᵗ node d₁ d₂ = node (leaf x Fx ∙ᵗ d₁) (leaf x Fx ∙ᵗ d₂)
  node c₁ c₂ ∙ᵗ d          = node (c₁ ∙ᵗ d) (c₂ ∙ᵗ d)

  ∙ᵗ-sum : (c : Tree F)(d : Tree G) → sum c ∙ᶜ sum d ≤ᶜ sum (c ∙ᵗ d)
  ∙ᵗ-sum (leaf x Fx)  (leaf y Gy)  = ≤ᶜ.refl
  ∙ᵗ-sum (leaf x Fx)  (node d₁ d₂) = ≤ᶜ.trans (distribˡ _ _ _) (+ᶜ.mono (∙ᵗ-sum (leaf x Fx) d₁) (∙ᵗ-sum (leaf x Fx) d₂))
  ∙ᵗ-sum (node c₁ c₂) d            = ≤ᶜ.trans (distribʳ _ _ _) (+ᶜ.mono (∙ᵗ-sum c₁ d) (∙ᵗ-sum c₂ d))

  α-helper : (c : Tree (U (α F) LMon.∙ U (α G))) → x ≤ᶜ sum c → Σ[ d ∈ Tree (F LMon.∙ G) ] (x ≤ᶜ sum d)
  α-helper (leaf y (y₁ , y₂ , y≤y₁y₂ , (c , y₁≤c) , (d , y₂≤d))) x≤y =
    (c ∙ᵗ d) , ≤ᶜ.trans x≤y (≤ᶜ.trans y≤y₁y₂ (≤ᶜ.trans (Mon.mono y₁≤c y₂≤d) (∙ᵗ-sum c d)))
  α-helper (node c d) x≤cd =
    let (c' , c≤c') , (d' , d≤d') = α-helper c ≤ᶜ.refl , α-helper d ≤ᶜ.refl
    in (node c' d') , (≤ᶜ.trans x≤cd (+ᶜ.mono c≤c' d≤d'))

  α-monoidal : (α F ∙ⁱ α G) ≈ⁱ α (F LMon.∙ G)
  α-monoidal .Product.proj₁ .*≤ⁱ* (c , x≤c)  = α-helper c x≤c
  α-monoidal .Product.proj₂ = α-mono (LMon.∙-mono unit unit)

  ∙ⁱ-mono : Monotonic₂ _≤ⁱ_ _≤ⁱ_ _≤ⁱ_ _∙ⁱ_
  ∙ⁱ-mono 𝓕₁≤𝓕₂ 𝓖₁≤𝓖₂ = α-mono (LMon.∙-mono (U-mono 𝓕₁≤𝓕₂) (U-mono 𝓖₁≤𝓖₂))

  ηⁱ-preserve-∙ : ηⁱ (x ∙ᶜ y) ≤ⁱ ηⁱ x ∙ⁱ ηⁱ y
  ηⁱ-preserve-∙ = α-mono (≤-trans LMon.η-preserve-∙ (LMon.∙-mono unit unit))

  ηⁱ-preserve-∙⁻¹ : ηⁱ x ∙ⁱ ηⁱ y ≤ⁱ ηⁱ (x ∙ᶜ y)
  ηⁱ-preserve-∙⁻¹ = ≤ⁱ-trans (α-monoidal .Product.proj₁) (α-mono LMon.η-preserve-∙⁻¹)

  ∙ⁱ-assoc : Associative _≈ⁱ_ _∙ⁱ_
  ∙ⁱ-assoc 𝓕 𝓖 𝓗 =
    begin
      (𝓕 ∙ⁱ 𝓖) ∙ⁱ 𝓗
    ≡⟨⟩
      α (U (α (U 𝓕 LMon.∙ U 𝓖)) LMon.∙ U 𝓗)
    ≈⟨ α-cong (LMon.∙-congˡ (U-cong counit-≈ⁱ)) ⟩
      α (U (α (U 𝓕 LMon.∙ U 𝓖)) LMon.∙ U (α (U 𝓗)))
    ≈⟨ α-monoidal ⟩
      α ((U 𝓕 LMon.∙ U 𝓖) LMon.∙ U 𝓗)
    ≈⟨ α-cong (LMon.∙-assoc (U 𝓕) (U 𝓖) (U 𝓗)) ⟩
      α (U 𝓕 LMon.∙ (U 𝓖 LMon.∙ U 𝓗))
    ≈⟨ α-monoidal ⟨
      α (U (α (U 𝓕)) LMon.∙ U (α (U 𝓖 LMon.∙ U 𝓗)))
    ≈⟨ α-cong (LMon.∙-congʳ (U-cong counit-≈ⁱ)) ⟨
      α (U 𝓕 LMon.∙ U (α (U 𝓖 LMon.∙ U 𝓗)))
    ≡⟨⟩
      𝓕 ∙ⁱ (𝓖 ∙ⁱ 𝓗)
    ∎
    where open SetoidReasoning ≈ⁱ-setoid

  ∙ⁱ-identityˡ : LeftIdentity _≈ⁱ_ εⁱ _∙ⁱ_
  ∙ⁱ-identityˡ 𝓕 =
    begin
      εⁱ ∙ⁱ 𝓕
    ≡⟨⟩
      α (U (α LMon.ε) LMon.∙ U 𝓕)
    ≈⟨ α-cong (LMon.∙-congˡ (U-cong counit-≈ⁱ)) ⟩
      α (U (α LMon.ε) LMon.∙ U (α (U 𝓕)))
    ≈⟨ α-monoidal ⟩
      α (LMon.ε LMon.∙ U 𝓕)
    ≈⟨ α-cong (LMon.∙-identityˡ (U 𝓕)) ⟩
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
      α (U 𝓕 LMon.∙ U (α LMon.ε))
    ≈⟨ α-cong (LMon.∙-congʳ (U-cong counit-≈ⁱ)) ⟩
      α (U (α (U 𝓕)) LMon.∙ U (α LMon.ε))
    ≈⟨ α-monoidal ⟩
      α (U 𝓕 LMon.∙ LMon.ε)
    ≈⟨ α-cong (LMon.∙-identityʳ (U 𝓕)) ⟩
      α (U 𝓕)
    ≈⟨ counit-≈ⁱ ⟨
      𝓕
    ∎
    where open SetoidReasoning ≈ⁱ-setoid

  ∙ⁱ-comm : Commutative _≈ⁱ_ _∙ⁱ_
  ∙ⁱ-comm 𝓕 𝓖 = α-cong (LMon.∙-comm (U 𝓕) (U 𝓖))

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
  commutativePomonoid = record
    { isCommutativePomonoid = ∙ⁱ-isCommutativePomonoid }

  ------------------------------------------------------------------------------
  -- Residuals

  _⊸ⁱ_ : Ideal → Ideal → Ideal
  (𝓕 ⊸ⁱ 𝓖) .ICarrier x = ∀ {y} → 𝓕 .ICarrier y → 𝓖 .ICarrier (x ∙ᶜ y)
  (𝓕 ⊸ⁱ 𝓖) .≤-closed x≤z f 𝓕y = 𝓖 .≤-closed (Mon.monoˡ x≤z) (f 𝓕y)
  (𝓕 ⊸ⁱ 𝓖) .+-closed 𝓕⊸𝓖x 𝓕⊸𝓖y {z} 𝓕z =
    𝓖 .≤-closed (distribʳ _ _ _) (𝓖 .+-closed (𝓕⊸𝓖x 𝓕z) (𝓕⊸𝓖y 𝓕z))

  U⊸ⁱ : U (𝓕 ⊸ⁱ 𝓖) ≤ (U 𝓕 LMon.⊸ U 𝓖)
  U⊸ⁱ .*≤* f = f

  U⊸ⁱ⁻¹ : (U 𝓕 LMon.⊸ U 𝓖) ≤ U (𝓕 ⊸ⁱ 𝓖)
  U⊸ⁱ⁻¹ .*≤* f = f

  U⊸ⁱ-≈ : U (𝓕 ⊸ⁱ 𝓖) ≈ (U 𝓕 LMon.⊸ U 𝓖)
  U⊸ⁱ-≈ = (U⊸ⁱ , U⊸ⁱ⁻¹)

  ⊸ⁱ-residual-to : (𝓕 ∙ⁱ 𝓖) ≤ⁱ 𝓗 → 𝓖 ≤ⁱ (𝓕 ⊸ⁱ 𝓗)
  ⊸ⁱ-residual-to 𝓕𝓖≤𝓗 =
    ≤ⁱ-trans counit⁻¹
   (≤ⁱ-trans (α-mono (LMon.⊸-residual-to (≤-trans unit (U-mono 𝓕𝓖≤𝓗))))
   (≤ⁱ-trans (α-mono U⊸ⁱ⁻¹)
             counit))

  ⊸ⁱ-residual-from : 𝓖 ≤ⁱ (𝓕 ⊸ⁱ 𝓗) → (𝓕 ∙ⁱ 𝓖) ≤ⁱ 𝓗
  ⊸ⁱ-residual-from {𝓖} {𝓕} {𝓗} 𝓖≤𝓕⊸𝓗 =
    begin
      𝓕 ∙ⁱ 𝓖
    ≡⟨⟩
      α (U 𝓕 LMon.∙ U 𝓖)
    ≤⟨ α-mono (LMon.⊸-residual-from (≤-trans (U-mono 𝓖≤𝓕⊸𝓗) U⊸ⁱ)) ⟩
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
    {_∙ᶜ_} 
    {_◁ᶜ_} 
    {εᶜ}
    {ιᶜ}
    (isCommutativeDuoidal : IsCommutativeDuoidal _≈ᶜ_ _≤ᶜ_ _∙ᶜ_ _◁ᶜ_ εᶜ ιᶜ)
    (distrib : _DistributesOver_ _≤ᶜ_ _∙ᶜ_ _+ᶜ_)
    (+ᶜ-entropy : Entropy _≤ᶜ_ _+ᶜ_ _◁ᶜ_)
    (+ᶜ-tidy : ιᶜ +ᶜ ιᶜ ≤ᶜ ιᶜ)
  where

  private
    module Duo = IsCommutativeDuoidal isCommutativeDuoidal
    module LDuo = L.LiftIsDuoidal Duo.isDuoidal

  open DayDistributive Duo.∙-isCommutativePomonoid distrib
  open DayEntropic Duo.◁-isPomonoid +ᶜ-entropy +ᶜ-tidy

  ∙ⁱ-◁ⁱ-entropy : Entropy _≤ⁱ_ _∙ⁱ_ _◁ⁱ_
  ∙ⁱ-◁ⁱ-entropy 𝓕₁ 𝓖₁ 𝓕₂ 𝓖₂ =
    begin
      (𝓕₁ ◁ⁱ 𝓖₁) ∙ⁱ (𝓕₂ ◁ⁱ 𝓖₂)
    ≡⟨⟩
      α (U (𝓕₁ ◁ⁱ 𝓖₁) LDuo.∙ U (𝓕₂ ◁ⁱ 𝓖₂))
    ≈⟨ α-cong (LDuo.∙-cong U-monoidal U-monoidal) ⟩
      α ((U 𝓕₁ LDuo.◁ U 𝓖₁) LDuo.∙ (U 𝓕₂ LDuo.◁ U 𝓖₂))
    ≤⟨ α-mono (LDuo.∙-◁-entropy (U 𝓕₁) (U 𝓖₁) (U 𝓕₂) (U 𝓖₂)) ⟩
      α ((U 𝓕₁ LDuo.∙ U 𝓕₂) LDuo.◁ (U 𝓖₁ LDuo.∙ U 𝓖₂))
    ≤⟨ α-mono (LDuo.◁-mono unit unit) ⟩
      α (U (α (U 𝓕₁ LDuo.∙ U 𝓕₂)) LDuo.◁ U (α (U 𝓖₁ LDuo.∙ U 𝓖₂)))
    ≈⟨ α-cong U-monoidal ⟨
      α (U (α (U 𝓕₁ LDuo.∙ U 𝓕₂) ◁ⁱ α (U 𝓖₁ LDuo.∙ U 𝓖₂)))
    ≈⟨ counit-≈ⁱ ⟨
      α (U 𝓕₁ LDuo.∙ U 𝓕₂) ◁ⁱ α (U 𝓖₁ LDuo.∙ U 𝓖₂)
    ≡⟨⟩
      (𝓕₁ ∙ⁱ 𝓕₂) ◁ⁱ (𝓖₁ ∙ⁱ 𝓖₂)
    ∎
    where open PosetReasoning ≤ⁱ-poset

  tidy : (c : Tree LDuo.ι) → sum c ≤ᶜ ιᶜ
  tidy (leaf x (lift x≤ι)) = x≤ι
  tidy (node c d) = ≤ᶜ.trans (+ᶜ.mono (tidy c) (tidy d)) +ᶜ-tidy

  εⁱ≤ιⁱ : εⁱ ≤ⁱ ιⁱ
  εⁱ≤ιⁱ .*≤ⁱ* (t , x≤t) = lift (≤ᶜ.trans x≤t (≤ᶜ.trans (map-sumᵗ LDuo.ε≤ι t) (tidy (mapᵗ LDuo.ε≤ι t))))

  ∙ⁱ-◁ⁱ-isDuoidal : IsDuoidal _≈ⁱ_ _≤ⁱ_ _∙ⁱ_ _◁ⁱ_ εⁱ ιⁱ
  ∙ⁱ-◁ⁱ-isDuoidal = record
    { ∙-isPomonoid = IsCommutativePomonoid.isPomonoid ∙ⁱ-isCommutativePomonoid
    ; ◁-isPomonoid = ◁ⁱ-isPomonoid
    ; ∙-◁-entropy = ∙ⁱ-◁ⁱ-entropy
    ; ∙-idem-ι = ≤ⁱ-trans (α-mono (LDuo.∙-mono (U-monoidal-ι .Product.proj₁) (U-monoidal-ι .Product.proj₁)))
                (≤ⁱ-trans (α-mono LDuo.∙-idem-ι)
                (≤ⁱ-trans (α-mono (U-monoidal-ι .Product.proj₂))
                          counit))
    ; ◁-idem-ε = ≤ⁱ-trans (α-mono LDuo.◁-idem-ε)
                (≤ⁱ-trans (α-mono (LDuo.◁-mono unit unit))
                (≤ⁱ-trans (α-mono (U-monoidal .Product.proj₂))
                counit))
    ; ε≲ι = εⁱ≤ιⁱ
    }
 