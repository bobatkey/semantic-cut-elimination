{-# OPTIONS --postfix-projections --safe --without-K --no-exact-split #-}

open import Level
open import Algebra
open import Algebra.Ordered
open import Algebra.Ordered.Consequences
import Algebra.Ordered.Construction.LowerSet
open import Function using (const; flip)
open import Function.EquiInhabited using (_↔_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; <_,_>; -,_; Σ-syntax; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
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
  module C = Pomagma pomagma

open C 
  using
    ( Carrier
    ) 
  renaming
    ( _∙_ to _∨ᶜ_
    ; _≤_ to _≤ᶜ_
    ; _≈_ to _≈ᶜ_
    )

private
  module L = Algebra.Ordered.Construction.LowerSet C.poset

open L using (LowerSet)

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
    ∨-closed : ICarrier x → ICarrier y → ICarrier (x ∨ᶜ y)
open Ideal public

private
  variable
    I I₁ I₂ : Ideal
    J J₁ J₂ : Ideal
    K K₁ K₂ : Ideal

infix 4 _≤_

record _≤_ (I J : Ideal) : Set (c ⊔ ℓ₂) where
  no-eta-equality
  field
    *≤* : I .ICarrier ⊆ J .ICarrier
open _≤_ public

infix 4 _≈_

_≈_ : Ideal → Ideal → Set (c ⊔ ℓ₂)
_≈_ = SymCore _≤_

≤-refl : I ≤ I
≤-refl .*≤* Ix = Ix

≤-trans : I ≤ J → J ≤ K → I ≤ K
≤-trans I≤J J≤K .*≤* z = J≤K .*≤* (I≤J .*≤* z)

-- FIXME: get rid of the propositional equality here
≤-isPartialOrder : IsPartialOrder _≈_ _≤_
≤-isPartialOrder = SymCore.isPreorder⇒isPartialOrder _≤_ ≡-≤-isPreorder
  where
    ≡-≤-isPreorder : IsPreorder _≡_ _≤_
    ≡-≤-isPreorder = record
      { isEquivalence = PropEq.isEquivalence
      ; reflexive = λ { PropEq.refl → ≤-refl }
      ; trans = ≤-trans
      }

open IsPartialOrder ≤-isPartialOrder
  using
    ( module Eq
    )
  renaming
    ( ≤-respˡ-≈  to ≤-respˡ-≈
    ; reflexive  to ≤-reflexive
    ; isPreorder to ≤-isPreorder
    )
  public

≤-poset : Poset _ _ _
≤-poset = record
  { isPartialOrder = ≤-isPartialOrder
  }

≈-setoid : Setoid _ _
≈-setoid = record
  { isEquivalence = Poset.isEquivalence ≤-poset
  }

------------------------------------------------------------------------------
-- From ideals to lower sets
U : Ideal → LowerSet
U I .L.ICarrier = I .ICarrier
U I .L.≤-closed = I .≤-closed

U-mono : I ≤ J → U I L.≤ U J
U-mono I≤J .L.*≤* = I≤J .*≤*

U-cong : I ≈ J → U I L.≈ U J
U-cong (J≤I , I≤J) = U-mono J≤I , U-mono I≤J

------------------------------------------------------------------------------
-- Turn a lower set into an ideal by closing under ∨

data `⋁ (F : LowerSet) : Set (c ⊔ ℓ₂) where
  leaf : (x : Carrier) → F .L.ICarrier x → `⋁ F
  node : `⋁ F → `⋁ F → `⋁ F

`⋁-eval : `⋁ F → Carrier
`⋁-eval (leaf x _) = x
`⋁-eval (node c d) = `⋁-eval c ∨ᶜ `⋁-eval d

`⋁-map : F L.≤ G → `⋁ F → `⋁ G
`⋁-map F≤G (leaf x Fx) = leaf x (F≤G .L.*≤* Fx)
`⋁-map F≤G (node c d)  = node (`⋁-map F≤G c) (`⋁-map F≤G d)

`⋁-map-eval : (F≤G : F L.≤ G) (c : `⋁ F) → `⋁-eval c ≤ᶜ `⋁-eval (`⋁-map F≤G c)
`⋁-map-eval F≤G (leaf x Fx) = C.refl
`⋁-map-eval F≤G (node c d) = C.mono (`⋁-map-eval F≤G c) (`⋁-map-eval F≤G d)

α : LowerSet → Ideal
α F .ICarrier x = Σ[ t ∈ `⋁ F ] (x ≤ᶜ `⋁-eval t)
α F .≤-closed x≤y (t , y≤t) = t , C.trans x≤y y≤t
α F .∨-closed (s , x≤s) (t , y≤t) = node s t , C.mono x≤s y≤t

α-mono : F L.≤ G → α F ≤ α G
α-mono F≤G .*≤* (t , x≤t) = `⋁-map F≤G t , C.trans x≤t (`⋁-map-eval F≤G t)

α-cong : ∀ {F G} → F L.≈ G → α F ≈ α G
α-cong (G≤F , F≤G) = (α-mono G≤F , α-mono F≤G)

------------------------------------------------------------------------------
η : Carrier → Ideal
η x = α (L.η x)

η-mono : x ≤ᶜ y → η x ≤ η y
η-mono x≤y = α-mono (L.η-mono x≤y)

------------------------------------------------------------------------------
-- U and α form a Galois connection

`⋁-closed : (t : `⋁ (U I)) → I .ICarrier (`⋁-eval t)
`⋁-closed {I} (leaf x ϕ) = ϕ
`⋁-closed {I} (node c d) = I .∨-closed (`⋁-closed c) (`⋁-closed d)

counit : α (U I) ≤ I
counit {I} .*≤* (t , x≤t) = I .≤-closed x≤t (`⋁-closed t)

counit⁻¹ : I ≤ α (U I)
counit⁻¹ .*≤* Ix = leaf _ Ix , C.refl

counit-≈ : I ≈ α (U I)
counit-≈ = counit⁻¹ , counit

unit : F L.≤ U (α F)
unit .L.*≤* Fx = leaf _ Fx , C.refl

------------------------------------------------------------------------------
-- Binary meets

_∧_ : Ideal → Ideal → Ideal
(I ∧ J) .ICarrier x = I .ICarrier x × J .ICarrier x
(I ∧ J) .≤-closed x≤y (Iy , Jy) = I .≤-closed x≤y Iy , J .≤-closed x≤y Jy
(I ∧ J) .∨-closed (Ix , Jx) (Iy , Jy) = (I .∨-closed Ix Iy) , (J .∨-closed Jx Jy)

x∧y≤x : (I ∧ J) ≤ I
x∧y≤x .*≤* = proj₁

x∧y≤y : (I ∧ J) ≤ J
x∧y≤y .*≤* = proj₂

∧-greatest : I ≤ J → I ≤ K → I ≤ (J ∧ K)
∧-greatest K≤I K≤J .*≤* = < K≤I .*≤* , K≤J .*≤* >

∧-infimum : Infimum _≤_ _∧_
∧-infimum I J = (x∧y≤x ,  x∧y≤y , λ K → ∧-greatest)

∧-isMeetSemilattice : IsMeetSemilattice _≈_ _≤_ _∧_
∧-isMeetSemilattice = record
  { isPartialOrder = ≤-isPartialOrder
  ; infimum        = ∧-infimum
  }

-- FIXME: under what conditions does α preserve meets?

⊤ : Ideal
⊤ .ICarrier x = Lift _ Unit.⊤
⊤ .≤-closed x≤y (lift Unit.tt) = lift Unit.tt
⊤ .∨-closed _ _ = lift Unit.tt

⊤-maximum : Maximum _≤_ ⊤
⊤-maximum x .*≤* _ = lift Unit.tt

∧-⊤-isBoundedMeetSemilattice : IsBoundedMeetSemilattice _≈_ _≤_ _∧_ ⊤
∧-⊤-isBoundedMeetSemilattice = record
  { isMeetSemilattice = ∧-isMeetSemilattice
  ; maximum = ⊤-maximum
  }

------------------------------------------------------------------------------
-- Binary joins

_∨_ : Ideal → Ideal → Ideal
I ∨ J = α (U I L.∨ U J)

⊥ : Ideal
⊥ = α L.⊥

x≤x∨y : I ≤ (I ∨ J)
x≤x∨y = ≤-trans counit⁻¹ (α-mono L.x≤x∨y)

y≤x∨y : J ≤ (I ∨ J)
y≤x∨y = ≤-trans counit⁻¹ (α-mono L.y≤x∨y)

∨-least : I ≤ K → J ≤ K → (I ∨ J) ≤ K
∨-least {I} {K} {J} I≤K J≤K .*≤* (t , x≤t) =
  K .≤-closed (C.trans x≤t (`⋁-map-eval _ t)) (`⋁-closed (`⋁-map (L.∨-least (U-mono I≤K) (U-mono J≤K)) t))

∨-supremum : Supremum _≤_ _∨_
∨-supremum I J = (x≤x∨y , y≤x∨y , λ K → ∨-least)

∨-isJoinSemilattice : IsJoinSemilattice _≈_ _≤_ _∨_
∨-isJoinSemilattice = record
  { isPartialOrder = ≤-isPartialOrder
  ; supremum       = ∨-supremum
  }

⊥-minimum : Minimum _≤_ ⊥
⊥-minimum x = ≤-trans (α-mono (L.⊥-minimum (U x))) counit

∨-⊥-isBoundedJoinSemilattice : IsBoundedJoinSemilattice _≈_ _≤_ _∨_ ⊥
∨-⊥-isBoundedJoinSemilattice = record
  { isJoinSemilattice = ∨-isJoinSemilattice
  ; minimum = ⊥-minimum
  }

private
  helper : (c : `⋁ (L.η (x ∨ᶜ y))) → Σ[ d ∈ `⋁ (U (α (L.η x) ∨ α (L.η y))) ] (`⋁-eval c ≤ᶜ `⋁-eval d)
  helper {x}{y} (leaf z (lift z≤x∨y)) =
    (node (leaf x (x≤x∨y .*≤* ((leaf x (lift C.refl)) , C.refl)))
          (leaf y (y≤x∨y .*≤* ((leaf y (lift C.refl)) , C.refl)))) ,
    z≤x∨y
  helper (node c₁ c₂) =
    let (d₁ , c₁≤d₁) , (d₂ , c₂≤d₂) = helper c₁ , helper c₂
    in node d₁ d₂ , C.mono c₁≤d₁ c₂≤d₂

η-preserve-∨ : α (L.η (x ∨ᶜ y)) ≤ α (L.η x) ∨ α (L.η y)
η-preserve-∨ {x}{y} .*≤* {z} (c , z≤c) =
  let d , c≤d = helper c in 
    Ideal.≤-closed (α (L.η x) ∨ α (L.η y)) 
      (C.trans z≤c c≤d) (`⋁-closed d)


------------------------------------------------------------------------------
module DayEntropic
    {_∙ᶜ_}
    {εᶜ}
    (isPomonoid : IsPomonoid _≈ᶜ_ _≤ᶜ_ _∙ᶜ_ εᶜ)
    (∨-entropy : Entropy _≤ᶜ_ _∨ᶜ_ _∙ᶜ_)
    (∨-tidy    : εᶜ ∨ᶜ εᶜ ≤ᶜ εᶜ)
    where

  private
    module LMon = L.Day isPomonoid

  _◁_ : Ideal → Ideal → Ideal
  (I ◁ J) .ICarrier x =
    ∃[ y ] ∃[ z ] (x ≤ᶜ (y ∙ᶜ z) × I .ICarrier y × J .ICarrier z)
  (I ◁ J) .≤-closed x≤w (y , z , w≤yz , Iy , Jz) =
    (-, -, C.trans x≤w w≤yz , Iy , Jz)
  (I ◁ J) .∨-closed (y₁ , z₁ , x₁≤y₁z₁ , ϕ₁ , ψ₁) (y₂ , z₂ , x₂≤y₂z₂ , ϕ₂ , ψ₂) =
    y₁ ∨ᶜ y₂ , z₁ ∨ᶜ z₂ ,
    C.trans (C.mono x₁≤y₁z₁ x₂≤y₂z₂) (∨-entropy _ _ _ _) ,
    I .∨-closed ϕ₁ ϕ₂ ,
    J .∨-closed ψ₁ ψ₂

  ι : Ideal
  ι .ICarrier x = Lift c (x ≤ᶜ εᶜ)
  ι .≤-closed x≤y (lift y≤ε) = lift (C.trans x≤y y≤ε)
  ι .∨-closed (lift x≤ε) (lift y≤ε) = lift (C.trans (C.mono x≤ε y≤ε) ∨-tidy)

  ◁-mono : Monotonic₂ _≤_ _≤_ _≤_ _◁_
  ◁-mono I₁≤J₁ I₂≤J₂ .*≤* = LMon.∙-mono (U-mono I₁≤J₁) (U-mono I₂≤J₂) .L.*≤*

  ◁-assoc : Associative _≈_ _◁_
  ◁-assoc I J K .proj₁ .*≤* = LMon.∙-assoc (U I) (U J) (U K) .proj₁ .L.*≤*
  ◁-assoc I J K .proj₂ .*≤* = LMon.∙-assoc (U I) (U J) (U K) .proj₂ .L.*≤*

  ◁-identityˡ : LeftIdentity _≈_ ι _◁_
  ◁-identityˡ I .proj₁ .*≤* = LMon.∙-identityˡ (U I) .proj₁ .L.*≤*
  ◁-identityˡ I .proj₂ .*≤* = LMon.∙-identityˡ (U I) .proj₂ .L.*≤*

  ◁-identityʳ : RightIdentity _≈_ ι _◁_
  ◁-identityʳ I .proj₁ .*≤* = LMon.∙-identityʳ (U I) .proj₁ .L.*≤*
  ◁-identityʳ I .proj₂ .*≤* = LMon.∙-identityʳ (U I) .proj₂ .L.*≤*

  ◁-identity : Identity _≈_ ι _◁_
  ◁-identity = (◁-identityˡ , ◁-identityʳ)

  ◁-isPomonoid : IsPomonoid _≈_ _≤_ _◁_ ι
  ◁-isPomonoid = record
    { isPosemigroup = record
      { isPomagma = record
        { isPartialOrder = ≤-isPartialOrder
        ; mono = ◁-mono
        }
      ; assoc = ◁-assoc
      }
    ; identity = ◁-identity
    }

  U-monoidal : U (I ◁ J) L.≈ (U I LMon.∙ U J)
  U-monoidal .proj₁ .L.*≤* Ix = Ix
  U-monoidal .proj₂ .L.*≤* Ix = Ix

  U-monoidal-ι : U ι L.≈ LMon.ε
  U-monoidal-ι .proj₁ .L.*≤* x≤ε = x≤ε
  U-monoidal-ι .proj₂ .L.*≤* x≤ε = x≤ε

  η-preserve-◁ : η (x ∙ᶜ y) ≤ η x ◁ η y
  η-preserve-◁ {x} {y} .*≤* {z} (c , z≤c) =
    Ideal.≤-closed
      (α (L.η x) ◁ α (L.η y))
        (C.trans z≤c (`⋁-map-eval _ c))
          (`⋁-closed {α (L.η x) ◁ α (L.η y)} 
            (`⋁-map 
              (L.≤-trans LMon.η-preserve-∙ 
                (L.≤-trans (LMon.∙-mono unit unit) (U-monoidal .proj₂))) c))

{-
  -- FIXME: this doesn't work
  module _ (idem : ∀ {x} → x ∨ᶜ x ≤ᶜ x) where

    open IsPomonoid isPomonoid using (mono)

    -- FIXME: this is the same combination function as below
    _∙ᶜ'_ : `⋁ F → `⋁ G → `⋁ (F LMon.∙ G)
    leaf x Fx  ∙ᶜ' leaf y Gy  = leaf (x ∙ᶜ y) (x , y , C.refl , Fx , Gy)
    leaf x Fx  ∙ᶜ' node d₁ d₂ = node (leaf x Fx ∙ᶜ' d₁) (leaf x Fx ∙ᶜ' d₂)
    node c₁ c₂ ∙ᶜ' d          = node (c₁ ∙ᶜ' d) (c₂ ∙ᶜ' d)

    `⋁-∙-eval : (c : `⋁ F)(d : `⋁ G) → eval (c ∙ᶜ' d) ≤ᶜ eval c ∙ᶜ eval d
    `⋁-∙-eval (leaf x Fx)  (leaf y Gy)  = C.refl
    `⋁-∙-eval (leaf x Fx)  (node d₁ d₂) =
       C.trans (C.mono (`⋁-∙-eval (leaf x Fx) d₁) (`⋁-∙-eval (leaf x Fx) d₂))
      (C.trans (∨-entropy _ _ _ _)
               (mono idem C.refl))
    `⋁-∙-eval (node c₁ c₂) d =
      C.trans (C.mono (`⋁-∙-eval c₁ d) (`⋁-∙-eval c₂ d))
      (C.trans (∨-entropy _ _ _ _)
      (mono C.refl idem))

    η-preserve-◁⁻¹ : α (η x) ◁ α (η y) ≤ α (η (x ∙ᶜ y))
    η-preserve-◁⁻¹ {x}{y} .*≤* {z} (z₁ , z₂ , z≤z₁z₂ , (c₁ , z₁≤c) , (c₂ , z₂≤c)) =
      `⋁-map η-preserve-∙⁻¹ (c₁ ∙ᶜ' c₂) ,
      C.trans z≤z₁z₂ {!!}
-}

module DayCommutative
    {_∙ᶜ_}
    {εᶜ}
    (isCommutativePomonoid : IsCommutativePomonoid _≈ᶜ_ _≤ᶜ_ _∙ᶜ_ εᶜ)
    (distrib : _DistributesOver_ _≤ᶜ_ _∙ᶜ_ _∨ᶜ_)
  where

  private
    module Mon = IsCommutativePomonoid isCommutativePomonoid
    module LMon = L.DayCommutative isCommutativePomonoid

  distribˡ = distrib .proj₁
  distribʳ = distrib .proj₂

  _∙_ : Ideal → Ideal → Ideal
  I ∙ J = α (U I LMon.∙ U J)

  ε : Ideal
  ε = α LMon.ε

  _`⋁-∙_ : `⋁ F → `⋁ G → `⋁ (F LMon.∙ G)
  leaf x Fx  `⋁-∙ leaf y Gy  = leaf (x ∙ᶜ y) (x , y , C.refl , Fx , Gy)
  leaf x Fx  `⋁-∙ node d₁ d₂ = node (leaf x Fx `⋁-∙ d₁) (leaf x Fx `⋁-∙ d₂)
  node c₁ c₂ `⋁-∙ d          = node (c₁ `⋁-∙ d) (c₂ `⋁-∙ d)

  `⋁-∙-eval : (c : `⋁ F)(d : `⋁ G) → `⋁-eval c ∙ᶜ `⋁-eval d ≤ᶜ `⋁-eval (c `⋁-∙ d)
  `⋁-∙-eval (leaf x Fx)  (leaf y Gy)  = C.refl
  `⋁-∙-eval (leaf x Fx)  (node d₁ d₂) = C.trans (distribˡ _ _ _) (C.mono (`⋁-∙-eval (leaf x Fx) d₁) (`⋁-∙-eval (leaf x Fx) d₂))
  `⋁-∙-eval (node c₁ c₂) d            = C.trans (distribʳ _ _ _) (C.mono (`⋁-∙-eval c₁ d) (`⋁-∙-eval c₂ d))

  α-helper : (c : `⋁ (U (α F) LMon.∙ U (α G))) → x ≤ᶜ `⋁-eval c → Σ[ d ∈ `⋁ (F LMon.∙ G) ] (x ≤ᶜ `⋁-eval d)
  α-helper (leaf y (y₁ , y₂ , y≤y₁y₂ , (c , y₁≤c) , (d , y₂≤d))) x≤y =
    (c `⋁-∙ d) , C.trans x≤y (C.trans y≤y₁y₂ (C.trans (Mon.mono y₁≤c y₂≤d) (`⋁-∙-eval c d)))
  α-helper (node c d) x≤cd =
    let (c' , c≤c') , (d' , d≤d') = α-helper c C.refl , α-helper d C.refl
    in (node c' d') , (C.trans x≤cd (C.mono c≤c' d≤d'))

  α-monoidal : (α F ∙ α G) ≈ α (F LMon.∙ G)
  α-monoidal .proj₁ .*≤* (c , x≤c)  = α-helper c x≤c
  α-monoidal .proj₂ = α-mono (LMon.∙-mono unit unit)

  ∙-mono : Monotonic₂ _≤_ _≤_ _≤_ _∙_
  ∙-mono I₁≤I₂ J₁≤J₂ = α-mono (LMon.∙-mono (U-mono I₁≤I₂) (U-mono J₁≤J₂))

  η-preserve-∙ : η (x ∙ᶜ y) ≤ η x ∙ η y
  η-preserve-∙ = α-mono (L.≤-trans LMon.η-preserve-∙ (LMon.∙-mono unit unit))

  η-preserve-∙⁻¹ : η x ∙ η y ≤ η (x ∙ᶜ y)
  η-preserve-∙⁻¹ = ≤-trans (α-monoidal .proj₁) (α-mono LMon.η-preserve-∙⁻¹)

  ∙-assoc : Associative _≈_ _∙_
  ∙-assoc I J K =
    begin
      (I ∙ J) ∙ K
    ≡⟨⟩
      α (U (α (U I LMon.∙ U J)) LMon.∙ U K)
    ≈⟨ α-cong (LMon.∙-congˡ (U-cong counit-≈)) ⟩
      α (U (α (U I LMon.∙ U J)) LMon.∙ U (α (U K)))
    ≈⟨ α-monoidal ⟩
      α ((U I LMon.∙ U J) LMon.∙ U K)
    ≈⟨ α-cong (LMon.∙-assoc (U I) (U J) (U K)) ⟩
      α (U I LMon.∙ (U J LMon.∙ U K))
    ≈⟨ α-monoidal ⟨
      α (U (α (U I)) LMon.∙ U (α (U J LMon.∙ U K)))
    ≈⟨ α-cong (LMon.∙-congʳ (U-cong counit-≈)) ⟨
      α (U I LMon.∙ U (α (U J LMon.∙ U K)))
    ≡⟨⟩
      I ∙ (J ∙ K)
    ∎
    where open SetoidReasoning ≈-setoid

  ∙-identityˡ : LeftIdentity _≈_ ε _∙_
  ∙-identityˡ I =
    begin
      ε ∙ I
    ≡⟨⟩
      α (U (α LMon.ε) LMon.∙ U I)
    ≈⟨ α-cong (LMon.∙-congˡ (U-cong counit-≈)) ⟩
      α (U (α LMon.ε) LMon.∙ U (α (U I)))
    ≈⟨ α-monoidal ⟩
      α (LMon.ε LMon.∙ U I)
    ≈⟨ α-cong (LMon.∙-identityˡ (U I)) ⟩
      α (U I)
    ≈⟨ counit-≈ ⟨
      I
    ∎
    where open SetoidReasoning ≈-setoid

  ∙-identityʳ : RightIdentity _≈_ ε _∙_
  ∙-identityʳ I =
    begin
      I ∙ ε
    ≡⟨⟩
      α (U I LMon.∙ U (α LMon.ε))
    ≈⟨ α-cong (LMon.∙-congʳ (U-cong counit-≈)) ⟩
      α (U (α (U I)) LMon.∙ U (α LMon.ε))
    ≈⟨ α-monoidal ⟩
      α (U I LMon.∙ LMon.ε)
    ≈⟨ α-cong (LMon.∙-identityʳ (U I)) ⟩
      α (U I)
    ≈⟨ counit-≈ ⟨
      I
    ∎
    where open SetoidReasoning ≈-setoid

  ∙-comm : Commutative _≈_ _∙_
  ∙-comm I J = α-cong (LMon.∙-comm (U I) (U J))

  ∙-isCommutativePomonoid : IsCommutativePomonoid _≈_ _≤_ _∙_ ε
  ∙-isCommutativePomonoid = record
    { isPomonoid = record
      { isPosemigroup = record
        { isPomagma = record
          { isPartialOrder = ≤-isPartialOrder
          ; mono = ∙-mono
          }
        ; assoc = ∙-assoc
        }
      ; identity = ∙-identityˡ , ∙-identityʳ
      }
      ; comm = ∙-comm
    }

  commutativePomonoid : CommutativePomonoid (suc (c ⊔ ℓ₂)) (c ⊔ ℓ₂) (c ⊔ ℓ₂)
  commutativePomonoid = record
    { isCommutativePomonoid = ∙-isCommutativePomonoid }

  ------------------------------------------------------------------------------
  -- Residuals

  _⊸_ : Ideal → Ideal → Ideal
  (I ⊸ J) .ICarrier x = ∀ {y} → I .ICarrier y → J .ICarrier (x ∙ᶜ y)
  (I ⊸ J) .≤-closed x≤z f Iy = J .≤-closed (Mon.monoˡ x≤z) (f Iy)
  (I ⊸ J) .∨-closed I⊸Jx I⊸Jy {z} Iz =
    J .≤-closed (distribʳ _ _ _) (J .∨-closed (I⊸Jx Iz) (I⊸Jy Iz))

  U⊸ : U (I ⊸ J) L.≤ (U I LMon.⊸ U J)
  U⊸ .L.*≤* f = f

  U⊸⁻¹ : (U I LMon.⊸ U J) L.≤ U (I ⊸ J)
  U⊸⁻¹ .L.*≤* f = f

  U⊸-≈ : U (I ⊸ J) L.≈ (U I LMon.⊸ U J)
  U⊸-≈ = (U⊸ , U⊸⁻¹)

  ⊸-residual-to : (I ∙ J) ≤ K → J ≤ (I ⊸ K)
  ⊸-residual-to IJ≤K =
    ≤-trans counit⁻¹
   (≤-trans (α-mono (LMon.⊸-residual-to (L.≤-trans unit (U-mono IJ≤K))))
   (≤-trans (α-mono U⊸⁻¹)
             counit))

  ⊸-residual-from : J ≤ (I ⊸ K) → (I ∙ J) ≤ K
  ⊸-residual-from {J} {I} {K} J≤I⊸K =
    begin
      I ∙ J
    ≡⟨⟩
      α (U I LMon.∙ U J)
    ≤⟨ α-mono (LMon.⊸-residual-from (L.≤-trans (U-mono J≤I⊸K) U⊸)) ⟩
      α (U K)
    ≈⟨ counit-≈ ⟨
      K
    ∎
    where open PosetReasoning ≤-poset

  ⊸-residual : RightResidual _≤_ _∙_ _⊸_
  ⊸-residual ._↔_.to        = ⊸-residual-to
  ⊸-residual ._↔_.from      = ⊸-residual-from

  ⊸-∙-isResiduatedCommutativePomonoid : IsResiduatedCommutativePomonoid _≈_ _≤_ _∙_ _⊸_ ε
  ⊸-∙-isResiduatedCommutativePomonoid = record
    { isCommutativePomonoid = ∙-isCommutativePomonoid
    ; residuated = comm∧residual⇒residuated ≤-isPreorder ∙-comm ⊸-residual
    }

module DayDuoidal
    {_∙ᶜ_} 
    {_◁ᶜ_} 
    {εᶜ}
    {ιᶜ}
    (isCommutativeDuoidal : IsCommutativeDuoidal _≈ᶜ_ _≤ᶜ_ _∙ᶜ_ _◁ᶜ_ εᶜ ιᶜ)
    (distrib : _DistributesOver_ _≤ᶜ_ _∙ᶜ_ _∨ᶜ_)
    (∨ᶜ-entropy : Entropy _≤ᶜ_ _∨ᶜ_ _◁ᶜ_)
    (∨ᶜ-tidy : ιᶜ ∨ᶜ ιᶜ ≤ᶜ ιᶜ)
  where

  private
    module Duo = IsCommutativeDuoidal isCommutativeDuoidal
    module LDuo = L.DayDuoidal Duo.isDuoidal

  open DayCommutative Duo.∙-isCommutativePomonoid distrib
  open DayEntropic Duo.◁-isPomonoid ∨ᶜ-entropy ∨ᶜ-tidy

  ∙-◁-entropy : Entropy _≤_ _∙_ _◁_
  ∙-◁-entropy I₁ J₁ I₂ J₂ =
    begin
      (I₁ ◁ J₁) ∙ (I₂ ◁ J₂)
    ≡⟨⟩
      α (U (I₁ ◁ J₁) LDuo.∙ U (I₂ ◁ J₂))
    ≈⟨ α-cong (LDuo.∙-cong U-monoidal U-monoidal) ⟩
      α ((U I₁ LDuo.◁ U J₁) LDuo.∙ (U I₂ LDuo.◁ U J₂))
    ≤⟨ α-mono (LDuo.∙-◁-entropy (U I₁) (U J₁) (U I₂) (U J₂)) ⟩
      α ((U I₁ LDuo.∙ U I₂) LDuo.◁ (U J₁ LDuo.∙ U J₂))
    ≤⟨ α-mono (LDuo.◁-mono unit unit) ⟩
      α (U (α (U I₁ LDuo.∙ U I₂)) LDuo.◁ U (α (U J₁ LDuo.∙ U J₂)))
    ≈⟨ α-cong U-monoidal ⟨
      α (U (α (U I₁ LDuo.∙ U I₂) ◁ α (U J₁ LDuo.∙ U J₂)))
    ≈⟨ counit-≈ ⟨
      α (U I₁ LDuo.∙ U I₂) ◁ α (U J₁ LDuo.∙ U J₂)
    ≡⟨⟩
      (I₁ ∙ I₂) ◁ (J₁ ∙ J₂)
    ∎
    where open PosetReasoning ≤-poset

  tidy : (c : `⋁ LDuo.ι) → `⋁-eval c ≤ᶜ ιᶜ
  tidy (leaf x (lift x≤ι)) = x≤ι
  tidy (node c d) = C.trans (C.mono (tidy c) (tidy d)) ∨ᶜ-tidy

  ε≤ι : ε ≤ ι
  ε≤ι .*≤* (t , x≤t) = lift (C.trans x≤t (C.trans (`⋁-map-eval LDuo.ε≤ι t) (tidy (`⋁-map LDuo.ε≤ι t))))

  ∙-◁-isDuoidal : IsDuoidal _≈_ _≤_ _∙_ _◁_ ε ι
  ∙-◁-isDuoidal = record
    { ∙-isPomonoid = IsCommutativePomonoid.isPomonoid ∙-isCommutativePomonoid
    ; ◁-isPomonoid = ◁-isPomonoid
    ; ∙-◁-entropy = ∙-◁-entropy
    ; ∙-idem-ι = ≤-trans (α-mono (LDuo.∙-mono (U-monoidal-ι .proj₁) (U-monoidal-ι .proj₁)))
                (≤-trans (α-mono LDuo.∙-idem-ι)
                (≤-trans (α-mono (U-monoidal-ι .proj₂))
                          counit))
    ; ◁-idem-ε = ≤-trans (α-mono LDuo.◁-idem-ε)
                (≤-trans (α-mono (LDuo.◁-mono unit unit))
                (≤-trans (α-mono (U-monoidal .proj₂))
                counit))
    ; ε≲ι = ε≤ι
    }
   