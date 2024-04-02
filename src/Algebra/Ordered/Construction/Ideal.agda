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
    +-closed : ICarrier x → ICarrier y → ICarrier (x +ᶜ y)
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
-- Turn a lower set into an ideal by closing under +

data Tree (F : LowerSet) : Set (c ⊔ ℓ₂) where
  leaf : (x : Carrier) → F .L.ICarrier x → Tree F
  node : Tree F → Tree F → Tree F

sum : Tree F → Carrier
sum (leaf x _) = x
sum (node c d) = sum c +ᶜ sum d

mapᵗ : F L.≤ G → Tree F → Tree G
mapᵗ F≤G (leaf x Fx) = leaf x (F≤G .L.*≤* Fx)
mapᵗ F≤G (node c d)  = node (mapᵗ F≤G c) (mapᵗ F≤G d)

map-sumᵗ : (F≤G : F L.≤ G) (c : Tree F) → sum c ≤ᶜ sum (mapᵗ F≤G c)
map-sumᵗ F≤G (leaf x Fx) = ≤ᶜ.refl
map-sumᵗ F≤G (node c d) = +ᶜ.mono (map-sumᵗ F≤G c) (map-sumᵗ F≤G d)

α : LowerSet → Ideal
α F .ICarrier x = Σ[ t ∈ Tree F ] (x ≤ᶜ sum t)
α F .≤-closed x≤y (t , y≤t) = t , ≤ᶜ.trans x≤y y≤t
α F .+-closed (s , x≤s) (t , y≤t) = node s t , +ᶜ.mono x≤s y≤t

α-mono : F L.≤ G → α F ≤ α G
α-mono F≤G .*≤* (t , x≤t) = mapᵗ F≤G t , ≤ᶜ.trans x≤t (map-sumᵗ F≤G t)

α-cong : ∀ {F G} → F L.≈ G → α F ≈ α G
α-cong (G≤F , F≤G) = (α-mono G≤F , α-mono F≤G)

------------------------------------------------------------------------------
η : Carrier → Ideal
η x = α (L.η x)

η-mono : x ≤ᶜ y → η x ≤ η y
η-mono x≤y = α-mono (L.η-mono x≤y)

------------------------------------------------------------------------------
-- U and α form a Galois connection

ideal-Tree-closed : (t : Tree (U I)) → I .ICarrier (sum t)
ideal-Tree-closed {I} (leaf x ϕ) = ϕ
ideal-Tree-closed {I} (node c d) = I .+-closed (ideal-Tree-closed c) (ideal-Tree-closed d)

counit : α (U I) ≤ I
counit {I} .*≤* (t , x≤t) = I .≤-closed x≤t (ideal-Tree-closed t)

counit⁻¹ : I ≤ α (U I)
counit⁻¹ .*≤* Ix = leaf _ Ix , ≤ᶜ.refl

counit-≈ : I ≈ α (U I)
counit-≈ = counit⁻¹ , counit

unit : F L.≤ U (α F)
unit .L.*≤* Fx = leaf _ Fx , ≤ᶜ.refl

------------------------------------------------------------------------------
-- Binary meets

_∧_ : Ideal → Ideal → Ideal
(I ∧ J) .ICarrier x = I .ICarrier x × J .ICarrier x
(I ∧ J) .≤-closed x≤y (Iy , Jy) = I .≤-closed x≤y Iy , J .≤-closed x≤y Jy
(I ∧ J) .+-closed (Ix , Jx) (Iy , Jy) = (I .+-closed Ix Iy) , (J .+-closed Jx Jy)

proj₁ : (I ∧ J) ≤ I
proj₁ .*≤* = Product.proj₁

proj₂ : (I ∧ J) ≤ J
proj₂ .*≤* = Product.proj₂

⟨_,_⟩ : I ≤ J → I ≤ K → I ≤ (J ∧ K)
⟨ K≤I , K≤J ⟩ .*≤* = Product.< K≤I .*≤* , K≤J .*≤* >

∧-isMeetSemilattice : IsMeetSemilattice _≈_ _≤_ _∧_
∧-isMeetSemilattice = record
  { isPartialOrder = ≤-isPartialOrder
  ; infimum        = λ I J → (proj₁ ,  proj₂ , λ K → ⟨_,_⟩)
  }

-- FIXME: under what conditions does α preserve meets?

------------------------------------------------------------------------------
-- Binary joins

_∨_ : Ideal → Ideal → Ideal
I ∨ J = α (U I L.∨ U J)

inj₁ : I ≤ (I ∨ J)
inj₁ = ≤-trans counit⁻¹ (α-mono L.inj₁)

inj₂ : J ≤ (I ∨ J)
inj₂ = ≤-trans counit⁻¹ (α-mono L.inj₂)

[_,_] : I ≤ K → J ≤ K → (I ∨ J) ≤ K
[_,_] {I} {K} {J} I≤K J≤K .*≤* (t , x≤t) =
  K .≤-closed (≤ᶜ.trans x≤t (map-sumᵗ _ t)) (ideal-Tree-closed (mapᵗ L.[ U-mono I≤K , U-mono J≤K ] t))

∨-isJoinSemilattice : IsJoinSemilattice _≈_ _≤_ _∨_
∨-isJoinSemilattice = record
  { isPartialOrder = ≤-isPartialOrder
  ; supremum       = λ I J → (inj₁ , inj₂ , λ K → [_,_])
  }


hulp : (c : Tree (L.η (x +ᶜ y))) → Σ[ d ∈ Tree (U (α (L.η x) ∨ α (L.η y))) ] (sum c ≤ᶜ sum d)
hulp {x}{y} (leaf z (lift z≤x+y)) =
  (node (leaf x (inj₁ .*≤* ((leaf x (lift ≤ᶜ.refl)) , ≤ᶜ.refl)))
        (leaf y (inj₂ .*≤* ((leaf y (lift ≤ᶜ.refl)) , ≤ᶜ.refl)))) ,
  z≤x+y
hulp (node c₁ c₂) =
  let (d₁ , c₁≤d₁) , (d₂ , c₂≤d₂) = hulp c₁ , hulp c₂
  in node d₁ d₂ , +ᶜ.mono c₁≤d₁ c₂≤d₂

η-preserve-∨ : α (L.η (x +ᶜ y)) ≤ α (L.η x) ∨ α (L.η y)
η-preserve-∨ {x}{y} .*≤* {z} (c , z≤c) =
  let d , c≤d = hulp c in down-closed (≤ᶜ.trans z≤c c≤d) (ideal-Tree-closed d)
  where open Ideal (α (L.η x) ∨ α (L.η y)) renaming (≤-closed to down-closed)


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

  _◁_ : Ideal → Ideal → Ideal
  (I ◁ J) .ICarrier x =
    ∃[ y ] ∃[ z ] (x ≤ᶜ (y ∙ᶜ z) × I .ICarrier y × J .ICarrier z)
  (I ◁ J) .≤-closed x≤w (y , z , w≤yz , Iy , Jz) =
    (-, -, ≤ᶜ.trans x≤w w≤yz , Iy , Jz)
  (I ◁ J) .+-closed (y₁ , z₁ , x₁≤y₁z₁ , ϕ₁ , ψ₁) (y₂ , z₂ , x₂≤y₂z₂ , ϕ₂ , ψ₂) =
    y₁ +ᶜ y₂ , z₁ +ᶜ z₂ ,
    ≤ᶜ.trans (+ᶜ.mono x₁≤y₁z₁ x₂≤y₂z₂) (+-entropy _ _ _ _) ,
    I .+-closed ϕ₁ ϕ₂ ,
    J .+-closed ψ₁ ψ₂

  ι : Ideal
  ι .ICarrier x = Lift c (x ≤ᶜ εᶜ)
  ι .≤-closed x≤y (lift y≤ε) = lift (≤ᶜ.trans x≤y y≤ε)
  ι .+-closed (lift x≤ε) (lift y≤ε) = lift (≤ᶜ.trans (+ᶜ.mono x≤ε y≤ε) +-tidy)

  ◁-mono : Monotonic₂ _≤_ _≤_ _≤_ _◁_
  ◁-mono I₁≤J₁ I₂≤J₂ .*≤* = LMon.∙-mono (U-mono I₁≤J₁) (U-mono I₂≤J₂) .L.*≤*

  ◁-assoc : Associative _≈_ _◁_
  ◁-assoc I J K .Product.proj₁ .*≤* = LMon.∙-assoc (U I) (U J) (U K) .Product.proj₁ .L.*≤*
  ◁-assoc I J K .Product.proj₂ .*≤* = LMon.∙-assoc (U I) (U J) (U K) .Product.proj₂ .L.*≤*

  ◁-identityˡ : LeftIdentity _≈_ ι _◁_
  ◁-identityˡ I .Product.proj₁ .*≤* = LMon.∙-identityˡ (U I) .Product.proj₁ .L.*≤*
  ◁-identityˡ I .Product.proj₂ .*≤* = LMon.∙-identityˡ (U I) .Product.proj₂ .L.*≤*

  ◁-identityʳ : RightIdentity _≈_ ι _◁_
  ◁-identityʳ I .Product.proj₁ .*≤* = LMon.∙-identityʳ (U I) .Product.proj₁ .L.*≤*
  ◁-identityʳ I .Product.proj₂ .*≤* = LMon.∙-identityʳ (U I) .Product.proj₂ .L.*≤*

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
  U-monoidal .Product.proj₁ .L.*≤* Ix = Ix
  U-monoidal .Product.proj₂ .L.*≤* Ix = Ix

  U-monoidal-ι : U ι L.≈ LMon.ε
  U-monoidal-ι .Product.proj₁ .L.*≤* x≤ε = x≤ε
  U-monoidal-ι .Product.proj₂ .L.*≤* x≤ε = x≤ε

  η-preserve-◁ : η (x ∙ᶜ y) ≤ η x ◁ η y
  η-preserve-◁ {x} {y} .*≤* {z} (c , z≤c) =
    down-closed
      (≤ᶜ.trans z≤c (map-sumᵗ _ c))
      (ideal-Tree-closed {α (L.η x) ◁ α (L.η y)} 
        (mapᵗ 
          (L.≤-trans LMon.η-preserve-∙ 
            (L.≤-trans (LMon.∙-mono unit unit) (U-monoidal .Product.proj₂))) c))
    where
      open Ideal (α (L.η x) ◁ α (L.η y)) renaming (≤-closed to down-closed)

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

    η-preserve-◁⁻¹ : α (η x) ◁ α (η y) ≤ α (η (x ∙ᶜ y))
    η-preserve-◁⁻¹ {x}{y} .*≤* {z} (z₁ , z₂ , z≤z₁z₂ , (c₁ , z₁≤c) , (c₂ , z₂≤c)) =
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

  _∙_ : Ideal → Ideal → Ideal
  I ∙ J = α (U I LMon.∙ U J)

  ε : Ideal
  ε = α LMon.ε

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

  α-monoidal : (α F ∙ α G) ≈ α (F LMon.∙ G)
  α-monoidal .Product.proj₁ .*≤* (c , x≤c)  = α-helper c x≤c
  α-monoidal .Product.proj₂ = α-mono (LMon.∙-mono unit unit)

  ∙-mono : Monotonic₂ _≤_ _≤_ _≤_ _∙_
  ∙-mono I₁≤I₂ J₁≤J₂ = α-mono (LMon.∙-mono (U-mono I₁≤I₂) (U-mono J₁≤J₂))

  η-preserve-∙ : η (x ∙ᶜ y) ≤ η x ∙ η y
  η-preserve-∙ = α-mono (L.≤-trans LMon.η-preserve-∙ (LMon.∙-mono unit unit))

  η-preserve-∙⁻¹ : η x ∙ η y ≤ η (x ∙ᶜ y)
  η-preserve-∙⁻¹ = ≤-trans (α-monoidal .Product.proj₁) (α-mono LMon.η-preserve-∙⁻¹)

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
  (I ⊸ J) .+-closed I⊸Jx I⊸Jy {z} Iz =
    J .≤-closed (distribʳ _ _ _) (J .+-closed (I⊸Jx Iz) (I⊸Jy Iz))

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
  ⊸-residual .Function.Equivalence.to        = ⊸-residual-to
  ⊸-residual .Function.Equivalence.from      = ⊸-residual-from
  ⊸-residual .Function.Equivalence.to-cong   = λ { PropEq.refl → PropEq.refl }
  ⊸-residual .Function.Equivalence.from-cong = λ { PropEq.refl → PropEq.refl }

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
    (distrib : _DistributesOver_ _≤ᶜ_ _∙ᶜ_ _+ᶜ_)
    (+ᶜ-entropy : Entropy _≤ᶜ_ _+ᶜ_ _◁ᶜ_)
    (+ᶜ-tidy : ιᶜ +ᶜ ιᶜ ≤ᶜ ιᶜ)
  where

  private
    module Duo = IsCommutativeDuoidal isCommutativeDuoidal
    module LDuo = L.LiftIsDuoidal Duo.isDuoidal

  open DayDistributive Duo.∙-isCommutativePomonoid distrib
  open DayEntropic Duo.◁-isPomonoid +ᶜ-entropy +ᶜ-tidy

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

  tidy : (c : Tree LDuo.ι) → sum c ≤ᶜ ιᶜ
  tidy (leaf x (lift x≤ι)) = x≤ι
  tidy (node c d) = ≤ᶜ.trans (+ᶜ.mono (tidy c) (tidy d)) +ᶜ-tidy

  ε≤ι : ε ≤ ι
  ε≤ι .*≤* (t , x≤t) = lift (≤ᶜ.trans x≤t (≤ᶜ.trans (map-sumᵗ LDuo.ε≤ι t) (tidy (mapᵗ LDuo.ε≤ι t))))

  ∙-◁-isDuoidal : IsDuoidal _≈_ _≤_ _∙_ _◁_ ε ι
  ∙-◁-isDuoidal = record
    { ∙-isPomonoid = IsCommutativePomonoid.isPomonoid ∙-isCommutativePomonoid
    ; ◁-isPomonoid = ◁-isPomonoid
    ; ∙-◁-entropy = ∙-◁-entropy
    ; ∙-idem-ι = ≤-trans (α-mono (LDuo.∙-mono (U-monoidal-ι .Product.proj₁) (U-monoidal-ι .Product.proj₁)))
                (≤-trans (α-mono LDuo.∙-idem-ι)
                (≤-trans (α-mono (U-monoidal-ι .Product.proj₂))
                          counit))
    ; ◁-idem-ε = ≤-trans (α-mono LDuo.◁-idem-ε)
                (≤-trans (α-mono (LDuo.◁-mono unit unit))
                (≤-trans (α-mono (U-monoidal .Product.proj₂))
                counit))
    ; ε≲ι = ε≤ι
    }
  