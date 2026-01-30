{-# OPTIONS --postfix-projections --safe --without-K --no-exact-split --cubical-compatible #-}

open import Level using (_⊔_; Level; suc; Lift; lift; lower)
open import Algebra using (Associative; LeftIdentity; RightIdentity; Identity; _DistributesOver_; Commutative; Op₁)
open import Algebra.Ordered
  using (Pomagma; IsPomonoid; Entropy; IsCommutativePomonoid; CommutativePomonoid; RightResidual; IsResiduatedCommutativePomonoid; IsCommutativeDuoidal; IsDuoidal)
open import Algebra.Ordered.Consequences using (comm∧residual⇒residuated)
import Algebra.Ordered.Construction.LowerSet
open import Function using (const; flip)
open import Function.EquiInhabited using (_↔_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; <_,_>; -,_; Σ-syntax; ∃; ∃-syntax)
open import Data.Unit as Unit using ()
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary using (IsPartialOrder; IsPreorder; Poset; Setoid; Maximum; Minimum; Monotonic₁; Monotonic₂)
open import Relation.Binary.Construct.Core.Symmetric as SymCore using (SymCore)
open import Relation.Binary.Lattice using (Infimum; IsMeetSemilattice; IsBoundedMeetSemilattice; Supremum; IsJoinSemilattice; IsBoundedJoinSemilattice)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
import Relation.Binary.Construct.Flip.EqAndOrd as Flip
open import Relation.Unary using (Pred; _⊆_)
import Relation.Binary.Reasoning.PartialOrder as PosetReasoning
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

module Algebra.Ordered.Construction.ZeroPlusIdeal {c ℓ₁ ℓ₂}
         (pomagma : Pomagma c ℓ₁ ℓ₂)
         (⊥ᶜ : pomagma .Pomagma.Carrier)
     where

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
    0-closed : ICarrier ⊥ᶜ
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
-- Closure under finite join-like things

data Context (F : LowerSet) : Carrier → Set (c ⊔ ℓ₂) where
  leaf : ∀ {x} → F .L.ICarrier x → Context F x
  bot  : (x : Carrier) → x ≤ᶜ ⊥ᶜ → Context F x
  node : ∀ {x y z} → Context F x → Context F y → z ≤ᶜ (x ∨ᶜ y) → Context F z

Context-≤ : x ≤ᶜ y → Context F y → Context F x
Context-≤ {x} {y} {F} x≤y (leaf Fy) = leaf (L.≤-closed F x≤y Fy)
Context-≤ x≤y (bot y y≤⊥) = bot _ (C.trans x≤y y≤⊥)
Context-≤ x≤y (node {z₁} {z₂} ϕ₁ ϕ₂ y≤z₁∨z₂) = node ϕ₁ ϕ₂ (C.trans x≤y y≤z₁∨z₂)

α : LowerSet → Ideal
α F .ICarrier = Context F
α F .≤-closed = Context-≤
α F .0-closed = bot ⊥ᶜ C.refl
α F .∨-closed Fx Fy = node Fx Fy C.refl

Context-mono : F L.≤ G → Context F x → Context G x
Context-mono F≤G (leaf x) = leaf (F≤G .L.*≤* x)
Context-mono F≤G (bot x x≤⊥) = bot x x≤⊥
Context-mono {x = z} F≤G (node Ix Iy z≤x∨y) = node (Context-mono F≤G Ix) (Context-mono F≤G Iy) z≤x∨y

α-mono : F L.≤ G → α F ≤ α G
α-mono F≤G .*≤* = Context-mono F≤G

α-cong : ∀ {F G} → F L.≈ G → α F ≈ α G
α-cong (G≤F , F≤G) = (α-mono G≤F , α-mono F≤G)

ideals-closed : Context (U I) x → I .ICarrier x
ideals-closed {I} (leaf Ix) = Ix
ideals-closed {I} (bot x x≤⊥) = I .≤-closed x≤⊥ (I .0-closed)
ideals-closed {I} {z} (node Ix Iy z≤x∨y) =
  I .≤-closed z≤x∨y (I .∨-closed (ideals-closed Ix) (ideals-closed Iy))

counit : α (U I) ≤ I
counit {I} .*≤* = ideals-closed

counit⁻¹ : I ≤ α (U I)
counit⁻¹ {I} .*≤* = leaf

counit-≈ : I ≈ α (U I)
counit-≈ = counit⁻¹ , counit

unit : F L.≤ U (α F)
unit .L.*≤* = leaf

------------------------------------------------------------------------------
η : Carrier → Ideal
η x = α (L.η x)

η-mono : x ≤ᶜ y → η x ≤ η y
η-mono x≤y = α-mono (L.η-mono x≤y)

------------------------------------------------------------------------------
-- Binary meets

_∧_ : Ideal → Ideal → Ideal
(I ∧ J) .ICarrier x = I .ICarrier x × J .ICarrier x
(I ∧ J) .≤-closed x≤y (Iy , Jy) = I .≤-closed x≤y Iy , J .≤-closed x≤y Jy
(I ∧ J) .0-closed = I .0-closed , J .0-closed
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
⊤ .0-closed = lift Unit.tt
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
∨-least I≤K J≤K = ≤-trans (α-mono (L.∨-least (U-mono I≤K) (U-mono J≤K))) counit

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

Context-preserve-∨ : Context (L.η (x ∨ᶜ y)) z → Context (U (α (L.η x)) L.∨ U (α (L.η y))) z
Context-preserve-∨ (leaf (lift z≤x∨y)) =
  node (leaf (inj₁ (leaf (lift C.refl))))
       (leaf (inj₂ (leaf (lift C.refl))))
       z≤x∨y
Context-preserve-∨ (bot x x≤⊥) = bot x x≤⊥
Context-preserve-∨ (node ϕ₁ ϕ₂ x) = node (Context-preserve-∨ ϕ₁) (Context-preserve-∨ ϕ₂) x

η-preserve-∨ : η (x ∨ᶜ y) ≤ η x ∨ η y
η-preserve-∨ .*≤* = Context-preserve-∨

Context-preserve-⊥ : Context (L.η ⊥ᶜ) x → Context L.⊥ x
Context-preserve-⊥ (leaf x) = bot _ (x .lower)
Context-preserve-⊥ (bot _ x≤⊥) = bot _ x≤⊥
Context-preserve-⊥ (node ϕ₁ ϕ₂ x≤y₁∨y₂) = node (Context-preserve-⊥ ϕ₁) (Context-preserve-⊥ ϕ₂) x≤y₁∨y₂

η-preserve-⊥ᶜ : η ⊥ᶜ ≤ ⊥
η-preserve-⊥ᶜ .*≤* = Context-preserve-⊥

------------------------------------------------------------------------------
module DayEntropic
    {_∙ᶜ_}
    {εᶜ}
    (isPomonoid : IsPomonoid _≈ᶜ_ _≤ᶜ_ _∙ᶜ_ εᶜ)
    (∨-entropy : Entropy _≤ᶜ_ _∨ᶜ_ _∙ᶜ_)
    (∨-tidy    : εᶜ ∨ᶜ εᶜ ≤ᶜ εᶜ)
    (⊥ᶜ-expand : ⊥ᶜ ≤ᶜ ⊥ᶜ ∙ᶜ ⊥ᶜ)
    (⊥ᶜ≤εᶜ     : ⊥ᶜ ≤ᶜ εᶜ)
    where

  private
    module LMon = L.Day isPomonoid

  _◁_ : Ideal → Ideal → Ideal
  (I ◁ J) .ICarrier x =
    ∃[ y ] ∃[ z ] (x ≤ᶜ (y ∙ᶜ z) × I .ICarrier y × J .ICarrier z)
  (I ◁ J) .≤-closed x≤w (y , z , w≤yz , Iy , Jz) =
    (-, -, C.trans x≤w w≤yz , Iy , Jz)
  (I ◁ J) .0-closed = ⊥ᶜ , ⊥ᶜ , ⊥ᶜ-expand , I .0-closed , J .0-closed
  (I ◁ J) .∨-closed (y₁ , z₁ , x₁≤y₁z₁ , ϕ₁ , ψ₁) (y₂ , z₂ , x₂≤y₂z₂ , ϕ₂ , ψ₂) =
    y₁ ∨ᶜ y₂ , z₁ ∨ᶜ z₂ ,
    C.trans (C.mono x₁≤y₁z₁ x₂≤y₂z₂) (∨-entropy _ _ _ _) ,
    I .∨-closed ϕ₁ ϕ₂ ,
    J .∨-closed ψ₁ ψ₂

  ι : Ideal
  ι .ICarrier x = Lift c (x ≤ᶜ εᶜ)
  ι .≤-closed x≤y (lift y≤ε) = lift (C.trans x≤y y≤ε)
  ι .0-closed = lift ⊥ᶜ≤εᶜ
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
  η-preserve-◁ {x} {y} = begin
      α (L.η (x ∙ᶜ y))
    ≤⟨ α-mono LMon.η-preserve-∙ ⟩
      α (L.η x LMon.∙ L.η y)
    ≤⟨ α-mono (LMon.∙-mono unit unit) ⟩
      α (U (α (L.η x)) LMon.∙ U (α (L.η y)))
    ≤⟨ α-mono (U-monoidal .proj₂) ⟩
      α (U (α (L.η x) ◁ α (L.η y)))
    ≤⟨ counit ⟩
      α (L.η x) ◁ α (L.η y)
    ∎
    where open PosetReasoning ≤-poset

-- FIXME: could do Day without commutative as well
module DayCommutative
    {_∙ᶜ_}
    {εᶜ}
    (isCommutativePomonoid : IsCommutativePomonoid _≈ᶜ_ _≤ᶜ_ _∙ᶜ_ εᶜ)
    (distrib : _DistributesOver_ _≤ᶜ_ _∙ᶜ_ _∨ᶜ_)
    (⊥ᶜ-distrib : ∀ {x} → ⊥ᶜ ∙ᶜ x ≤ᶜ ⊥ᶜ)
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

  -- FIXME: if εᶜ is closed under ⟘ and ∨, then η εᶜ is automatically
  -- an ideal, and we do not need to complete it. This is done in the
  -- Day Duoidal section below, but is useful even without the
  -- duoidality assumption.

  -- “Multiplication” of contexts
  Context-∙ : Context F x → Context G y → Context (F LMon.∙ G) (x ∙ᶜ y)
  Context-∙ (leaf Fx) (leaf Gy) = leaf (_ , _ , C.refl , Fx , Gy)
  Context-∙ (leaf Fx) (bot _ y≤⊥) = bot _ (C.trans (Mon.mono C.refl y≤⊥) (C.trans (C.reflexive (Mon.comm _ _)) ⊥ᶜ-distrib))
  Context-∙ (leaf Fx) (node ψ₁ ψ₂ y≤y₁∙y₂) =
    node (Context-∙ (leaf Fx) ψ₁) (Context-∙ (leaf Fx) ψ₂) (C.trans (Mon.mono C.refl y≤y₁∙y₂) (distribˡ _ _ _))
  Context-∙ (bot _ x≤⊥) ψ = bot _ (C.trans (Mon.mono x≤⊥ C.refl) ⊥ᶜ-distrib)
  Context-∙ (node ϕ₁ ϕ₂ x≤x₁∙x₂) ψ =
    node (Context-∙ ϕ₁ ψ) (Context-∙ ϕ₂ ψ) (C.trans (Mon.mono x≤x₁∙x₂ C.refl) (distribʳ _ _ _))

  Context-strong : Context (U (α F) LMon.∙ U (α G)) z → Context (F LMon.∙ G) z
  Context-strong (leaf (x , y , z≤x∙y , ϕ₁ , ϕ₂)) = Context-≤ z≤x∙y (Context-∙ ϕ₁ ϕ₂)
  Context-strong (bot x x≤⊥) = bot x x≤⊥
  Context-strong (node ϕ₁ ϕ₂ z≤x∨y) = node (Context-strong ϕ₁) (Context-strong ϕ₂) z≤x∨y

  α-monoidal : (α F ∙ α G) ≈ α (F LMon.∙ G)
  α-monoidal .proj₁ .*≤* = Context-strong
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
  (I ⊸ J) .0-closed Iy = J .≤-closed ⊥ᶜ-distrib (J .0-closed)
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

  module Exp (！ᶜ : Op₁ Carrier)
      (！ᶜ-discard   : ∀ {x} → ！ᶜ x ≤ᶜ εᶜ)
      (！ᶜ-duplicate : ∀ {x} → ！ᶜ x ≤ᶜ (！ᶜ x ∙ᶜ ！ᶜ x))
      (！ᶜ-derelict  : ∀ {x} → ！ᶜ x ≤ᶜ x)
      (！ᶜ-dig       : ∀ {x} → ！ᶜ x ≤ᶜ ！ᶜ (！ᶜ x))
      where

    private
      module LExp = LMon.Exp ！ᶜ ！ᶜ-discard ！ᶜ-duplicate ！ᶜ-derelict ！ᶜ-dig

    ！ : Ideal → Ideal
    ！ I = α (LExp.！ (U I))

    ！-monoidal-unit : ε ≤ ！ ε
    ！-monoidal-unit =
      ≤-trans (α-mono LExp.！-monoidal-unit) (α-mono (LExp.！-mono unit))

    ！-monoidal : (！ I ∙ ！ J) ≤ ！ (I ∙ J)
    ！-monoidal = ≤-trans (α-monoidal .proj₁)
                 (≤-trans (α-mono LExp.！-monoidal)
                 (α-mono (LExp.！-mono unit)))

    ！-mono : Monotonic₁ _≤_ _≤_ ！
    ！-mono I≤J = α-mono (LExp.！-mono (U-mono I≤J))

    ！-discard : ！ I ≤ ε
    ！-discard = α-mono LExp.！-discard

    ！-duplicate : ！ I ≤ (！ I ∙ ！ I)
    ！-duplicate = ≤-trans (α-mono LExp.！-duplicate) (α-monoidal .proj₂)

    ！-derelict : ！ I ≤ I
    ！-derelict = ≤-trans (α-mono LExp.！-derelict) counit

    ！-dig : ！ I ≤ ！ (！ I)
    ！-dig = ≤-trans (α-mono LExp.！-dig) (α-mono (LExp.！-mono unit))

    η-preserve-！ : η (！ᶜ x) ≤ ！ (η x)
    η-preserve-！ = ≤-trans (α-mono LExp.η-preserve-！) (α-mono (LExp.！-mono unit))

module DayDuoidal
    {_∙ᶜ_}
    {_◁ᶜ_}
    {εᶜ}
    {ιᶜ}
    (isCommutativeDuoidal : IsCommutativeDuoidal _≈ᶜ_ _≤ᶜ_ _∙ᶜ_ _◁ᶜ_ εᶜ ιᶜ)
    (distrib : _DistributesOver_ _≤ᶜ_ _∙ᶜ_ _∨ᶜ_)
    (⊥ᶜ-distrib : ∀ {x} → ⊥ᶜ ∙ᶜ x ≤ᶜ ⊥ᶜ)
    (∨ᶜ-entropy : Entropy _≤ᶜ_ _∨ᶜ_ _◁ᶜ_)
    (∨ᶜ-tidy : ιᶜ ∨ᶜ ιᶜ ≤ᶜ ιᶜ)
    (⊥ᶜ-expand : ⊥ᶜ ≤ᶜ (⊥ᶜ ◁ᶜ ⊥ᶜ))
    (⊥ᶜ≤ιᶜ     : ⊥ᶜ ≤ᶜ ιᶜ)
  where

  private
    module Duo = IsCommutativeDuoidal isCommutativeDuoidal
    module LDuo = L.DayDuoidal Duo.isDuoidal

  open DayCommutative Duo.∙-isCommutativePomonoid distrib ⊥ᶜ-distrib
  open DayEntropic Duo.◁-isPomonoid ∨ᶜ-entropy ∨ᶜ-tidy ⊥ᶜ-expand ⊥ᶜ≤ιᶜ

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

  Context-tidy : Context (L.η ιᶜ) z → z ≤ᶜ ιᶜ
  Context-tidy (leaf x) = x .lower
  Context-tidy (bot _ z≤⊥) = C.trans z≤⊥ ⊥ᶜ≤ιᶜ
  Context-tidy (node ϕ₁ ϕ₂ z≤x₁∨x₂) = C.trans z≤x₁∨x₂ (C.trans (C.mono (Context-tidy ϕ₁) (Context-tidy ϕ₂)) ∨ᶜ-tidy)

  ε≤ι : ε ≤ ι
  ε≤ι .*≤* ϕ .lower = Context-tidy (Context-mono (L.η-mono Duo.ε≲ι) ϕ)

  ∙-◁-isDuoidal : IsDuoidal _≈_ _≤_ _∙_ _◁_ ε ι
  ∙-◁-isDuoidal = record
    { ∙-isPomonoid = IsCommutativePomonoid.isPomonoid ∙-isCommutativePomonoid
    ; ◁-isPomonoid = ◁-isPomonoid
    ; ∙-◁-entropy = ∙-◁-entropy
      -- FIXME: split these two out
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
