{-# OPTIONS --postfix-projections --safe --without-K #-}

module Algebra.Ordered.Construction.Chu where

-- If we have a preordered closed symmetric monoid with finite meets
-- and chosen element K, then the Chu construction is a *-autonomous
-- preorder. Moreover, if the preorder is duoidal, and K is a
-- ◁-monoid, then Chu(A,K) is duoidal.

open import Level
open import Data.Product as Product using (_×_; _,_; swap)
open import Function using (Equivalence)
open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Ordered using (IsCommutativePomonoid; IsPomonoid; IsPosemigroup; IsPomagma)
open import Algebra.Ordered.Consequences using (supremum∧residualʳ⇒distribˡ)
open import Algebra.Ordered.Definitions using (Entropy)
open import Algebra.Ordered.Structures.Residuated
open import Algebra.Ordered.Structures.Duoidal
open import Algebra.Ordered.Structures.StarAutonomous
open import Relation.Binary.Construct.Core.Symmetric as SymCore using (SymCore)
open import Relation.Binary.Bundles using (Poset)
open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Binary.Structures using (IsPartialOrder; IsPreorder; IsEquivalence)
open import Relation.Binary.Lattice.Definitions
open import Relation.Binary.Lattice.Structures using (IsMeetSemilattice; IsJoinSemilattice)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
import Relation.Binary.Reasoning.PartialOrder as PosetReasoning
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

module Construction
    {c ℓ₁ ℓ₂}
    {Carrier : Set c}
    {_≈ᶜ_ : Rel Carrier ℓ₁}
    {_≤ᶜ_ : Rel Carrier ℓ₂}
    {_∙ᶜ_ : Op₂ Carrier}
    {_-∙ᶜ_ : Op₂ Carrier}
    {εᶜ : Carrier}
    (∙ᶜ-isResiduatedCommutativePomonoid : IsResiduatedCommutativePomonoid _≈ᶜ_ _≤ᶜ_ _∙ᶜ_ _-∙ᶜ_ εᶜ)
    {_∧ᶜ_ : Op₂ Carrier}
    (∧ᶜ-isMeet : IsMeetSemilattice _≈ᶜ_ _≤ᶜ_ _∧ᶜ_)
    {_∨ᶜ_ : Op₂ Carrier}
    (∨ᶜ-isJoin : IsJoinSemilattice _≈ᶜ_ _≤ᶜ_ _∨ᶜ_)
    (K : Carrier)
  where

  open import Algebra.Definitions

  private
    variable
      w w′ w₁ w₂ : Carrier
      x x′ x₁ x₂ : Carrier
      y y′ y₁ y₂ : Carrier
      z z′ z₁ z₂ : Carrier

  private
    module C where
      open IsResiduatedCommutativePomonoid ∙ᶜ-isResiduatedCommutativePomonoid public
      open IsMeetSemilattice ∧ᶜ-isMeet public using (infimum; x∧y≤x; x∧y≤y; ∧-greatest)
      open IsJoinSemilattice ∨ᶜ-isJoin public using (supremum; ∨-least; x≤x∨y; y≤x∨y)

  record Chu : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
    no-eta-equality
    field
      pos : Carrier
      neg : Carrier
      int : (pos ∙ᶜ neg) ≤ᶜ K
  open Chu public 

  private
    variable
      W W′ W₁ W₂ : Chu
      X X′ X₁ X₂ : Chu
      Y Y′ Y₁ Y₂ : Chu
      Z Z′ Z₁ Z₂ : Chu

  record _≤_ (X Y : Chu) : Set ℓ₂ where
    no-eta-equality
    field
      fpos : X .pos ≤ᶜ Y .pos
      fneg : Y .neg ≤ᶜ X .neg
  open _≤_ public
  infix 4 _≤_

  _≈_ : Rel Chu ℓ₂
  _≈_ = SymCore _≤_

  mk-≈ : X .pos ≈ᶜ Y .pos → X .neg ≈ᶜ Y .neg → X ≈ Y
  mk-≈ pos-eq neg-eq .Product.proj₁ .fpos = C.reflexive pos-eq
  mk-≈ pos-eq neg-eq .Product.proj₁ .fneg = C.reflexive (C.Eq.sym neg-eq)
  mk-≈ pos-eq neg-eq .Product.proj₂ .fpos = C.reflexive (C.Eq.sym pos-eq)
  mk-≈ pos-eq neg-eq .Product.proj₂ .fneg = C.reflexive neg-eq

  ≤-refl : Reflexive _≤_
  ≤-refl .fpos = C.refl
  ≤-refl .fneg = C.refl

  ≤-trans : Transitive _≤_
  ≤-trans x≤y y≤z .fpos = C.trans (x≤y .fpos) (y≤z .fpos)
  ≤-trans x≤y y≤z .fneg = C.trans (y≤z .fneg) (x≤y .fneg)

  ≤-isPartialOrder : IsPartialOrder _≈_ _≤_
  ≤-isPartialOrder = SymCore.isPreorder⇒isPartialOrder _≤_  record 
    { isEquivalence = PropEq.isEquivalence 
    ; reflexive     = λ { PropEq.refl → ≤-refl } 
    ; trans         = ≤-trans 
    }

  infixr 5 _>>_
  
  _>>_ : Transitive _≤ᶜ_
  _>>_ = C.trans

  -- Embedding
  embed : Carrier → Chu
  embed x .pos = x
  embed x .neg = x -∙ᶜ K
  embed x .int = C.evalʳ

  -- Negation/duality
  ¬ : Chu → Chu
  ¬ X .pos = X .neg
  ¬ X .neg = X .pos
  ¬ X .int = C.trans (C.reflexive (C.comm _ _)) (X .int)

  ¬-involutive : Involutive _≈_ ¬
  ¬-involutive X .Product.proj₁ .fpos = C.refl
  ¬-involutive X .Product.proj₁ .fneg = C.refl
  ¬-involutive X .Product.proj₂ .fpos = C.refl
  ¬-involutive X .Product.proj₂ .fneg = C.refl

  ¬-mono : Antitonic₁ _≤_ _≤_ ¬
  ¬-mono f .fpos = f .fneg
  ¬-mono f .fneg = f .fpos

  -- Monoidal structure
  ε : Chu
  ε .pos = εᶜ
  ε .neg = K
  ε .int = C.reflexive (C.identity .Product.proj₁ _)

  _⊗_ : Chu → Chu → Chu
  (X ⊗ Y) .pos = X .pos ∙ᶜ Y .pos
  (X ⊗ Y) .neg = (Y .pos -∙ᶜ X .neg) ∧ᶜ (X .pos -∙ᶜ Y .neg)
  (X ⊗ Y) .int =
    C.mono C.refl (C.x∧y≤x _ _) >>
    C.reflexive (C.assoc _ _ _) >>
    C.mono C.refl C.evalʳ >>
    X .int

  ⊗-mono : X₁ ≤ X₂ → Y₁ ≤ Y₂ → (X₁ ⊗ Y₁) ≤ (X₂ ⊗ Y₂)
  ⊗-mono f g .fpos = C.mono (f .fpos) (g .fpos)
  ⊗-mono f g .fneg =
    C.∧-greatest (C.x∧y≤x _ _ >> C.anti-monoʳ (g .fpos) (f .fneg))
                 (C.x∧y≤y _ _ >> C.anti-monoʳ (f .fpos) (g .fneg))


  ⊗-sym : (X ⊗ Y) ≤ (Y ⊗ X)
  ⊗-sym .fpos = C.reflexive (C.comm _ _)
  ⊗-sym .fneg = C.∧-greatest (C.x∧y≤y _ _) (C.x∧y≤x _ _)

{- TODO: need general (un)curry
  embed-⊗ : ∀ {x y} → embed (x ∙ y) ≤ embed x ⊗ embed y
  embed-⊗ .fpos = C.refl
  embed-⊗ .fneg = C.trans (C.x∧y≤y _ _) {!!}

  ⊗-embed : ∀ {x y} → embed x ⊗ embed y ≤ embed (x ∙ y)
  ⊗-embed .fpos = C.refl
  ⊗-embed .fneg = C.∧-greatest {!!} {!!}
-}

  private
    Λˡ : ∀ {x y z} → (x ∙ᶜ y) ≤ᶜ z → x ≤ᶜ (y -∙ᶜ z)
    Λˡ = C.residualˡ .Equivalence.to
    Λʳ : ∀ {x y z} → (x ∙ᶜ y) ≤ᶜ z → y ≤ᶜ (x -∙ᶜ z)
    Λʳ = C.residualʳ .Equivalence.to

  ⊗-identityˡ : LeftIdentity _≈_ ε _⊗_
  ⊗-identityˡ X .Product.proj₁ .fpos = C.reflexive (C.identityˡ _)
  ⊗-identityˡ X .Product.proj₁ .fneg =
    C.∧-greatest (C.residualʳ .Equivalence.to (X .int))
                 (C.residualʳ .Equivalence.to (C.reflexive (C.identityˡ _)))
  ⊗-identityˡ X .Product.proj₂ .fpos = C.reflexive (C.Eq.sym (C.identityˡ (X .pos)))
  ⊗-identityˡ X .Product.proj₂ .fneg = C.x∧y≤y _ _ >> C.reflexive (C.Eq.sym (C.identityʳ _)) >> C.evalˡ

  ⊗-identityʳ : RightIdentity _≈_ ε _⊗_
  ⊗-identityʳ X .Product.proj₁ = ≤-trans ⊗-sym (⊗-identityˡ X .Product.proj₁)
  ⊗-identityʳ X .Product.proj₂ = ≤-trans (⊗-identityˡ X .Product.proj₂) ⊗-sym

  ⊗-identity : Identity _≈_ ε _⊗_
  ⊗-identity = ⊗-identityˡ , ⊗-identityʳ

  -- FIXME: This really probably should use reasoning syntax.
  ⊗-assoc : Associative _≈_ _⊗_
  ⊗-assoc X Y Z .Product.proj₁ .fpos = C.reflexive (C.assoc _ _ _)
  ⊗-assoc X Y Z .Product.proj₁ .fneg =
    C.∧-greatest 
      (Λˡ 
        (C.∧-greatest
          (Λˡ (  C.mono (C.mono (C.x∧y≤x _ _) C.refl) C.refl 
              >> C.reflexive (C.assoc _ _ _) 
              >> C.mono C.refl (C.reflexive (C.comm _ _)) 
              >> C.evalˡ))
          (Λˡ (  C.mono (C.mono (C.x∧y≤y _ _ 
              >> C.anti-monoʳ C.refl (C.x∧y≤x _ _)) C.refl) C.refl
              >> C.reflexive (C.assoc _ _ _) 
              >> C.mono C.refl (C.reflexive (C.comm _ _)) 
              >> C.reflexive (C.Eq.sym (C.assoc _ _ _)) 
              >> C.mono C.evalˡ C.refl 
              >> C.evalˡ))))
      (Λˡ (  C.mono (C.x∧y≤y _ _ >> C.anti-monoʳ C.refl (C.x∧y≤y _ _)) C.refl
          >> (C.reflexive (C.Eq.sym (C.assoc _ _ _)) 
          >> (C.mono C.evalˡ C.refl 
          >> C.evalˡ))))
  ⊗-assoc X Y Z .Product.proj₂ .fpos =
    C.reflexive (C.Eq.sym (C.assoc _ _ _))
  ⊗-assoc X Y Z .Product.proj₂ .fneg =
    C.∧-greatest
      (Λˡ (  C.mono (C.x∧y≤x _ _ >> C.anti-monoʳ C.refl (C.x∧y≤x _ _)) C.refl 
          >> (C.mono C.refl (C.reflexive (C.comm _ _)) 
          >> (C.reflexive (C.Eq.sym (C.assoc _ _ _)) 
          >> (C.mono C.evalˡ C.refl 
          >> C.evalˡ)))))
      (Λˡ (C.∧-greatest
            (Λˡ (  C.mono (  C.mono (C.x∧y≤x _ _ 
                        >> C.anti-monoʳ C.refl (C.x∧y≤y _ _)) C.refl) C.refl
                >> C.reflexive (C.assoc _ _ _) >> C.mono C.refl (C.reflexive (C.comm _ _)) 
                >> C.reflexive (C.Eq.sym (C.assoc _ _ _)) 
                >> (C.mono C.evalˡ C.refl >> C.evalˡ)))
            (Λˡ (C.mono (C.mono (C.x∧y≤y _ _) C.refl) C.refl 
                >> C.reflexive (C.assoc _ _ _) 
                >> C.evalˡ))))

  ⊗-isPomonoid : IsPomonoid _≈_ _≤_ _⊗_ ε
  ⊗-isPomonoid .IsPomonoid.isPosemigroup .IsPosemigroup.isPomagma .IsPomagma.isPartialOrder = ≤-isPartialOrder
  ⊗-isPomonoid .IsPomonoid.isPosemigroup .IsPosemigroup.isPomagma .IsPomagma.mono = ⊗-mono
  ⊗-isPomonoid .IsPomonoid.isPosemigroup .IsPosemigroup.assoc = ⊗-assoc
  ⊗-isPomonoid .IsPomonoid.identity = ⊗-identity

  ⊗-isCommutativePomonoid : IsCommutativePomonoid _≈_ _≤_ _⊗_ ε
  ⊗-isCommutativePomonoid .IsCommutativePomonoid.isPomonoid = ⊗-isPomonoid
  ⊗-isCommutativePomonoid .IsCommutativePomonoid.comm x y = ⊗-sym , ⊗-sym

  ------------------------------------------------------------------------------
  -- We have a *-autonomous preorder:

  *-aut : ∀ {X Y Z} → (X ⊗ Y) ≤ ¬ Z → X ≤ ¬ (Y ⊗ Z)
  *-aut m .fpos = C.∧-greatest (Λʳ (C.mono (m .fneg >> C.x∧y≤y _ _) C.refl >> C.evalˡ)) (Λˡ (m .fpos))
  *-aut m .fneg = C.reflexive (C.comm _ _) >> C.mono (m .fneg >> C.x∧y≤x _ _) C.refl >> C.evalˡ

  *-aut⁻¹ : ∀ {X Y Z} → X ≤ ¬ (Y ⊗ Z) → (X ⊗ Y) ≤ ¬ Z
  *-aut⁻¹ m .fpos = C.mono (m .fpos >> C.x∧y≤y _ _) C.refl >> C.evalˡ
  *-aut⁻¹ m .fneg =
    C.∧-greatest (Λʳ (m .fneg)) (Λʳ (C.mono (m .fpos >> C.x∧y≤x _ _) C.refl >> C.evalˡ))

  ⊗-isStarAutonomous : IsStarAutonomous _≈_ _≤_ _⊗_ ε ¬
  ⊗-isStarAutonomous .IsStarAutonomous.isCommutativePomonoid = ⊗-isCommutativePomonoid
  ⊗-isStarAutonomous .IsStarAutonomous.¬-mono = ¬-mono
  ⊗-isStarAutonomous .IsStarAutonomous.¬-involutive = ¬-involutive
  ⊗-isStarAutonomous .IsStarAutonomous.*-aut = *-aut
  ⊗-isStarAutonomous .IsStarAutonomous.*-aut⁻¹ = *-aut⁻¹

  open IsStarAutonomous ⊗-isStarAutonomous public
    using
      ( _⅋_
      ; ⅋-cong
      ; ⅋-mono
      ; ⅋-assoc
      ; ⅋-comm
      ; ⅋-identityˡ
      ; ⅋-identityʳ
      )

  ------------------------------------------------------------------------------
  -- Additive structure

  •-∨-distrib : (x ∙ᶜ (y ∨ᶜ z)) ≤ᶜ ((x ∙ᶜ y) ∨ᶜ (x ∙ᶜ z))
  •-∨-distrib {x} {y} {z} =
    supremum∧residualʳ⇒distribˡ C.isPreorder {_∨ᶜ_} {_∙ᶜ_} C.supremum C.residualʳ x y z

  _&_ : Chu → Chu → Chu
  (X & Y) .pos = X .pos ∧ᶜ Y .pos
  (X & Y) .neg = X .neg ∨ᶜ Y .neg
  (X & Y) .int = •-∨-distrib >> C.∨-least (C.mono (C.x∧y≤x _ _) C.refl >> X .int) (C.mono (C.x∧y≤y _ _) C.refl >> Y .int)

  proj₁ : (X & Y) ≤ X
  proj₁ .fpos = C.x∧y≤x _ _
  proj₁ .fneg = C.x≤x∨y _ _

  proj₂ : (X & Y) ≤ Y
  proj₂ .fpos = C.x∧y≤y _ _
  proj₂ .fneg = C.y≤x∨y _ _

  ⟨_,_⟩ : X ≤ Y → X ≤ Z → X ≤ (Y & Z)
  ⟨_,_⟩ f g .fpos = C.∧-greatest (f .fpos) (g .fpos)
  ⟨_,_⟩ f g .fneg = C.∨-least (f .fneg) (g .fneg)

  &-infimum : Infimum _≤_ _&_
  &-infimum X Y = proj₁ , proj₂ , λ Z → ⟨_,_⟩

  &-isMeet : IsMeetSemilattice _≈_ _≤_ _&_
  &-isMeet .IsMeetSemilattice.isPartialOrder = ≤-isPartialOrder
  &-isMeet .IsMeetSemilattice.infimum = &-infimum

  ------------------------------------------------------------------------------
  -- Self-dual operators on Chu, arising from duoidal structures on
  -- the underlying order.
  module SelfDual
      {_◁ᶜ_ : Op₂ Carrier}
      {ιᶜ : Carrier}
      (∙-◁-isDuoidal : IsDuoidal _≈ᶜ_ _≤ᶜ_ _∙ᶜ_ _◁ᶜ_ εᶜ ιᶜ)
      (K-m : (K ◁ᶜ K) ≤ᶜ K)
      (K-u : ιᶜ ≤ᶜ K) -- K is a ◁-monoid
    where

    private
      module Duo = IsDuoidal ∙-◁-isDuoidal

    _◁_ : Chu → Chu → Chu
    (X ◁ Y) .pos = X .pos ◁ᶜ Y .pos
    (X ◁ Y) .neg = X .neg ◁ᶜ Y .neg
    (X ◁ Y) .int = Duo.∙-◁-entropy _ _ _ _ >> (Duo.◁-mono (X .int) (Y .int) >> K-m)

    self-dual : ¬ (X ◁ Y) ≈ (¬ X ◁ ¬ Y)
    self-dual .Product.proj₁ .fpos = C.refl
    self-dual .Product.proj₁ .fneg = C.refl
    self-dual .Product.proj₂ .fpos = C.refl
    self-dual .Product.proj₂ .fneg = C.refl

    ι : Chu
    ι .pos = ιᶜ
    ι .neg = ιᶜ
    ι .int = Duo.∙-idem-ι >> K-u

    -- ◁ is self-dual, so the structure is quite repetitive...
    ◁-mono : Monotonic₂ _≤_ _≤_ _≤_ _◁_
    ◁-mono f g .fpos = Duo.◁-mono (f .fpos) (g .fpos)
    ◁-mono f g .fneg = Duo.◁-mono (f .fneg) (g .fneg)

    ◁-assoc : Associative _≈_ _◁_
    ◁-assoc x y z = mk-≈ (Duo.◁-assoc _ _ _) (Duo.◁-assoc _ _ _)

    ◁-identityˡ : LeftIdentity _≈_ ι _◁_
    ◁-identityˡ x = mk-≈ (Duo.◁-identityˡ _) (Duo.◁-identityˡ _)

    ◁-identityʳ : RightIdentity _≈_ ι _◁_
    ◁-identityʳ x = mk-≈ (Duo.◁-identityʳ _) (Duo.◁-identityʳ _)

    ◁-identity : Identity _≈_ ι _◁_
    ◁-identity = ◁-identityˡ , ◁-identityʳ

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

    -- Transpose for any closed duoidal category
    private
      -∙ᶜ-◁ᶜ-entropy : Entropy _≤ᶜ_ _◁ᶜ_ _-∙ᶜ_
      -∙ᶜ-◁ᶜ-entropy w x y z = Λˡ (Duo.∙-◁-entropy _ _ _ _ >> Duo.◁-mono C.evalˡ C.evalˡ)

    ◁-medial : ((w ∧ᶜ x) ◁ᶜ (y ∧ᶜ z)) ≤ᶜ ((w ◁ᶜ y) ∧ᶜ (x ◁ᶜ z))
    ◁-medial = C.∧-greatest (Duo.◁-mono (C.x∧y≤x _ _) (C.x∧y≤x _ _)) (Duo.◁-mono (C.x∧y≤y _ _) (C.x∧y≤y _ _))

    ⊗-◁-entropy : Entropy _≤_ _⊗_ _◁_
    ⊗-◁-entropy W X Y Z .fpos = Duo.∙-◁-entropy _ _ _ _
    ⊗-◁-entropy W X Y Z .fneg = ◁-medial >> C.∧-greatest (C.x∧y≤x _ _ >> -∙ᶜ-◁ᶜ-entropy _ _ _ _) (C.x∧y≤y _ _ >> -∙ᶜ-◁ᶜ-entropy _ _ _ _)

    ⊗-idem-ι : (ι ⊗ ι) ≤ ι
    ⊗-idem-ι .fpos = Duo.∙-idem-ι
    ⊗-idem-ι .fneg = C.∧-greatest (Λˡ Duo.∙-idem-ι) (Λˡ Duo.∙-idem-ι)

    ◁-idem-ε : ε ≤ (ε ◁ ε)
    ◁-idem-ε .fpos = Duo.◁-idem-ε
    ◁-idem-ε .fneg = K-m

    ε≤ι : ε ≤ ι
    ε≤ι .fpos = Duo.ε≲ι
    ε≤ι .fneg = K-u

    ⊗-◁-isDuoidal : IsDuoidal _≈_ _≤_ _⊗_ _◁_ ε ι
    ⊗-◁-isDuoidal .IsDuoidal.∙-isPomonoid = ⊗-isPomonoid
    ⊗-◁-isDuoidal .IsDuoidal.◁-isPomonoid = ◁-isPomonoid
    ⊗-◁-isDuoidal .IsDuoidal.∙-◁-entropy = ⊗-◁-entropy
    ⊗-◁-isDuoidal .IsDuoidal.∙-idem-ι = ⊗-idem-ι
    ⊗-◁-isDuoidal .IsDuoidal.◁-idem-ε = ◁-idem-ε
    ⊗-◁-isDuoidal .IsDuoidal.ε≲ι = ε≤ι
