{-# OPTIONS --postfix-projections --safe --without-K #-}

module Algebra.Ordered.Construction.Chu where

-- If we have a preordered closed symmetric monoid with finite meets
-- and chosen element K, then the Chu construction is a *-autonomous
-- preorder. Moreover, if the preorder is duoidal, and K is a
-- ◁-monoid, then Chu(A,K) is duoidal.

open import Level
open import Data.Product using (proj₁; proj₂; _,_; swap)
open import Relation.Binary.Construct.Core.Symmetric using (SymCore)
open import Function using (Equivalence)
open import Algebra using (Associative; LeftIdentity; RightIdentity)
open import Algebra.Ordered
open import Algebra.Ordered.Consequences using (supremum∧residualʳ⇒distribˡ)
open import Algebra.Ordered.Structures.Residuated
open import Algebra.Ordered.Structures.Duoidal using (IsDuoidal)
open import Algebra.Ordered.Structures.StarAuto using (IsStarAuto)
open import Relation.Binary
  using (Reflexive; Transitive; IsPartialOrder; IsPreorder; IsEquivalence)
open import Relation.Binary.Lattice using (IsMeetSemilattice; IsJoinSemilattice)

module Construction {a b c}
           {A : Set a}
           {_≈_ : A → A → Set b}
           {_≤_ : A → A → Set c}
           {_∙_ : A → A → A}
           {ε : A}
           {_-∙_ : A → A → A}
           (isResiduatedCommutativePomonoid :
              IsResiduatedCommutativePomonoid _≈_ _≤_ _∙_ _-∙_ ε)
           {_∧_ : A → A → A}
           (∧-isMeet : IsMeetSemilattice _≈_ _≤_ _∧_)
           {_∨_ : A → A → A}
           (∨-isJoin : IsJoinSemilattice _≈_ _≤_ _∨_)
           (K : A)
        where

  open IsResiduatedCommutativePomonoid isResiduatedCommutativePomonoid
  open IsMeetSemilattice ∧-isMeet using (x∧y≤x; x∧y≤y; ∧-greatest)
  open IsJoinSemilattice ∨-isJoin using (supremum; ∨-least; x≤x∨y; y≤x∨y)


  record Chu : Set (suc (a ⊔ b ⊔ c)) where
    no-eta-equality
    field
      pos : A
      neg : A
      int : (pos ∙ neg) ≤ K
  open Chu

  record _==>_ (X Y : Chu) : Set c where
    no-eta-equality
    field
      fpos : X .pos ≤ Y .pos
      fneg : Y .neg ≤ X .neg
  open _==>_
  infix 4 _==>_

  _≅_ = SymCore _==>_

  mk-≅ : ∀ {X Y} → (X .pos ≈ Y .pos) → (X .neg ≈ Y .neg) → X ≅ Y
  mk-≅ pos-eq neg-eq .proj₁ .fpos = reflexive pos-eq
  mk-≅ pos-eq neg-eq .proj₁ .fneg = reflexive (Eq.sym neg-eq)
  mk-≅ pos-eq neg-eq .proj₂ .fpos = reflexive (Eq.sym pos-eq)
  mk-≅ pos-eq neg-eq .proj₂ .fneg = reflexive neg-eq

  ==>-refl : Reflexive _==>_
  ==>-refl .fpos = refl
  ==>-refl .fneg = refl

  ==>-trans : Transitive _==>_
  ==>-trans x≤y y≤z .fpos = trans (x≤y .fpos) (y≤z .fpos)
  ==>-trans x≤y y≤z .fneg = trans (y≤z .fneg) (x≤y .fneg)

  ==>-isPreorder : IsPreorder _≅_ _==>_
  ==>-isPreorder .IsPreorder.isEquivalence .IsEquivalence.refl = ==>-refl , ==>-refl
  ==>-isPreorder .IsPreorder.isEquivalence .IsEquivalence.sym = swap
  ==>-isPreorder .IsPreorder.isEquivalence .IsEquivalence.trans (ϕ₁ , ϕ₂) (ψ₁ , ψ₂) = (==>-trans ϕ₁ ψ₁) , (==>-trans ψ₂ ϕ₂)
  ==>-isPreorder .IsPreorder.reflexive = proj₁
  ==>-isPreorder .IsPreorder.trans = ==>-trans

  ==>-isPartialOrder : IsPartialOrder _≅_ _==>_
  ==>-isPartialOrder .IsPartialOrder.isPreorder = ==>-isPreorder
  ==>-isPartialOrder .IsPartialOrder.antisym = _,_

  _>>_ : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
  _>>_ = trans
  infixr 5 _>>_

  _∘_ : ∀ {X Y Z} → (Y ==> Z) → (X ==> Y) → X ==> Z
  f ∘ g = ==>-trans g f

  -- Embedding
  embed : A → Chu
  embed x .pos = x
  embed x .neg = x -∙ K
  embed x .int = evalʳ

  -- Negation/duality
  ¬ : Chu → Chu
  ¬ X .pos = X .neg
  ¬ X .neg = X .pos
  ¬ X .int = trans (reflexive (comm _ _)) (X .int)

  involution : ∀ {X} → X ≅ ¬ (¬ X)
  involution .proj₁ .fpos = refl
  involution .proj₁ .fneg = refl
  involution .proj₂ .fpos = refl
  involution .proj₂ .fneg = refl

  ¬-mono : ∀ {X Y} → X ==> Y → ¬ Y ==> ¬ X
  ¬-mono f .fpos = f .fneg
  ¬-mono f .fneg = f .fpos

  -- Monoidal structure
  I : Chu
  I .pos = ε
  I .neg = K
  I .int = reflexive (identity .proj₁ _)

  _⊗_ : Chu → Chu → Chu
  (X ⊗ Y) .pos = X .pos ∙ Y .pos
  (X ⊗ Y) .neg = (Y .pos -∙ X .neg) ∧ (X .pos -∙ Y .neg)
  (X ⊗ Y) .int =
    mono refl (x∧y≤x _ _) >>
    reflexive (assoc _ _ _) >>
    mono refl evalʳ >>
    X .int

  ⊗-mono : ∀ {X₁ Y₁ X₂ Y₂} → X₁ ==> X₂ → Y₁ ==> Y₂ → (X₁ ⊗ Y₁) ==> (X₂ ⊗ Y₂)
  ⊗-mono f g .fpos = mono (f .fpos) (g .fpos)
  ⊗-mono f g .fneg =
    ∧-greatest (x∧y≤x _ _ >> anti-monoʳ (g .fpos) (f .fneg))
               (x∧y≤y _ _ >> anti-monoʳ (f .fpos) (g .fneg))


  ⊗-sym : ∀ {X Y} → (X ⊗ Y) ==> (Y ⊗ X)
  ⊗-sym .fpos = reflexive (comm _ _)
  ⊗-sym .fneg = ∧-greatest (x∧y≤y _ _) (x∧y≤x _ _)

{- TODO: need general (un)curry
  embed-⊗ : ∀ {x y} → embed (x ∙ y) ==> embed x ⊗ embed y
  embed-⊗ .fpos = refl
  embed-⊗ .fneg = trans (x∧y≤y _ _) {!!}

  ⊗-embed : ∀ {x y} → embed x ⊗ embed y ==> embed (x ∙ y)
  ⊗-embed .fpos = refl
  ⊗-embed .fneg = ∧-greatest {!!} {!!}
-}

  Λˡ : ∀ {x y z} → (x ∙ y) ≤ z → x ≤ (y -∙ z)
  Λˡ = residualˡ .Equivalence.to

  Λʳ : ∀ {x y z} → (x ∙ y) ≤ z → y ≤ (x -∙ z)
  Λʳ = residualʳ .Equivalence.to

  ⊗-lunit : ∀ X → (I ⊗ X) ≅ X
  ⊗-lunit X .proj₁ .fpos = reflexive (identityˡ _)
  ⊗-lunit X .proj₁ .fneg =
    ∧-greatest (residualʳ .Equivalence.to (X .int))
               (residualʳ .Equivalence.to (reflexive (identityˡ _)))
  ⊗-lunit X .proj₂ .fpos = reflexive (Eq.sym (identityˡ (X .pos)))
  ⊗-lunit X .proj₂ .fneg = x∧y≤y _ _ >> reflexive (Eq.sym (identityʳ _)) >> evalˡ

  ⊗-runit : ∀ X → (X ⊗ I) ≅ X
  ⊗-runit X .proj₁ = ==>-trans ⊗-sym (⊗-lunit X .proj₁)
  ⊗-runit X .proj₂ = ==>-trans (⊗-lunit X .proj₂) ⊗-sym

  ⊗-assoc : ∀ X Y Z → ((X ⊗ Y) ⊗ Z) ≅ (X ⊗ (Y ⊗ Z))
  ⊗-assoc X Y Z .proj₁ .fpos = reflexive (assoc _ _ _)
  ⊗-assoc X Y Z .proj₁ .fneg =
    ∧-greatest (Λˡ (∧-greatest
                     (Λˡ (mono (mono (x∧y≤x _ _) refl) refl >> reflexive (assoc _ _ _) >> mono refl (reflexive (comm _ _)) >> evalˡ))
                     (Λˡ (mono (mono (x∧y≤y _ _ >> anti-monoʳ refl (x∧y≤x _ _)) refl) refl >> reflexive (assoc _ _ _) >> mono refl (reflexive (comm _ _)) >> reflexive (Eq.sym (assoc _ _ _)) >> mono evalˡ refl >> evalˡ))))
               (Λˡ (mono (x∧y≤y _ _ >> anti-monoʳ refl (x∧y≤y _ _)) refl >> (reflexive (Eq.sym (assoc _ _ _)) >> (mono evalˡ refl >> evalˡ))))
  ⊗-assoc X Y Z .proj₂ .fpos = reflexive (Eq.sym (assoc _ _ _))
  ⊗-assoc X Y Z .proj₂ .fneg =
    ∧-greatest
      (Λˡ (mono (x∧y≤x _ _ >> anti-monoʳ refl (x∧y≤x _ _)) refl >> (mono refl (reflexive (comm _ _)) >> (reflexive (Eq.sym (assoc _ _ _)) >> (mono evalˡ refl >> evalˡ)))))
      (Λˡ (∧-greatest
            (Λˡ (mono (mono (x∧y≤x _ _ >> anti-monoʳ refl (x∧y≤y _ _)) refl) refl >> reflexive (assoc _ _ _) >> mono refl (reflexive (comm _ _)) >> reflexive (Eq.sym (assoc _ _ _)) >> (mono evalˡ refl >> evalˡ)))
            (Λˡ (mono (mono (x∧y≤y _ _) refl) refl >> reflexive (assoc _ _ _) >> evalˡ))))

  ⊗-isPomonoid : IsPomonoid _≅_ _==>_ _⊗_ I
  ⊗-isPomonoid .IsPomonoid.isPosemigroup .IsPosemigroup.isPomagma .IsPomagma.isPartialOrder = ==>-isPartialOrder
  ⊗-isPomonoid .IsPomonoid.isPosemigroup .IsPosemigroup.isPomagma .IsPomagma.mono = ⊗-mono
  ⊗-isPomonoid .IsPomonoid.isPosemigroup .IsPosemigroup.assoc = ⊗-assoc
  ⊗-isPomonoid .IsPomonoid.identity = ⊗-lunit , ⊗-runit

  ⊗-isCommutativePomonoid : IsCommutativePomonoid _≅_ _==>_ _⊗_ I
  ⊗-isCommutativePomonoid .IsCommutativePomonoid.isPomonoid = ⊗-isPomonoid
  ⊗-isCommutativePomonoid .IsCommutativePomonoid.comm = λ x y → ⊗-sym , ⊗-sym

  ------------------------------------------------------------------------------
  -- We have a *-autonomous preorder:

  *-aut : ∀ {X Y Z} → (X ⊗ Y) ==> ¬ Z → X ==> ¬ (Y ⊗ Z)
  *-aut m .fpos = ∧-greatest (Λʳ (mono (m .fneg >> x∧y≤y _ _) refl >> evalˡ)) (Λˡ (m .fpos))
  *-aut m .fneg = reflexive (comm _ _) >> mono (m .fneg >> x∧y≤x _ _) refl >> evalˡ

  *-aut⁻¹ : ∀ {X Y Z} → X ==> ¬ (Y ⊗ Z) → (X ⊗ Y) ==> ¬ Z
  *-aut⁻¹ m .fpos = mono (m .fpos >> x∧y≤y _ _) refl >> evalˡ
  *-aut⁻¹ m .fneg =
    ∧-greatest (Λʳ (m .fneg)) (Λʳ (mono (m .fpos >> x∧y≤x _ _) refl >> evalˡ))

  ⊗-isStarAutonomous : IsStarAuto _≅_ _==>_ ⊗-isCommutativePomonoid ¬
  ⊗-isStarAutonomous .IsStarAuto.¬-mono = ¬-mono
  ⊗-isStarAutonomous .IsStarAuto.involution = involution
  ⊗-isStarAutonomous .IsStarAuto.*-aut = *-aut
  ⊗-isStarAutonomous .IsStarAuto.*-aut⁻¹ = *-aut⁻¹

  open IsStarAuto ⊗-isStarAutonomous
    using (_⅋_; ⅋-cong; ⅋-mono; ⅋-assoc; ⅋-comm; ⅋-identityˡ; ⅋-identityʳ)
    public

  ------------------------------------------------------------------------------
  -- Additive structure

  •-∨-distrib : ∀ {x y z} → (x ∙ (y ∨ z)) ≤ ((x ∙ y) ∨ (x ∙ z))
  •-∨-distrib {x}{y}{z} = supremum∧residualʳ⇒distribˡ isPreorder {_∨_} {_∙_} supremum residualʳ x y z

  _&_ : Chu → Chu → Chu
  (X & Y) .pos = X .pos ∧ Y .pos
  (X & Y) .neg = X .neg ∨ Y .neg
  (X & Y) .int = •-∨-distrib >> ∨-least (mono (x∧y≤x _ _) refl >> X .int) (mono (x∧y≤y _ _) refl >> Y .int)

  fst : ∀ {X Y} → (X & Y) ==> X
  fst .fpos = x∧y≤x _ _
  fst .fneg = x≤x∨y _ _

  snd : ∀ {X Y} → (X & Y) ==> Y
  snd .fpos = x∧y≤y _ _
  snd .fneg = y≤x∨y _ _

  pair : ∀ {X Y Z} → (X ==> Y) → (X ==> Z) → X ==> (Y & Z)
  pair f g .fpos = ∧-greatest (f .fpos) (g .fpos)
  pair f g .fneg = ∨-least (f .fneg) (g .fneg)

  &-isMeet : IsMeetSemilattice _≅_ _==>_ _&_
  &-isMeet .IsMeetSemilattice.isPartialOrder = ==>-isPartialOrder
  &-isMeet .IsMeetSemilattice.infimum x y = fst , snd , λ z → pair

  ------------------------------------------------------------------------------
  -- Self-dual operators on Chu, arising from duoidal structures on
  -- the underlying order.
  module SelfDual {_◁_ : A → A → A} {ι : A}
                  (∙-◁-isDuoidal : IsDuoidal _≈_ _≤_ _∙_ _◁_ ε ι)
                  (K-m : (K ◁ K) ≤ K) (K-u : ι ≤ K) -- K is a ◁-monoid
                where

    open IsDuoidal ∙-◁-isDuoidal hiding (refl; module Eq)

    _⍮_ : Chu → Chu → Chu
    (X ⍮ Y) .pos = X .pos ◁ Y .pos
    (X ⍮ Y) .neg = X .neg ◁ Y .neg
    (X ⍮ Y) .int = ∙-◁-entropy _ _ _ _ >> (◁-mono (X .int) (Y .int) >> K-m)

    self-dual : ∀ {X Y} → ¬ (X ⍮ Y) ≅ (¬ X ⍮ ¬ Y)
    self-dual .proj₁ .fpos = refl
    self-dual .proj₁ .fneg = refl
    self-dual .proj₂ .fpos = refl
    self-dual .proj₂ .fneg = refl

    J : Chu
    J .pos = ι
    J .neg = ι
    J .int = ∙-idem-ι >> K-u

    -- ⍮ is self-dual, so the structure is quite repetitive...
    ⍮-mono : ∀ {X₁ Y₁ X₂ Y₂} → X₁ ==> X₂ → Y₁ ==> Y₂ → (X₁ ⍮ Y₁) ==> (X₂ ⍮ Y₂)
    ⍮-mono f g .fpos = ◁-mono (f .fpos) (g .fpos)
    ⍮-mono f g .fneg = ◁-mono (f .fneg) (g .fneg)

    ⍮-assoc : Associative _≅_ _⍮_
    ⍮-assoc x y z = mk-≅ (◁-assoc _ _ _) (◁-assoc _ _ _)

    ⍮-identityˡ : LeftIdentity _≅_ J _⍮_
    ⍮-identityˡ x = mk-≅ (◁-identityˡ _) (◁-identityˡ _)

    ⍮-identityʳ : RightIdentity _≅_ J _⍮_
    ⍮-identityʳ x = mk-≅ (◁-identityʳ _) (◁-identityʳ _)

    ⍮-isPomonoid : IsPomonoid _≅_ _==>_ _⍮_ J
    ⍮-isPomonoid =
      record { isPosemigroup = record {
        isPomagma = record {
          isPartialOrder = ==>-isPartialOrder ;
          mono = ⍮-mono }
        ; assoc = ⍮-assoc }
      ; identity = ⍮-identityˡ , ⍮-identityʳ }

    -- transpose for any closed duoidal category
    entropy' : ∀ {w x y z} → ((w -∙ x) ◁ (y -∙ z)) ≤ ((w ◁ y) -∙ (x ◁ z))
    entropy' = Λˡ (∙-◁-entropy _ _ _ _ >> ◁-mono evalˡ evalˡ)

    ◁-medial : ∀ {A B C D} → ((A ∧ B) ◁ (C ∧ D)) ≤ ((A ◁ C) ∧ (B ◁ D))
    ◁-medial = ∧-greatest (◁-mono (x∧y≤x _ _) (x∧y≤x _ _)) (◁-mono (x∧y≤y _ _) (x∧y≤y _ _))

    ⍮-entropy : ∀ W X Y Z → ((W ⍮ X) ⊗ (Y ⍮ Z)) ==> ((W ⊗ Y) ⍮ (X ⊗ Z))
    ⍮-entropy W X Y Z .fpos = ∙-◁-entropy _ _ _ _
    ⍮-entropy W X Y Z .fneg =
      ◁-medial >> ∧-greatest (x∧y≤x _ _ >> entropy') (x∧y≤y _ _ >> entropy')

    ⍮-mu : (J ⊗ J) ==> J
    ⍮-mu .fpos = ∙-idem-ι
    ⍮-mu .fneg = ∧-greatest (Λˡ ∙-idem-ι) (Λˡ ∙-idem-ι)

    ⍮-idem-I : I ==> (I ⍮ I)
    ⍮-idem-I .fpos = ◁-idem-ε
    ⍮-idem-I .fneg = K-m

    I==>J : I ==> J
    I==>J .fpos = ε≲ι
    I==>J .fneg = K-u

    ⊗-⍮-isDuoidal : IsDuoidal _≅_ _==>_ _⊗_ _⍮_ I J
    ⊗-⍮-isDuoidal .IsDuoidal.∙-isPomonoid = ⊗-isPomonoid
    ⊗-⍮-isDuoidal .IsDuoidal.◁-isPomonoid = ⍮-isPomonoid
    ⊗-⍮-isDuoidal .IsDuoidal.∙-◁-entropy = ⍮-entropy
    ⊗-⍮-isDuoidal .IsDuoidal.∙-idem-ι = ⍮-mu
    ⊗-⍮-isDuoidal .IsDuoidal.◁-idem-ε = ⍮-idem-I
    ⊗-⍮-isDuoidal .IsDuoidal.ε≲ι = I==>J
