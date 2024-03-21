{-# OPTIONS --postfix-projections --safe --without-K #-}

module Algebra.Chu where

-- If we have a preordered closed symmetric monoid with finite meets
-- and chosen element K, then the Chu construction is a *-autonomous
-- preorder. Moreover, if the preorder is duoidal, and K is a
-- ▷-monoid, then Chu(A,K) is duoidal.

open import Level
open import Data.Product using (proj₁; proj₂; _,_; swap)
open import Prelude
open import Relation.Binary.Construct.Core.Symmetric using (SymCore)
open import Function using (Equivalence)
open import Algebra.Ordered
open import Algebra.Ordered.Structures.Residuated
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
  open IsMeetSemilattice ∧-isMeet hiding (refl; reflexive; trans; module Eq) -- why on earth does this export refl?


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

  ==>-refl : Reflexive _==>_
  ==>-refl .fpos = refl
  ==>-refl .fneg = refl

  ==>-trans : Transitive _==>_
  ==>-trans x≤y y≤z .fpos = trans (x≤y .fpos) (y≤z .fpos)
  ==>-trans x≤y y≤z .fneg = trans (y≤z .fneg) (x≤y .fneg)

  ==>-isPartialOrder : IsPartialOrder _≅_ _==>_
  ==>-isPartialOrder .IsPartialOrder.isPreorder .IsPreorder.isEquivalence .IsEquivalence.refl = ==>-refl , ==>-refl
  ==>-isPartialOrder .IsPartialOrder.isPreorder .IsPreorder.isEquivalence .IsEquivalence.sym = swap
  ==>-isPartialOrder .IsPartialOrder.isPreorder .IsPreorder.isEquivalence .IsEquivalence.trans (ϕ₁ , ϕ₂) (ψ₁ , ψ₂) = (==>-trans ϕ₁ ψ₁) , (==>-trans ψ₂ ϕ₂)
  ==>-isPartialOrder .IsPartialOrder.isPreorder .IsPreorder.reflexive = proj₁
  ==>-isPartialOrder .IsPartialOrder.isPreorder .IsPreorder.trans = ==>-trans
  ==>-isPartialOrder .IsPartialOrder.antisym = _,_

  _>>_ : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
  _>>_ = trans
  infixr 5 _>>_

  _∘_ : ∀ {X Y Z} → (Y ==> Z) → (X ==> Y) → X ==> Z
  f ∘ g = ==>-trans g f

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

  ⊗-isCommutativePomonoid : IsCommutativePomonoid _≅_ _==>_ _⊗_ I
  ⊗-isCommutativePomonoid .IsCommutativePomonoid.isPomonoid .IsPomonoid.isPosemigroup .IsPosemigroup.isPomagma .IsPomagma.isPartialOrder = ==>-isPartialOrder
  ⊗-isCommutativePomonoid .IsCommutativePomonoid.isPomonoid .IsPomonoid.isPosemigroup .IsPosemigroup.isPomagma .IsPomagma.mono = ⊗-mono
  ⊗-isCommutativePomonoid .IsCommutativePomonoid.isPomonoid .IsPomonoid.isPosemigroup .IsPosemigroup.assoc = ⊗-assoc
  ⊗-isCommutativePomonoid .IsCommutativePomonoid.isPomonoid .IsPomonoid.identity = ⊗-lunit , ⊗-runit
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

{-
  ⊗-isStarAutonomous : IsStarAuto ==>-isPreorder ⊗-isMonoid ⊗-sym ¬
  ⊗-isStarAutonomous .IsStarAuto.¬-mono = ¬-mono
  ⊗-isStarAutonomous .IsStarAuto.involution = involution
  ⊗-isStarAutonomous .IsStarAuto.*-aut = *-aut
  ⊗-isStarAutonomous .IsStarAuto.*-aut⁻¹ = *-aut⁻¹

  open IsStarAuto ⊗-isStarAutonomous hiding (¬-mono; involution; *-aut; *-aut⁻¹) public

  ------------------------------------------------------------------------------
  -- Additive structure

  •-∨-distrib : ∀ {x y z} → (x • (y ∨ z)) ≤ ((x • y) ∨ (x • z))
  •-∨-distrib = ∙-∨-distrib ≤-isPreorder •-isMonoid •-sym -•-isClosure ∨-isJoin

  _&_ : Chu → Chu → Chu
  (X & Y) .pos = X .pos ∧ Y .pos
  (X & Y) .neg = X .neg ∨ Y .neg
  (X & Y) .int = •-∨-distrib >> [ (mono π₁ refl >> X .int) , (mono π₂ refl >> Y .int) ]

  fst : ∀ {X Y} → (X & Y) ==> X
  fst .fpos = π₁
  fst .fneg = inl

  snd : ∀ {X Y} → (X & Y) ==> Y
  snd .fpos = π₂
  snd .fneg = inr

  pair : ∀ {X Y Z} → (X ==> Y) → (X ==> Z) → X ==> (Y & Z)
  pair f g .fpos = ⟨ f .fpos , g .fpos ⟩
  pair f g .fneg = [ f .fneg , g .fneg ]

  &-isMeet : IsMeet ==>-isPreorder _&_
  &-isMeet .IsMeet.π₁ = fst
  &-isMeet .IsMeet.π₂ = snd
  &-isMeet .IsMeet.⟨_,_⟩ = pair

  _⊕_ : Chu → Chu → Chu
  X ⊕ Y = ¬ (¬ X & ¬ Y)

  -- FIXME: ⊕-isJoin

  ------------------------------------------------------------------------------
  -- Self-dual operators on Chu, arising from duoidal structures on
  -- the underlying order.
  module SelfDual {_▷_ : A → A → A} {ι : A}
                  (▷-isMonoid : IsMonoid ≤-isPreorder _▷_ ι)
                  (K-m : (K ▷ K) ≤ K) (K-u : ι ≤ K) -- K is a ▷-monoid
                  (•-▷-isDuoidal : IsDuoidal ≤-isPreorder •-isMonoid ▷-isMonoid)
                where

    open IsMonoid ▷-isMonoid renaming (mono  to ▷-mono;
                                       assoc to ▷-assoc;
                                       lunit to ▷-lunit;
                                       runit to ▷-runit)
    open IsDuoidal •-▷-isDuoidal

    _⍮_ : Chu → Chu → Chu
    (X ⍮ Y) .pos = X .pos ▷ Y .pos
    (X ⍮ Y) .neg = X .neg ▷ Y .neg
    (X ⍮ Y) .int = entropy >> (▷-mono (X .int) (Y .int) >> K-m)

    self-dual : ∀ {X Y} → ¬ (X ⍮ Y) ≅ (¬ X ⍮ ¬ Y)
    self-dual .proj₁ .fpos = refl
    self-dual .proj₁ .fneg = refl
    self-dual .proj₂ .fpos = refl
    self-dual .proj₂ .fneg = refl

    J : Chu
    J .pos = ι
    J .neg = ι
    J .int = mu >> K-u

    -- ⍮ is self-dual, so the structure is quite repetitive...
    ⍮-mono : ∀ {X₁ Y₁ X₂ Y₂} → X₁ ==> X₂ → Y₁ ==> Y₂ → (X₁ ⍮ Y₁) ==> (X₂ ⍮ Y₂)
    ⍮-mono f g .fpos = ▷-mono (f .fpos) (g .fpos)
    ⍮-mono f g .fneg = ▷-mono (f .fneg) (g .fneg)

    ⍮-lunit : ∀ {X} → (J ⍮ X) ≅ X
    ⍮-lunit .proj₁ .fpos = ▷-lunit .proj₁
    ⍮-lunit .proj₁ .fneg = ▷-lunit .proj₂
    ⍮-lunit .proj₂ .fpos = ▷-lunit .proj₂
    ⍮-lunit .proj₂ .fneg = ▷-lunit .proj₁

    ⍮-runit : ∀ {X} → (X ⍮ J) ≅ X
    ⍮-runit .proj₁ .fpos = ▷-runit .proj₁
    ⍮-runit .proj₁ .fneg = ▷-runit .proj₂
    ⍮-runit .proj₂ .fpos = ▷-runit .proj₂
    ⍮-runit .proj₂ .fneg = ▷-runit .proj₁

    ⍮-assoc : ∀ {X Y Z} → ((X ⍮ Y) ⍮ Z) ≅ (X ⍮ (Y ⍮ Z))
    ⍮-assoc .proj₁ .fpos = ▷-assoc .proj₁
    ⍮-assoc .proj₁ .fneg = ▷-assoc .proj₂
    ⍮-assoc .proj₂ .fpos = ▷-assoc .proj₂
    ⍮-assoc .proj₂ .fneg = ▷-assoc .proj₁

    ⍮-isMonoid : IsMonoid ==>-isPreorder _⍮_ J
    ⍮-isMonoid .IsMonoid.mono = ⍮-mono
    ⍮-isMonoid .IsMonoid.assoc = ⍮-assoc
    ⍮-isMonoid .IsMonoid.lunit = ⍮-lunit
    ⍮-isMonoid .IsMonoid.runit = ⍮-runit

    -- transpose for any closed duoidal category
    entropy' : ∀ {w x y z} → ((w -• x) ▷ (y -• z)) ≤ ((w ▷ y) -• (x ▷ z))
    entropy' = lambda (entropy >> ▷-mono eval eval)

    ▷-medial : ∀ {A B C D} → ((A ∧ B) ▷ (C ∧ D)) ≤ ((A ▷ C) ∧ (B ▷ D))
    ▷-medial = ⟨ ▷-mono π₁ π₁ , ▷-mono π₂ π₂ ⟩

    ⍮-entropy : ∀ {W X Y Z} → ((W ⍮ X) ⊗ (Y ⍮ Z)) ==> ((W ⊗ Y) ⍮ (X ⊗ Z))
    ⍮-entropy .fpos = entropy
    ⍮-entropy .fneg = ▷-medial >> ∧-mono entropy' entropy'

    ⍮-mu : (J ⊗ J) ==> J
    ⍮-mu .fpos = mu
    ⍮-mu .fneg = ⟨ lambda mu , lambda mu ⟩

    -- presumably Δ and eps are derivable too if we assume them
    ⊗-⍮-isDuoidal : IsDuoidal ==>-isPreorder ⊗-isMonoid ⍮-isMonoid
    ⊗-⍮-isDuoidal .IsDuoidal.entropy = ⍮-entropy
    ⊗-⍮-isDuoidal .IsDuoidal.mu = ⍮-mu
-}
