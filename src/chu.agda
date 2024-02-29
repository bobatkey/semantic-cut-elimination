{-# OPTIONS --postfix-projections --safe --without-K #-}

module chu where

-- If we have a preordered closed symmetric monoid with finite meets
-- and chosen element K, then the Chu construction is a *-autonomous
-- category. Moreover, if the preorder is duoidal, and K is a monoid,
-- then Chu(A,K) is duoidal.

-- X+ ⊗ X- ==> ⊥ is satisfied by X- = (X+ ⊸ ⊥)

-- if we require X+ ⊗ X- ≅ ⊥, then X+ ≅ X- ⊸ ⊥?

-- The profunctor version is more general, because we don't
-- necessarily get a duality?

open import Level
open import Data.Product
open import basics

module Construction {a b} {A : Set a}
          {_≤_ : A → A → Set b}
          (≤-isPreorder : IsPreorder _≤_)
          {_•_ : A → A → A} {ε : A}
          (•-isMonoid : IsMonoid ≤-isPreorder _•_ ε)
          (•-sym : ∀ {x y} → (x • y) ≤ (y • x))
          {_-•_ : A → A → A}
          (-•-isClosure : IsClosure ≤-isPreorder •-isMonoid _-•_)
          {_∧_ : A → A → A}
          (∧-isMeet : IsMeet ≤-isPreorder _∧_)
          {_∨_ : A → A → A}
          (∨-isJoin : IsJoin ≤-isPreorder _∨_)
          (K : A)
        where

  record Chu : Set (suc (a ⊔ b)) where
    no-eta-equality
    field
      pos : A
      neg : A
      int : (pos • neg) ≤ K
  open Chu

  record _==>_ (X Y : Chu) : Set b where
    no-eta-equality
    field
      fpos : X .pos ≤ Y .pos
      fneg : Y .neg ≤ X .neg
  open _==>_
  infix 4 _==>_

  _≅_ = SymmetricClosure _==>_

  open IsPreorder ≤-isPreorder
  open IsMonoid •-isMonoid
  open IsMeet ∧-isMeet renaming (mono to ∧-mono)
  open IsJoin ∨-isJoin renaming (mono to ∨-mono)
  open IsClosure -•-isClosure renaming (-∙-mono to -•-mono)

  _>>_ : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
  _>>_ = trans
  infix 5 _>>_

  ==>-isPreorder : IsPreorder _==>_
  ==>-isPreorder .IsPreorder.refl .fpos = refl
  ==>-isPreorder .IsPreorder.refl .fneg = refl
  ==>-isPreorder .IsPreorder.trans f g .fpos = f .fpos >> g . fpos
  ==>-isPreorder .IsPreorder.trans f g .fneg = g .fneg >> f .fneg

  open IsPreorder ==>-isPreorder renaming (refl to id; trans to ==>-trans)
  _∘_ : ∀ {X Y Z} → (Y ==> Z) → (X ==> Y) → X ==> Z
  f ∘ g = ==>-trans g f

  -- Negation/duality
  ¬ : Chu → Chu
  ¬ X .pos = X .neg
  ¬ X .neg = X .pos
  ¬ X .int = trans •-sym (X .int)

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
  I .int = lunit .proj₁

  _⊗_ : Chu → Chu → Chu
  (X ⊗ Y) .pos = X .pos • Y .pos
  (X ⊗ Y) .neg = (Y .pos -• X .neg) ∧ (X .pos -• Y .neg)
  (X ⊗ Y) .int =
    mono refl π₁ >> (assoc .proj₁ >> (mono refl •-sym >> (mono refl eval >> X .int)))

  ⊗-mono : ∀ {X₁ Y₁ X₂ Y₂} → X₁ ==> X₂ → Y₁ ==> Y₂ → (X₁ ⊗ Y₁) ==> (X₂ ⊗ Y₂)
  ⊗-mono f g .fpos = mono (f .fpos) (g .fpos)
  ⊗-mono f g .fneg = ∧-mono (-•-mono (g .fpos) (f .fneg)) (-•-mono (f .fpos) (g .fneg))

  ⊗-sym : ∀ {X Y} → (X ⊗ Y) ==> (Y ⊗ X)
  ⊗-sym .fpos = •-sym
  ⊗-sym .fneg = ⟨ π₂ , π₁ ⟩

  ⊗-lunit : ∀ {X} → (I ⊗ X) ≅ X
  ⊗-lunit {X} .proj₁ .fpos = lunit .proj₁
  ⊗-lunit {X} .proj₁ .fneg = ⟨ lambda (•-sym >> X .int) , lambda (runit .proj₁) ⟩
  ⊗-lunit {X} .proj₂ .fpos = lunit .proj₂
  ⊗-lunit {X} .proj₂ .fneg = π₂ >> (runit .proj₂ >> eval)

  ⊗-runit : ∀ {X} → (X ⊗ I) ≅ X
  ⊗-runit .proj₁ = ==>-trans ⊗-sym (⊗-lunit .proj₁)
  ⊗-runit .proj₂ = ==>-trans (⊗-lunit .proj₂) ⊗-sym

  ⊗-assoc : ∀ {X Y Z} → ((X ⊗ Y) ⊗ Z) ≅ (X ⊗ (Y ⊗ Z))
  ⊗-assoc .proj₁ .fpos = assoc .proj₁
  ⊗-assoc .proj₁ .fneg =
    ⟨ lambda
        ⟨ lambda (mono (mono π₁ refl) refl >> (assoc .proj₁ >> (mono refl •-sym >> eval)))
        , lambda (mono (mono (π₂ >> -•-mono refl π₁) refl) refl >> (assoc .proj₁ >> (mono refl •-sym >> (assoc .proj₂ >> (mono eval refl >> eval)))))
        ⟩
    , lambda (mono (π₂ >> -•-mono refl π₂) refl >> (assoc .proj₂ >> (mono eval refl >> eval)))
    ⟩
  ⊗-assoc .proj₂ .fpos = assoc .proj₂
  ⊗-assoc .proj₂ .fneg =
    ⟨ lambda (mono (π₁ >> -•-mono refl π₁) refl >> (mono refl •-sym >> (assoc .proj₂ >> (mono eval refl >> eval))))
    , lambda ⟨ lambda (mono (mono (π₁ >> -•-mono refl π₂) refl) refl >> (assoc .proj₁ >> (mono refl •-sym >> (assoc .proj₂ >> (mono eval refl >> eval)))))
             , lambda (mono (mono π₂ refl) refl >> (assoc .proj₁ >> eval))
             ⟩
    ⟩

  ⊗-isMonoid : IsMonoid ==>-isPreorder _⊗_ I
  ⊗-isMonoid .IsMonoid.mono {X₁}{Y₁}{X₂}{Y₂} = ⊗-mono {X₁}{Y₁}{X₂}{Y₂}
  ⊗-isMonoid .IsMonoid.assoc {X}{Y}{Z} = ⊗-assoc {X}{Y}{Z}
  ⊗-isMonoid .IsMonoid.lunit {X} = ⊗-lunit {X}
  ⊗-isMonoid .IsMonoid.runit {X} = ⊗-runit {X}

  -- We have a *-autonomous preorder:

  *-aut : ∀ {X Y Z} → (X ⊗ Y) ==> ¬ Z → X ==> ¬ (Y ⊗ Z)
  *-aut m .fpos = ⟨ lambda (•-sym >> (mono (m .fneg >> π₂) refl >> eval)) , lambda (m .fpos) ⟩
  *-aut m .fneg = •-sym >> (mono (m .fneg >> π₁) refl >> eval)

  *-aut⁻¹ : ∀ {X Y Z} → X ==> ¬ (Y ⊗ Z) → (X ⊗ Y) ==> ¬ Z
  *-aut⁻¹ m .fpos = mono (m .fpos >> π₂) refl >> eval
  *-aut⁻¹ m .fneg = ⟨ lambda (•-sym >> m .fneg) , lambda (•-sym >> (mono (m .fpos >> π₁) refl >> eval)) ⟩

  ------------------------------------------------------------------------------
  _⅋_ : Chu → Chu → Chu
  X ⅋ Y = ¬ (¬ X ⊗ ¬ Y)

  ⅋-mono : ∀ {X₁ Y₁ X₂ Y₂} → X₁ ==> X₂ → Y₁ ==> Y₂ → (X₁ ⅋ Y₁) ==> (X₂ ⅋ Y₂)
  ⅋-mono m₁ m₂ = ¬-mono (⊗-mono (¬-mono m₁) (¬-mono m₂))

  ⅋-sym : ∀ {X Y} → (X ⅋ Y) ==> (Y ⅋ X)
  ⅋-sym = ¬-mono ⊗-sym

  -- FIXME: ⅋-isMonoid

  -- FIXME: linear distributivity

  identity : ∀ {X} → I ==> (¬ X ⅋ X)
  identity = *-aut (⊗-lunit .proj₁)

  _⊸_ : Chu → Chu → Chu
  X ⊸ Y = ¬ X ⅋ Y

  apply : ∀ {X Y} → ((X ⊸ Y) ⊗ X) ==> Y
  apply = ==>-trans (*-aut⁻¹ (¬-mono (⊗-mono (involution .proj₁) id))) (involution .proj₂)

  -- linear distributivity law, to interpret “switch” in BV/MAV
  lin-distrib : ∀ {X Y Z} → (X ⊗ (Y ⅋ Z)) ==> ((X ⊗ Y) ⅋ Z)
  lin-distrib =
    ==>-trans (*-aut (
    ==>-trans (
    ==>-trans (⊗-assoc .proj₁)
              (⊗-mono id (==>-trans (⊗-mono (==>-trans (⅋-mono id (involution .proj₁)) ⅋-sym) id) apply)))
              (involution .proj₁)))
    ⅋-sym

  ------------------------------------------------------------------------------
  -- Additive structure

  -- deduce distributivity from closure-
  •-∨-distrib : ∀ {x y z} → (x • (y ∨ z)) ≤ ((x • y) ∨ (x • z))
  •-∨-distrib =
    •-sym >> lambda⁻¹ [ lambda (•-sym >> inl) , lambda (•-sym >> inr) ]

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

  -- Self-dual operators on Chu, arising from duoidal structures on
  -- the underlying order.
  module SelfDual {_▷_ : A → A → A} {ι : A}
                  (▷-isMonoid : IsMonoid ≤-isPreorder _▷_ ι)
                  (K-m : (K ▷ K) ≤ K) (K-u : ι ≤ K) -- K is a ▷-monoid
                  (▷-exchange : ∀ {w x y z} → ((w ▷ x) • (y ▷ z)) ≤ ((w • y) ▷ (x • z)))
                  -- (co)monoid structures on the units
                  (μ : (ι • ι) ≤ ι)
                  -- (Δ : ε ≤ (ε ▷ ε)) -- what is this needed for?
                  -- (u : ε ≤ ι) -- what is this needed for?
                  where

    open IsMonoid ▷-isMonoid renaming (mono  to ▷-mono;
                                       assoc to ▷-assoc;
                                       lunit to ▷-lunit;
                                       runit to ▷-runit)

    _⍮_ : Chu → Chu → Chu
    (X ⍮ Y) .pos = X .pos ▷ Y .pos
    (X ⍮ Y) .neg = X .neg ▷ Y .neg
    (X ⍮ Y) .int = ▷-exchange >> (▷-mono (X .int) (Y .int) >> K-m)

    J : Chu
    J .pos = ι
    J .neg = ι
    J .int = μ >> K-u

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

    -- transpose for any closed duoidal category
    ▷-exchange' : ∀ {w x y z} → ((w -• x) ▷ (y -• z)) ≤ ((w ▷ y) -• (x ▷ z))
    ▷-exchange' = lambda (▷-exchange >> ▷-mono eval eval)

    ▷-medial : ∀ {A B C D} → ((A ∧ B) ▷ (C ∧ D)) ≤ ((A ▷ C) ∧ (B ▷ D))
    ▷-medial = ⟨ ▷-mono π₁ π₁ , ▷-mono π₂ π₂ ⟩

    exchange : ∀ {W X Y Z} → ((W ⍮ X) ⊗ (Y ⍮ Z)) ==> ((W ⊗ Y) ⍮ (X ⊗ Z))
    exchange .fpos = ▷-exchange
    exchange .fneg = ▷-medial >> ∧-mono ▷-exchange' ▷-exchange'

    mu : (J ⊗ J) ==> J
    mu .fpos = μ
    mu .fneg = ⟨ lambda μ , lambda μ ⟩

    -- presuambly Δ and eps are derivable too if we assume them
