------------------------------------------------------------------------
-- The Agda standard library
--
-- Ordered algebraic structures (not packed up with sets, orders,
-- operations, etc.)
------------------------------------------------------------------------

-- The contents of this module should be accessed via
-- `Algebra.Ordered`.

{-# OPTIONS --postfix-projections --without-K --safe #-}

open import Relation.Binary.Core using (Rel; _⇒_)

module Algebra.Ordered.Structures.StarAuto
  {a ℓ₁ ℓ₂} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ₁)       -- The underlying equality relation
  (_≲_ : Rel A ℓ₂)       -- The underlying order relation
  where

open import Algebra.Core
open import Algebra.Definitions _≈_
open import Algebra.Structures _≈_
open import Algebra.Ordered.Consequences
open import Algebra.Ordered.Definitions _≲_
open import Algebra.Ordered.Structures _≈_ _≲_
open import Algebra.Ordered.Structures.Residuated _≈_ _≲_
open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (flip; _$_)
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
import Relation.Binary.Reasoning.PartialOrder as PosetReasoning

record IsStarAuto (_⊗_ : Op₂ A) (ε : A) (¬ : A → A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isCommutativePomonoid : IsCommutativePomonoid _⊗_ ε
    ¬-mono                : Antitonic₁ _≲_ _≲_ ¬
    ¬-involutive          : Involutive ¬
    *-aut                 : ∀ {x y z} → (x ⊗ y) ≲ ¬ z → x ≲ ¬ (y ⊗ z)
    *-aut⁻¹               : ∀ {x y z} → x ≲ ¬ (y ⊗ z) → (x ⊗ y) ≲ ¬ z

  open IsCommutativePomonoid isCommutativePomonoid public
    using
      ( refl
      ; trans
      ; reflexive
      ; antisym
      ; module Eq
      ; setoid
      ; isEquivalence
      ; isPreorder
      ; isPartialOrder
      )
    renaming
      ( mono      to ⊗-mono
      ; monoˡ     to ⊗-monoˡ
      ; monoʳ     to ⊗-monoʳ
      ; ∙-cong    to ⊗-cong
      ; ∙-congˡ   to ⊗-congˡ
      ; ∙-congʳ   to ⊗-congʳ
      ; assoc     to ⊗-assoc
      ; comm      to ⊗-comm
      ; identity  to ⊗-identity
      ; identityˡ to ⊗-identityˡ
      ; identityʳ to ⊗-identityʳ
      )

  poset : Poset _ _ _
  poset = record { isPartialOrder = isPartialOrder }

  ¬-cong : ∀ {x y} → x ≈ y → ¬ x ≈ ¬ y
  ¬-cong x≈y = antisym (¬-mono (reflexive (Eq.sym x≈y))) (¬-mono (reflexive x≈y))

  ⊥ : A
  ⊥ = ¬ ε

  _⅋_ : A → A → A
  x ⅋ y = ¬ (¬ x ⊗ ¬ y)

  ⅋-comm : ∀ x y → (x ⅋ y) ≈ (y ⅋ x)
  ⅋-comm x y = ¬-cong (⊗-comm _ _)

  ⅋-mono : Monotonic₂ _≲_ _≲_ _≲_ _⅋_
  ⅋-mono x≲y u≲v = ¬-mono (⊗-mono (¬-mono x≲y) (¬-mono u≲v))

  ⅋-assoc : Associative _⅋_
  ⅋-assoc x y z =
    begin
      (x ⅋ y) ⅋ z
    ≡⟨⟩
      ¬ (¬ (x ⅋ y) ⊗ ¬ z)
    ≈⟨ ¬-cong (⊗-cong (¬-involutive _) Eq.refl) ⟩
      ¬ ((¬ x ⊗ ¬ y) ⊗ ¬ z)
    ≈⟨ ¬-cong (⊗-assoc _ _ _) ⟩
      ¬ (¬ x ⊗ (¬ y ⊗ ¬ z))
    ≈⟨ ¬-cong (⊗-cong Eq.refl (¬-involutive _)) ⟨
      ¬ (¬ x ⊗ ¬ (y ⅋ z))
    ≡⟨⟩
      x ⅋ (y ⅋ z)
    ∎
    where open SetoidReasoning setoid

  ⅋-identityˡ : LeftIdentity ⊥ _⅋_
  ⅋-identityˡ x =
      begin
        ⊥ ⅋ x
      ≡⟨⟩
        ¬ (¬ (¬ ε) ⊗ ¬ x)
      ≈⟨ ¬-cong (⊗-cong (¬-involutive _) Eq.refl) ⟩
        ¬ (ε ⊗ ¬ x)
      ≈⟨ ¬-cong (⊗-identityˡ _) ⟩
        ¬ (¬ x)
      ≈⟨ ¬-involutive _ ⟩
        x
      ∎
      where open SetoidReasoning setoid

  ⅋-identityʳ : RightIdentity ⊥ _⅋_
  ⅋-identityʳ x =
      begin
        x ⅋ ⊥
      ≡⟨⟩
        ¬ (¬ x ⊗ ¬ (¬ ε))
      ≈⟨ ¬-cong (⊗-cong Eq.refl (¬-involutive _)) ⟩
        ¬ (¬ x ⊗ ε)
      ≈⟨ ¬-cong (⊗-identityʳ _) ⟩
        ¬ (¬ x)
      ≈⟨ ¬-involutive _ ⟩
        x
      ∎
      where open SetoidReasoning setoid

  ⅋-isCommutativePomonoid : IsCommutativePomonoid _⅋_ ⊥
  ⅋-isCommutativePomonoid = record
    { isPomonoid = record
      { isPosemigroup = record
        { isPomagma = record
          { isPartialOrder = isPartialOrder
          ; mono = ⅋-mono
          }
        ; assoc = ⅋-assoc
        }
      ; identity = ⅋-identityˡ , ⅋-identityʳ
      }
    ; comm = ⅋-comm
    }

  open IsCommutativePomonoid ⅋-isCommutativePomonoid public
    using
      (
      )
    renaming
      ( monoˡ     to ⅋-monoˡ
      ; monoʳ     to ⅋-monoʳ
      ; ∙-cong    to ⅋-cong
      ; ∙-congˡ   to ⅋-congˡ
      ; ∙-congʳ   to ⅋-congʳ
      ; identity  to ⅋-identity
      )

  _⊸_ : A → A → A
  x ⊸ y = ¬ x ⅋ y

  residualʳ-to : ∀ {x y z} → (x ⊗ y) ≲ z → y ≲ (x ⊸ z)
  residualʳ-to {x} {y} {z} xy≲z = *-aut $
    begin
      y ⊗ ¬ (¬ x)
    ≈⟨ ⊗-cong Eq.refl (¬-involutive _) ⟩
      y ⊗ x
    ≈⟨ ⊗-comm _ _ ⟩
      x ⊗ y
    ≤⟨ xy≲z ⟩
      z
    ≈⟨ ¬-involutive _ ⟨
      ¬ (¬ z)
    ∎
    where open PosetReasoning poset

  residualʳ-from : ∀ {x y z} → y ≲ (x ⊸ z) → (x ⊗ y) ≲ z
  residualʳ-from {x} {y} {z} y≲x⊸z =
    begin
      x ⊗ y
    ≈⟨ ⊗-comm _ _ ⟩ 
      y ⊗ x
    ≤⟨ *-aut⁻¹ (trans y≲x⊸z (¬-mono ((⊗-mono (reflexive (Eq.sym (¬-involutive _))) refl)))) ⟩
      ¬ (¬ z)
    ≈⟨ ¬-involutive _ ⟩ 
      z
    ∎
    where open PosetReasoning poset

  residualʳ : RightResidual _⊗_ _⊸_
  residualʳ .Function.Equivalence.to = residualʳ-to
  residualʳ .Function.Equivalence.from = residualʳ-from
  residualʳ .Function.Equivalence.to-cong PropEq.refl = PropEq.refl
  residualʳ .Function.Equivalence.from-cong PropEq.refl = PropEq.refl

  ⊗-⊸-isResiduatedCommutativePomonoid : IsResiduatedCommutativePomonoid _⊗_ _⊸_ ε
  ⊗-⊸-isResiduatedCommutativePomonoid = record
    { isCommutativePomonoid = isCommutativePomonoid
    ; residuated            = comm∧residual⇒residuated isPreorder ⊗-comm residualʳ
    }

  open IsResiduatedCommutativePomonoid ⊗-⊸-isResiduatedCommutativePomonoid public
    using
      ( residualˡ
      ; evalˡ
      ; evalʳ
      ; mono-antiˡ
      ; anti-monoʳ
      )
    renaming
      ( residuated to ⊗-⊸-residuated
      )

  -- FIXME: This is contraction.
  ev : ∀ {x} → (x ⊗ ¬ x) ≲ ⊥
  ev {x} = *-aut⁻¹ $
    begin
      x
    ≈⟨ ¬-involutive x ⟨
      ¬ (¬ x)
    ≈⟨ ¬-cong (⊗-identityʳ (¬ x)) ⟨
      ¬ (¬ x ⊗ ε)
    ∎
    where open PosetReasoning poset

  -- FIXME: This is expansion.
  coev : ∀ {x} → ε ≲ (x ⅋ ¬ x)
  coev {x} = 
    begin
      ε
    ≤⟨ residualʳ-to (reflexive (⊗-identityʳ x)) ⟩
      ¬ (¬ (¬ x) ⊗ ¬ x)
    ≈⟨ ⅋-comm _ _ ⟩
      ¬ (¬ x ⊗ ¬ (¬ x))
    ≡⟨⟩
      x ⅋ ¬ x
    ∎
    where open PosetReasoning poset

  linear-distrib : ∀ {x y z} → (x ⊗ (y ⅋ z)) ≲ ((x ⊗ y) ⅋ z)
  linear-distrib {x} {y} {z} =
    let lem₁ =
          begin
            (y ⅋ z) ⊗ ¬ z
          ≡⟨⟩
            ¬ (¬ y ⊗ ¬ z) ⊗ ¬ z
          ≈⟨ ⊗-congʳ (¬-cong (⊗-comm _ _)) ⟩
            ¬ (¬ z ⊗ ¬ y) ⊗ ¬ z
          ≈⟨ ⊗-congʳ (¬-cong (⊗-congʳ (¬-cong (¬-involutive z)))) ⟨
            ¬ (¬ (¬ (¬ z)) ⊗ ¬ y) ⊗ ¬ z
          ≤⟨ evalˡ ⟩
            y
          ∎
        lem₂ =
          begin
            (x ⊗ ¬ (¬ y ⊗ ¬ z)) ⊗ ¬ z
          ≈⟨ ⊗-assoc _ _ _ ⟩ 
            (x ⊗ (¬ (¬ y ⊗ ¬ z) ⊗ ¬ z))
          ≤⟨ ⊗-monoʳ lem₁ ⟩
            (x ⊗ y)
          ≈⟨ ¬-involutive _ ⟨
            ¬ (¬ (x ⊗ y))
          ∎
    in    begin
            x ⊗ (y ⅋ z)
          ≤⟨ *-aut lem₂ ⟩
            z ⅋ (x ⊗ y)
          ≈⟨ ⅋-comm _ _ ⟩
            (x ⊗ y) ⅋ z
          ∎
    where open PosetReasoning poset
