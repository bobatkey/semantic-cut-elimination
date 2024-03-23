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

record IsStarAuto {_⊗_ ε} (⊗-isCommutativePomonoid : IsCommutativePomonoid _⊗_ ε) (¬ : A → A)
   : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    ¬-mono     : ∀ {x y} → x ≲ y → ¬ y ≲ ¬ x
    involution : ∀ {x} → x ≈ ¬ (¬ x)

    *-aut   : ∀ {x y z} → (x ⊗ y) ≲ ¬ z → x ≲ ¬ (y ⊗ z)
    *-aut⁻¹ : ∀ {x y z} → x ≲ ¬ (y ⊗ z) → (x ⊗ y) ≲ ¬ z

  open IsCommutativePomonoid ⊗-isCommutativePomonoid public
    using
      ( refl
      ; trans
      ; reflexive
      ; antisym
      ; module Eq
      ; setoid
      ; isPreorder
      ; isPartialOrder
      )
    renaming
      ( mono      to ⊗-mono
      ; assoc     to ⊗-assoc
      ; comm      to ⊗-comm
      ; ∙-cong    to ⊗-cong
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
        (x ⅋ y) ⅋ z            ≡⟨⟩
        ¬ (¬ (x ⅋ y) ⊗ ¬ z)     ≈˘⟨ ¬-cong (⊗-cong involution Eq.refl) ⟩
        ¬ ((¬ x ⊗ ¬ y) ⊗ ¬ z)   ≈⟨ ¬-cong (⊗-assoc _ _ _) ⟩
        ¬ (¬ x ⊗ (¬ y ⊗ ¬ z))   ≈⟨ ¬-cong (⊗-cong Eq.refl involution) ⟩
        ¬ (¬ x ⊗ ¬ (y ⅋ z))     ≡⟨⟩
        x ⅋ (y ⅋ z)            ∎
     where open SetoidReasoning setoid

  ⅋-identityˡ : LeftIdentity ⊥ _⅋_
  ⅋-identityˡ x =
      begin
        ⊥ ⅋ x             ≡⟨⟩
        ¬ (¬ (¬ ε) ⊗ ¬ x)  ≈˘⟨ ¬-cong (⊗-cong involution Eq.refl) ⟩
        ¬ (ε ⊗ ¬ x)        ≈⟨ ¬-cong (⊗-identityˡ _) ⟩
        ¬ (¬ x)            ≈˘⟨ involution ⟩
        x                  ∎
      where open SetoidReasoning setoid

  ⅋-identityʳ : RightIdentity ⊥ _⅋_
  ⅋-identityʳ x =
      begin
        x ⅋ ⊥             ≡⟨⟩
        ¬ (¬ x ⊗ ¬ (¬ ε))  ≈˘⟨ ¬-cong (⊗-cong Eq.refl involution) ⟩
        ¬ (¬ x ⊗ ε)        ≈⟨ ¬-cong (⊗-identityʳ _) ⟩
        ¬ (¬ x)            ≈˘⟨ involution ⟩
        x                  ∎
      where open SetoidReasoning setoid

  ⅋-isCommutativePomonoid : IsCommutativePomonoid _⅋_ ⊥
  ⅋-isCommutativePomonoid = record {
    isPomonoid = record {
      isPosemigroup = record {
        isPomagma = record {
            isPartialOrder = isPartialOrder ;
            mono = ⅋-mono } ;
          assoc = ⅋-assoc } ;
        identity = ⅋-identityˡ , ⅋-identityʳ } ;
      comm = ⅋-comm }

  open IsCommutativePomonoid ⅋-isCommutativePomonoid public
    using
      (
      )
    renaming
      ( ∙-cong to ⅋-cong
      )

  ev : ∀ {x} → (x ⊗ ¬ x) ≲ ⊥
  ev = *-aut⁻¹ (trans (reflexive involution) (¬-mono (reflexive (⊗-identityʳ _))))

  _⊸_ : A → A → A
  x ⊸ y = ¬ x ⅋ y

  residualʳ-to : ∀ {x y z} → (x ⊗ y) ≲ z → y ≲ (x ⊸ z)
  residualʳ-to xy≲z =
    *-aut (trans (reflexive (⊗-comm _ _)) (trans (⊗-mono (reflexive (Eq.sym involution)) refl) (trans xy≲z (reflexive involution))))

  residualʳ-from : ∀ {x y z} → y ≲ (x ⊸ z) → (x ⊗ y) ≲ z
  residualʳ-from y≲x⊸z =
    trans (reflexive (⊗-comm _ _))
          (trans (*-aut⁻¹ (trans y≲x⊸z (¬-mono (⊗-mono (reflexive involution) refl)))) (reflexive (Eq.sym involution)))

  residualʳ : RightResidual _⊗_ _⊸_
  residualʳ .Function.Equivalence.to = residualʳ-to
  residualʳ .Function.Equivalence.from = residualʳ-from
  residualʳ .Function.Equivalence.to-cong PropEq.refl = PropEq.refl
  residualʳ .Function.Equivalence.from-cong PropEq.refl = PropEq.refl

  ⊗-⊸-isResiduatedCommutativePomonoid : IsResiduatedCommutativePomonoid _⊗_ _⊸_ ε
  ⊗-⊸-isResiduatedCommutativePomonoid = record
    { isCommutativePomonoid = ⊗-isCommutativePomonoid
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

  -- FIXME: This is related to evalˡ and evalʳ, but contains an additional involution.
  eval : ∀ {x y} → ((x ⅋ y) ⊗ ¬ y) ≲ x
  eval = trans (reflexive (⊗-comm _ _))
               (residualʳ-from (trans (reflexive (⅋-comm _ _))
                                         (⅋-mono (reflexive involution) refl)))

  -- FIXME: This is expansion.
  coev : ∀ {x} → ε ≲ (x ⅋ ¬ x)
  coev {x} = trans (residualʳ-to (reflexive (⊗-identityʳ x))) (reflexive (⅋-comm _ _))

  -- FIXME: There must be a shorter proof of this?
  linear-distrib : ∀ {x y z} → (x ⊗ (y ⅋ z)) ≲ ((x ⊗ y) ⅋ z)
  linear-distrib =
    trans (*-aut (trans (reflexive (⊗-assoc _ _ _))
                  (trans (⊗-mono refl eval)
                          (reflexive involution))))
          (reflexive (⅋-comm _ _))
