{-# OPTIONS --postfix-projections --safe #-}

open import Level using (_⊔_; suc)
open import Data.Product using (_,_; Σ-syntax; _×_; proj₁; proj₂)
open import Algebra.Ordered using (IsPomonoid; IsClosureOp; IsStrongClosureOp)
open import Relation.Binary using (Poset)

module Algebra.Ordered.Construction.Covered
  {c ℓ₁ ℓ₂} (poset : Poset c ℓ₁ ℓ₂)

  -- Data for a system of "covers", but we needn't necessarily have
  -- that a “cover” covers wrt to the order.
  --
  -- This stops it being a formal topology in the Coquand/Ayberk
  -- sense, unless we add the covering axiom back in. In general
  -- though, we don't need it. We get an interesting non-distributive
  -- logic without it.
  (S : poset .Poset.Carrier → Set (c ⊔ ℓ₂))
  (S-≤ : ∀ {x y} → poset .Poset._≤_ x y → S y → S x)
  (P : ∀ x → S x → poset .Poset.Carrier → Set (c ⊔ ℓ₂))
  (P-≤ : ∀ {x y z} c (x≤y : poset .Poset._≤_ x y) → P x (S-≤ x≤y c) z → P y c z)

  -- S is a presheaf on 'poset'
  -- P is a presheaf on ∫S ? the category of elements of S? no?
  --   P is a functor ∫S → PSh(|C|)
  -- why discrete?
  where

-- Example:
--   S Γ = { A , B | Γ ⊢ne A ∨ B } ⊎ { * | Γ ⊢ne ⊥ }
--   P Γ (A , B) Δ = Δ ⇒ Γ , A or Δ ⇒ Γ , B
--   P Γ *       Δ = Δ ⇒ Γ , ⊥

-- Relational things:
--   □ F x = ∃ y. R x y × F y
--
-- Define R Γ Δ = Γ ⊢ne ! A × ... ?

private
  module C = Poset poset

open C using (Carrier)
       renaming (_≈_ to _≈ᶜ_; _≤_ to _≤ᶜ_)

open import Algebra.Ordered.Construction.LowerSet poset

data Complete (F : LowerSet) : Carrier → Set (c ⊔ ℓ₂) where
  leaf  : ∀ {x} → F .ICarrier x → Complete F x
  split : ∀ {x} (s : S x) → (∀ y → P x s y → Complete F y) → Complete F x

Complete-≤-closed : ∀ {F x y} → x ≤ᶜ y → Complete F y → Complete F x
Complete-≤-closed {F} x≤y (leaf y∈F) = leaf (F .≤-closed x≤y y∈F)
Complete-≤-closed {F} x≤y (split c χ) = split (S-≤ x≤y c) λ z p → χ z (P-≤ c x≤y p)

𝐂 : LowerSet → LowerSet
𝐂 F .ICarrier = Complete F
𝐂 F .≤-closed = Complete-≤-closed

Complete-mono : ∀ {F G} → F ≤ G → ∀ {x} → Complete F x → Complete G x
Complete-mono F≤G (leaf x∈F) = leaf (F≤G .*≤* x∈F)
Complete-mono F≤G (split s χ) = split s λ y p → Complete-mono F≤G (χ y p)

Complete-join : ∀ {F x} → Complete (𝐂 F) x → Complete F x
Complete-join (leaf x∈𝐂F) = x∈𝐂F
Complete-join (split s χ) = split s λ y p → Complete-join (χ y p)

𝐂-mono : ∀ {F G} → F ≤ G → 𝐂 F ≤ 𝐂 G
𝐂-mono F≤G .*≤* = Complete-mono F≤G

𝐂-unit : ∀ {F} → F ≤ 𝐂 F
𝐂-unit .*≤* = leaf

𝐂-join : ∀ {F} → 𝐂 (𝐂 F) ≤ 𝐂 F
𝐂-join .*≤* = Complete-join

𝐂-isClosureOp : IsClosureOp _≈_ _≤_ 𝐂
𝐂-isClosureOp .IsClosureOp.mono = 𝐂-mono
𝐂-isClosureOp .IsClosureOp.inflate _ = 𝐂-unit
𝐂-isClosureOp .IsClosureOp.closed x = 𝐂-join

------------------------------------------------------------------------------

-- If P x s y → y ≤ x, then we have strength wrt to ∧. And the converse?
--
-- This means that the 's : S x' are actually covers.
module StrongProduct (is-cover : ∀ {x y} c → P x c y → y ≤ᶜ x) where

  ∧-strength-lemma : ∀ {F G x} → F .ICarrier x → Complete G x → Complete (F ∧ G) x
  ∧-strength-lemma x∈F (leaf x∈G)      = leaf (x∈F , x∈G)
  ∧-strength-lemma {F} x∈F (split c χ) = split c λ y p → ∧-strength-lemma (F .≤-closed (is-cover c p) x∈F) (χ y p)

  ∧-strength : ∀ {F G} → F ∧ 𝐂 G ≤ 𝐂 (F ∧ G)
  ∧-strength .*≤* {x} (x∈F , x∈𝐂G) = ∧-strength-lemma x∈F x∈𝐂G

  𝐂-isStrongClosureOp : IsStrongClosureOp _≈_ _≤_ 𝐂 _∧_
  𝐂-isStrongClosureOp .IsStrongClosureOp.isClosureOp = 𝐂-isClosureOp
  𝐂-isStrongClosureOp .IsStrongClosureOp.strength = ∧-strength

module StrongDay
    {_∙ᶜ_} {εᶜ} (isPomonoid : IsPomonoid _≈ᶜ_ _≤ᶜ_ _∙ᶜ_ εᶜ)
    -- FIXME: rephrase with a ternary relation
    (S-∙ : ∀ {x y z} → x ≤ᶜ (y ∙ᶜ z) → S z → S x)
    (P-∙ : ∀ {w x y z s} (x≤y∙z : x ≤ᶜ (y ∙ᶜ z)) →
              P x (S-∙ x≤y∙z s) w → Σ[ w' ∈ _ ] (w ≤ᶜ (y ∙ᶜ w') × P z s w'))
  where

  -- For sums wrt tensor products:
  --   S Γ = Σ[ Γ₁ , Γ₂ , A , B ] (Γ ⇒ Γ₁ , Γ₂ × Γ₂ ⊢ A ∨ B)
  --   P Γ (Γ₁ , Γ₂ , A , B , ϕ , ψ) Δ = (Γ₁ , A ⇒ Δ) or (Γ₁ , B ⇒ Δ)

  -- And for tensor products by themselves
  --   S Γ = ∃ Δ , A , B. Γ ⇒ Δ₁ , Δ₂ × Δ₂ ⊢ne A ⊗ B

  open Day isPomonoid

  ∙-strength : ∀ {F G x y z} → x ≤ᶜ y ∙ᶜ z → F .ICarrier y → Complete G z → Complete (F ∙ G) x
  ∙-strength x≤y∙z y∈F (leaf z∈G) = leaf (_ , _ , x≤y∙z , y∈F , z∈G)
  ∙-strength {F} {G} {x} {y} {z} x≤y∙z y∈F (split s χ) =
    split (S-∙ x≤y∙z s) λ w p →
      ∙-strength (P-∙ x≤y∙z p .proj₂ .proj₁) y∈F (χ _ (P-∙ x≤y∙z p .proj₂ .proj₂))

  ∙-strong : ∀ {F G} → F ∙ 𝐂 G ≤ 𝐂 (F ∙ G)
  ∙-strong .*≤* {x} (y , z , x≤y∙z , y∈F , z∈𝐂G) = ∙-strength x≤y∙z y∈F z∈𝐂G
