{-# OPTIONS --postfix-projections --safe #-}

module CK.Frame2 {a} (Atom : Set a) where

open import Level using (suc; _⊔_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; _×_)
open import Relation.Binary using (Rel; IsPartialOrder; Poset)
open import CK.Model Atom using (ModalHeytingAlgebra)
import Relation.Binary.Reasoning.PartialOrder as PosetReasoning

-- A frame is a poset with a coverage and a relational operator for
-- the modality
record Frame c ℓ₁ ℓ₂ : Set (a ⊔ suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁
    _≤_     : Rel Carrier ℓ₂

    isPartialOrder : IsPartialOrder _≈_ _≤_

    atom : Atom → Carrier → Set (c ⊔ ℓ₂)
    atom-≤ : ∀ {at x y} → x ≤ y → atom at y → atom at x

    -- the “coverage”
    Cover   : Carrier → Set (c ⊔ ℓ₂)
    Cover-≤ : ∀ {x y} → x ≤ y → Cover y → Cover x        -- 'Cover' is a lower set
    Elem    : ∀ x → Cover x → Carrier → Set (c ⊔ ℓ₂)
    Elem-≤  : ∀ {x y z} c (x≤y : x ≤ y) → Elem x (Cover-≤ x≤y c) z → Elem y c z

    -- Covers actually cover, which yields distributivity and a
    -- HeytingAlgebra
    isCover : ∀ {x y} c → Elem x c y → y ≤ x

    -- The relation for the □ modality
    R : Carrier → Carrier → Set (c ⊔ ℓ₂)
    R-≤ : ∀ {x y z} → x ≤ y → R y z → R x z
    R-⊤ : ∀ x → Σ[ y ∈ Carrier ] R x y
    R-∧ : ∀ {x y z} → R x y → R x z → Σ[ w ∈ Carrier ] (R x w × w ≤ y × w ≤ z)

    -- The relation for the ◇ modality
    S : Carrier → Carrier → Set (c ⊔ ℓ₂)
    S-≤ : ∀ {x y z} → x ≤ y → S y z → S x z
    RS  : ∀ {x y z} → R x y → S x z → Σ[ w ∈ Carrier ] (S x w × w ≤ y × w ≤ z)

  open IsPartialOrder isPartialOrder

  poset : Poset c ℓ₁ ℓ₂
  poset = record { isPartialOrder = isPartialOrder }

module _ {c} {ℓ₁} {ℓ₂} (F : Frame c ℓ₁ ℓ₂) where

  module F = Frame F

  import Algebra.Ordered.Construction.LowerSet F.poset as L
  module LR = L.RelationalModality F.R F.R-≤
  module LRN = LR.Necessity F.R-⊤ F.R-∧
  module LS = L.RelationalModality F.S F.S-≤

  import Algebra.Ordered.Construction.Covered F.poset F.Cover F.Cover-≤ F.Elem F.Elem-≤ as Cl
  open Cl.StrongProduct F.isCover using (𝐂-isStrongClosureOp)
  import Algebra.Ordered.Construction.Closed.HeytingAlgebra L.heytingAlgebra 𝐂-isStrongClosureOp as M

  atom₀ : Atom → L.LowerSet
  atom₀ at .L.LowerSet.ICarrier = F.atom at
  atom₀ at .L.LowerSet.≤-closed = F.atom-≤

  atom : Atom → M.Elt
  atom at = M.η (atom₀ at)

  □ : M.Elt → M.Elt
  □ X = M.η (LR.◯ (X .M.Elt.elt))

  □-mono : ∀ {x y} → x M.≤ y → □ x M.≤ □ y
  □-mono x≤y = M.η-mono (LR.◯-mono (x≤y .M._≤_.*≤*))

  ◇ : M.Elt → M.Elt
  ◇ X = M.η (LS.◯ (X .M.Elt.elt))

  ◇-mono : ∀ {x y} → x M.≤ y → ◇ x M.≤ ◇ y
  ◇-mono x≤y = M.η-mono (LS.◯-mono (x≤y .M._≤_.*≤*))

  L□-◇ : ∀ {x y} → LR.◯ x L.∧ LS.◯ y L.≤ LS.◯ (x L.∧ y)
  L□-◇ {F} {G} .L.*≤* {x} ((y , Rxy , Fy) , (z , Sxz , Gz)) =
    let w , Sxw , w≤y , w≤z = F.RS Rxy Sxz in
    w , Sxw , F .L.≤-closed w≤y Fy , G .L.≤-closed w≤z Gz

  □-⊤ : M.⊤ M.≤ □ M.⊤
  □-⊤ = begin
      M.⊤                            ≤⟨ M.η-⊤ ⟩
      M.η L.⊤                        ≤⟨ M.η-mono LRN.◯-Nec ⟩
      M.η (LR.◯ L.⊤)                 ≡⟨⟩
      M.η (LR.◯ (M.⊤ .M.Elt.elt))    ≡⟨⟩
      □ M.⊤                          ∎
    where open PosetReasoning M.poset

  □-∧ : ∀ x y → □ x M.∧ □ y M.≤ □ (x M.∧ y)
  □-∧ x y = begin
      □ x M.∧ □ y                                              ≡⟨⟩
      M.η (LR.◯ (x .M.Elt.elt)) M.∧ M.η (LR.◯ (y .M.Elt.elt))  ≤⟨ M.η-∧ ⟩
      M.η (LR.◯ (x .M.Elt.elt) L.∧ LR.◯ (y .M.Elt.elt))        ≤⟨ M.η-mono LRN.◯-K ⟩
      M.η (LR.◯ (x .M.Elt.elt L.∧ y .M.Elt.elt))               ≡⟨⟩
      □ (x M.∧ y)                                              ∎
    where open PosetReasoning M.poset

  K-◇ : ∀ x y → □ x M.∧ ◇ y M.≤ ◇ (x M.∧ y)
  K-◇ x y = begin
      □ x M.∧ ◇ y                                              ≡⟨⟩
      M.η (LR.◯ (x .M.Elt.elt)) M.∧ M.η (LS.◯ (y .M.Elt.elt))  ≤⟨ M.η-∧ ⟩
      M.η (LR.◯ (x .M.Elt.elt) L.∧ LS.◯ (y .M.Elt.elt))        ≤⟨ M.η-mono L□-◇ ⟩
      M.η (LS.◯ (x .M.Elt.elt L.∧ y .M.Elt.elt))               ≡⟨⟩
      ◇ (x M.∧ y)                                              ∎
    where open PosetReasoning M.poset

  model : ModalHeytingAlgebra (suc (c ⊔ ℓ₂)) (c ⊔ ℓ₂) (c ⊔ ℓ₂)
  model = record
           { isHeytingAlgebra = M.isHeytingAlgebra
           ; □ = □
           ; □-mono = □-mono
           ; □-⊤ = □-⊤
           ; □-∧ = □-∧
           ; ◇ = ◇
           ; ◇-mono = ◇-mono
           ; K-◇ = K-◇
           ; atom = atom
           }
