{-# OPTIONS --postfix-projections --safe #-}

module MIPL.SyntacticFrame2 {a} (Atom : Set a) where

open import Data.Product using (_×_; proj₁; proj₂; _,_; swap)
open import MIPL.Formula Atom
open import MIPL.NaturalDeduction Atom
open import MIPL.Frame2 Atom using (Frame)
open import Relation.Binary.Construct.Core.Symmetric using (SymCore)
open import Relation.Binary using (IsEquivalence; IsPartialOrder; IsPreorder)

_≤_ : context → context → Set a
Γ ≤ Δ = Ren Γ Δ

≤-refl : ∀ {Γ} → Γ ≤ Γ
≤-refl x∈Γ = x∈Γ

≤-trans : ∀ {Γ Δ Ξ} → Γ ≤ Δ → Δ ≤ Ξ → Γ ≤ Ξ
≤-trans ρ₁ ρ₂ x = ρ₁ (ρ₂ x)

_≈_ : context → context → Set a
Γ ≈ Δ = (Γ ≤ Δ) × (Δ ≤ Γ)

≈-isEquivalence : IsEquivalence _≈_
≈-isEquivalence .IsEquivalence.refl = ≤-refl , ≤-refl
≈-isEquivalence .IsEquivalence.sym (x≤y , y≤x) = y≤x , x≤y
≈-isEquivalence .IsEquivalence.trans (x≤y , y≤x) (y≤z , z≤y) = ≤-trans x≤y y≤z , ≤-trans z≤y y≤x

≤-isPreorder : IsPreorder _≈_ _≤_
≤-isPreorder .IsPreorder.isEquivalence = ≈-isEquivalence
≤-isPreorder .IsPreorder.reflexive = proj₁
≤-isPreorder .IsPreorder.trans = ≤-trans

≤-isPartialOrder : IsPartialOrder _≈_ _≤_
≤-isPartialOrder .IsPartialOrder.isPreorder = ≤-isPreorder
≤-isPartialOrder .IsPartialOrder.antisym x≤y y≤x = x≤y , y≤x

syntacticFrame : Frame a a a
syntacticFrame .Frame.Carrier = context
syntacticFrame .Frame._≈_ = _≈_
syntacticFrame .Frame._≤_ = _≤_
syntacticFrame .Frame.atom at Γ = Γ ⊢ `atom at
syntacticFrame .Frame.atom-≤ {at} {Γ} {Δ} = rename
syntacticFrame .Frame.isPartialOrder = ≤-isPartialOrder
