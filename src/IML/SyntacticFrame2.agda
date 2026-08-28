{-# OPTIONS --postfix-projections --safe #-}

module IML.SyntacticFrame2 {a} (Atom : Set a) where

open import Level using (Lift; lift)
open import Data.Product using (Σ-syntax; proj₁; proj₂; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Binary using (IsPartialOrder; IsPreorder; IsEquivalence)
open import IML.Formula Atom
open import IML.NaturalDeduction Atom
open import IML.Frame2 Atom using (Frame)

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
syntacticFrame .Frame.isPartialOrder = ≤-isPartialOrder
syntacticFrame .Frame.atom at Γ = Γ ⊢ `atom at
syntacticFrame .Frame.atom-≤ {at} {Γ} {Δ} Γ≤Δ Δ⊢at = rename Γ≤Δ Δ⊢at
syntacticFrame .Frame.Cover Γ = (Σ[ ϕ ∈ formula ] Σ[ ψ ∈ formula ] (Γ ⊢ (ϕ `∨ ψ))) ⊎ (Γ ⊢ `⊥)
syntacticFrame .Frame.Cover-≤ {Γ} {Δ} Γ≤Δ (inj₁ (ϕ , ψ , Δ⊢ϕ∨ψ)) = inj₁ (ϕ , ψ , rename Γ≤Δ Δ⊢ϕ∨ψ)
syntacticFrame .Frame.Cover-≤ {Γ} {Δ} Γ≤Δ (inj₂ Δ⊢⊥) = inj₂ (rename Γ≤Δ Δ⊢⊥)
syntacticFrame .Frame.Elem Γ (inj₁ (ϕ , ψ , Γ⊢ψ∨ψ)) Δ = (Δ ≤ (Γ -, ϕ)) ⊎ (Δ ≤ (Γ -, ψ))
syntacticFrame .Frame.Elem Γ (inj₂ Γ⊢⊥) Δ = Lift a ⊥
syntacticFrame .Frame.Elem-≤ {Γ} {Δ} {Ξ} (inj₁ (ϕ , ψ , Δ⊢ϕ∨ψ)) Γ≤Δ (inj₁ Ξ≤Γϕ) = inj₁ (≤-trans Ξ≤Γϕ (Ren-wk Γ≤Δ))
syntacticFrame .Frame.Elem-≤ {Γ} {Δ} {Ξ} (inj₁ (ϕ , ψ , Δ⊢ϕ∨ψ)) Γ≤Δ (inj₂ Ξ≤Γψ) = inj₂ (≤-trans Ξ≤Γψ (Ren-wk Γ≤Δ))
syntacticFrame .Frame.Elem-≤ {Γ} {Δ} {Ξ} (inj₂ Δ⊢⊥) _ ()
syntacticFrame .Frame.isCover {Γ} {Δ} (inj₁ (ϕ , ψ , Γ⊢ϕ∨ψ)) (inj₁ Δ≤Γϕ) = ≤-trans Δ≤Γϕ next
syntacticFrame .Frame.isCover {Γ} {Δ} (inj₁ (ϕ , ψ , Γ⊢ϕ∨ψ)) (inj₂ Δ≤Γψ) = ≤-trans Δ≤Γψ next
syntacticFrame .Frame.isCover {Γ} {Δ} (inj₂ Γ⊢⊥) ()
syntacticFrame .Frame.R Γ Δ = Σ[ ϕ ∈ formula ] (Γ ⊢ `◯ ϕ × ε -, ϕ ≤ Δ)
syntacticFrame .Frame.R-≤ {Γ} {Δ} {Ξ} Γ≤Δ (ϕ , Δ⊢◯ϕ , ϕ≤Ξ) = ϕ , rename Γ≤Δ Δ⊢◯ϕ , ϕ≤Ξ
