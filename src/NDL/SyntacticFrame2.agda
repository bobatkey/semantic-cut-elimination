{-# OPTIONS --postfix-projections --safe #-}

module NDL.SyntacticFrame2 {a} (Atom : Set a) where

open import Level using (Lift; lift)
open import Data.Product using (Σ-syntax; proj₁; proj₂; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Binary using (IsPartialOrder; IsPreorder; IsEquivalence)
open import NDL.Formula Atom
open import NDL.NaturalDeduction Atom
open import NDL.Frame2 Atom using (Frame)

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
syntacticFrame .Frame.Elem Γ (inj₁ (ϕ , ψ , Γ⊢ψ∨ψ)) Δ = (Δ ≤ (ε -, ϕ)) ⊎ (Δ ≤ (ε -, ψ))
syntacticFrame .Frame.Elem Γ (inj₂ Γ⊢⊥) Δ = Lift a ⊥
syntacticFrame .Frame.Elem-≤ {Γ} {Δ} {Ξ} (inj₁ (ϕ , ψ , Δ⊢ϕ∨ψ)) Γ≤Δ (inj₁ Ξ≤ϕ) = inj₁ Ξ≤ϕ
syntacticFrame .Frame.Elem-≤ {Γ} {Δ} {Ξ} (inj₁ (ϕ , ψ , Δ⊢ϕ∨ψ)) Γ≤Δ (inj₂ Ξ≤ψ) = inj₂ Ξ≤ψ
syntacticFrame .Frame.Elem-≤ {Γ} {Δ} {Ξ} (inj₂ Δ⊢⊥) _ ()
