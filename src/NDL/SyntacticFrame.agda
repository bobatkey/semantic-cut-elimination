{-# OPTIONS --postfix-projections --safe #-}

module NDL.SyntacticFrame {a} (Atom : Set a) where

open import Algebra.Ordered using (IsPomagma)
open import Data.Product using (_,_; swap; proj₁; proj₂)
open import NDL.Formula Atom
open import NDL.NaturalDeduction Atom
open import NDL.Frame Atom using (Frame)
open import Relation.Binary.Construct.Core.Symmetric using (SymCore)
open import Relation.Binary using (IsEquivalence; IsPartialOrder; IsPreorder)

_≤_ : formula → formula → Set a
ϕ ≤ ψ = ε -, ϕ ⊢ ψ

≤-refl : ∀ {ϕ} → ϕ ≤ ϕ
≤-refl = assump here

≤-trans : ∀ {ϕ ψ χ} → ϕ ≤ ψ → ψ ≤ χ → ϕ ≤ χ
≤-trans {ϕ}{ψ}{χ} π₁ π₂ = subst σ π₂
  where σ : Sub (ε -, ϕ) (ε -, ψ)
        σ here = π₁

_≈_ : formula → formula → Set a
_≈_ = SymCore _≤_

≈-isEquivalence : IsEquivalence _≈_
≈-isEquivalence .IsEquivalence.refl = ≤-refl , ≤-refl
≈-isEquivalence .IsEquivalence.sym = swap
≈-isEquivalence .IsEquivalence.trans (ϕ≤ψ , ψ≤ϕ) (ψ≤χ , χ≤ψ) =
  ≤-trans ϕ≤ψ ψ≤χ , ≤-trans χ≤ψ ψ≤ϕ

≤-isPartialOrder : IsPartialOrder _≈_ _≤_
≤-isPartialOrder .IsPartialOrder.isPreorder .IsPreorder.isEquivalence = ≈-isEquivalence
≤-isPartialOrder .IsPartialOrder.isPreorder .IsPreorder.reflexive = proj₁
≤-isPartialOrder .IsPartialOrder.isPreorder .IsPreorder.trans = ≤-trans
≤-isPartialOrder .IsPartialOrder.antisym ϕ≤ψ ψ≤ϕ = ϕ≤ψ , ψ≤ϕ

∨-isPomagma : IsPomagma _≈_ _≤_ _∨_
∨-isPomagma .IsPomagma.isPartialOrder = ≤-isPartialOrder
∨-isPomagma .IsPomagma.mono π₁ π₂ = orE (assump here) (orI1 π₁) (orI2 π₂)

syntacticFrame : Frame a a a
syntacticFrame = record { ⊥ = ⊥; isPomagma = ∨-isPomagma; atom = atom }
