{-# OPTIONS --postfix-projections --safe #-}

module MIPL.SyntacticFrame {a} (Atom : Set a) where

open import Data.Product using (_×_; proj₁; proj₂; _,_; swap)
open import MIPL.Formula Atom
open import MIPL.NaturalDeduction Atom
open import MIPL.Frame Atom using (Frame)
open import Relation.Binary.Construct.Core.Symmetric
open import Relation.Binary.Lattice
open import Relation.Binary.Structures

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

syntacticFrame : Frame a a a
syntacticFrame .Frame.Carrier = formula
syntacticFrame .Frame._≈_ = _≈_
syntacticFrame .Frame._≤_ = _≤_
syntacticFrame .Frame.isPartialOrder = ≤-isPartialOrder
syntacticFrame .Frame.atom = `atom
