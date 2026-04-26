{-# OPTIONS --postfix-projections --safe #-}

module IPL.SyntacticFrame {a} (Atom : Set a) where

open import Data.Product using (_×_; proj₁; proj₂; _,_; swap)
open import IPL.Formula Atom
open import IPL.NaturalDeduction Atom
open import IPL.Frame Atom using (Frame)
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

isLattice : IsLattice _≈_ _≤_ _`∨_ _`∧_
isLattice .IsLattice.isPartialOrder = ≤-isPartialOrder
isLattice .IsLattice.supremum ϕ ψ .proj₁ = orI1 (assump here)
isLattice .IsLattice.supremum ϕ ψ .proj₂ .proj₁ = orI2 (assump here)
isLattice .IsLattice.supremum ϕ ψ .proj₂ .proj₂ χ π₁ π₂ =
  orE (assump here)
      (rename (Ren-wk next) π₁)
      (rename (Ren-wk next) π₂)
isLattice .IsLattice.infimum ϕ ψ .proj₁ = andE1 (assump here)
isLattice .IsLattice.infimum ϕ ψ .proj₂ .proj₁ = andE2 (assump here)
isLattice .IsLattice.infimum ϕ ψ .proj₂ .proj₂ χ π₁ π₂ = andI π₁ π₂

isDistributiveLattice : IsDistributiveLattice _≈_ _≤_ _`∨_ _`∧_
isDistributiveLattice .IsDistributiveLattice.isLattice = isLattice
isDistributiveLattice .IsDistributiveLattice.∧-distribˡ-∨ ϕ ψ χ =
  orE (andE2 (assump here))
      (orI1 (andI (andE1 (assump (next here))) (assump here)))
      (orI2 (andI (andE1 (assump (next here))) (assump here))) ,
  orE (assump here)
      (andI (andE1 (assump here)) (orI1 (andE2 (assump here))))
      (andI (andE1 (assump here)) (orI2 (andE2 (assump here))))

syntacticFrame : Frame a a a
syntacticFrame .Frame.Carrier = formula
syntacticFrame .Frame._≈_ = _≈_
syntacticFrame .Frame._≤_ = _≤_
syntacticFrame .Frame._∧_ = _`∧_
syntacticFrame .Frame._∨_ = _`∨_
syntacticFrame .Frame.⊥ = `⊥
syntacticFrame .Frame.isDistributiveLattice = isDistributiveLattice
syntacticFrame .Frame.isMinimum χ = falseE (assump here)
syntacticFrame .Frame.atom = `atom
