{-# OPTIONS --postfix-projections --safe #-}

open import Data.Product using (proj₁; proj₂)
open import CK.Model

module CK.Interpretation {a} (Atom : Set a)
   {c} {ℓ₁} {ℓ₂}
   (ℳ : ModalHeytingAlgebra Atom c ℓ₁ ℓ₂)
   where

open import CK.Formula Atom
open import CK.NaturalDeduction Atom

module ℳ = ModalHeytingAlgebra ℳ

open import Algebra.Definitions ℳ._≈_ using (_DistributesOverˡ_)

------------------------------------------------------------------------------
-- FIXME: put these in the HeytingAlgebra bits

swap-∧ : ∀ {x y} → (x ℳ.∧ y) ℳ.≤ (y ℳ.∧ x)
swap-∧ = ℳ.∧-greatest (ℳ.x∧y≤y _ _) (ℳ.x∧y≤x _ _)

∧-distrib-∨ : ℳ._∧_ DistributesOverˡ ℳ._∨_
∧-distrib-∨ x y z = ℳ.antisym
  (ℳ.trans
    swap-∧
    (ℳ.transpose-∧
      (ℳ.∨-least
        (ℳ.transpose-⇨ (ℳ.trans swap-∧ (ℳ.x≤x∨y _ _)))
        (ℳ.transpose-⇨ (ℳ.trans swap-∧ (ℳ.y≤x∨y _ _))))))
  (ℳ.∨-least
    (ℳ.∧-greatest (ℳ.x∧y≤x _ _) (ℳ.trans (ℳ.x∧y≤y _ _) (ℳ.x≤x∨y _ _)))
    (ℳ.∧-greatest (ℳ.x∧y≤x _ _) (ℳ.trans (ℳ.x∧y≤y _ _) (ℳ.y≤x∨y _ _))))

------------------------------------------------------------------------------

Fm⟦_⟧ : formula → ℳ.Carrier
Fm⟦ `atom a ⟧ = ℳ.atom a
Fm⟦ ϕ `⇒ ψ ⟧ = Fm⟦ ϕ ⟧ ℳ.⇒ Fm⟦ ψ ⟧
Fm⟦ ϕ `∧ ψ ⟧ = Fm⟦ ϕ ⟧ ℳ.∧ Fm⟦ ψ ⟧
Fm⟦ ϕ `∨ ψ ⟧ = Fm⟦ ϕ ⟧ ℳ.∨ Fm⟦ ψ ⟧
Fm⟦ `⊤ ⟧ = ℳ.⊤
Fm⟦ `⊥ ⟧ = ℳ.⊥
Fm⟦ `□ ϕ ⟧ = ℳ.□ Fm⟦ ϕ ⟧
Fm⟦ `◇ ϕ ⟧ = ℳ.◇ Fm⟦ ϕ ⟧

Ctxt⟦_⟧ : context → ℳ.Carrier
Ctxt⟦ ε ⟧      = ℳ.⊤
Ctxt⟦ Γ -, ϕ ⟧ = Ctxt⟦ Γ ⟧ ℳ.∧ Fm⟦ ϕ ⟧

Assump⟦_⟧ : ∀ {Γ ϕ} → ϕ ∈ Γ → Ctxt⟦ Γ ⟧ ℳ.≤ Fm⟦ ϕ ⟧
Assump⟦ here ⟧   = ℳ.x∧y≤y _ _
Assump⟦ next x ⟧ = ℳ.trans (ℳ.x∧y≤x _ _) Assump⟦ x ⟧

mutual
  Proof⟦_⟧ : ∀ {Γ ϕ} → Γ ⊢ ϕ → Ctxt⟦ Γ ⟧ ℳ.≤ Fm⟦ ϕ ⟧
  Proof⟦ assump x ⟧ = Assump⟦ x ⟧
  Proof⟦ impI π ⟧ = ℳ.transpose-⇨ Proof⟦ π ⟧
  Proof⟦ impE π₁ π₂ ⟧ =
    ℳ.trans (ℳ.∧-greatest ℳ.refl Proof⟦ π₂ ⟧) (ℳ.transpose-∧ Proof⟦ π₁ ⟧)
  Proof⟦ andI π₁ π₂ ⟧ = ℳ.∧-greatest Proof⟦ π₁ ⟧ Proof⟦ π₂ ⟧
  Proof⟦ andE1 π ⟧ = ℳ.trans Proof⟦ π ⟧ (ℳ.x∧y≤x _ _)
  Proof⟦ andE2 π ⟧ = ℳ.trans Proof⟦ π ⟧ (ℳ.x∧y≤y _ _)
  Proof⟦ orI1 π ⟧ = ℳ.trans Proof⟦ π ⟧ (ℳ.x≤x∨y _ _)
  Proof⟦ orI2 π ⟧ = ℳ.trans Proof⟦ π ⟧ (ℳ.y≤x∨y _ _)
  Proof⟦ orE π π₁ π₂ ⟧ =
    ℳ.trans
      (ℳ.∧-greatest ℳ.refl Proof⟦ π ⟧)
      (ℳ.trans
        (ℳ.reflexive (∧-distrib-∨ _ _ _))
        (ℳ.∨-least Proof⟦ π₁ ⟧ Proof⟦ π₂ ⟧))
  Proof⟦ trueI ⟧ = ℳ.maximum _
  Proof⟦ falseE π ⟧ = ℳ.trans Proof⟦ π ⟧ (ℳ.minimum _)
  Proof⟦ mono π₁ π₂ ⟧ = ℳ.trans Proof□⟦ π₁ ⟧ (ℳ.□-mono Proof⟦ π₂ ⟧)
  Proof⟦ mono-◇ π₁ π₂ π₃ ⟧ =
    ℳ.trans (ℳ.∧-greatest Proof□⟦ π₁ ⟧ Proof⟦ π₂ ⟧)
    (ℳ.trans (ℳ.K-◇ _ _) (ℳ.◇-mono Proof⟦ π₃ ⟧))

  Proof□⟦_⟧ : ∀ {Γ Δ} → Γ ⊢□* Δ → Ctxt⟦ Γ ⟧ ℳ.≤ ℳ.□ Ctxt⟦ Δ ⟧
  Proof□⟦ nil ⟧ = ℳ.trans (ℳ.maximum _) ℳ.□-⊤
  Proof□⟦ δ -, π ⟧ = ℳ.trans (ℳ.∧-greatest Proof□⟦ δ ⟧ Proof⟦ π ⟧) (ℳ.□-∧ _ _)
