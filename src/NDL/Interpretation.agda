{-# OPTIONS --postfix-projections --safe #-}

open import Data.Product using (proj₁; proj₂)
open import NDL.Model

module NDL.Interpretation {a} (Atom : Set a)
  {c} {ℓ₁} {ℓ₂} (ℳ : NDLModel Atom c ℓ₁ ℓ₂)
  where

open import NDL.Formula Atom
open import NDL.NaturalDeduction Atom

module ℳ = NDLModel ℳ

Fm⟦_⟧ : formula → ℳ.Carrier
Fm⟦ atom a ⟧ = ℳ.atom a
Fm⟦ ϕ ∧ ψ ⟧ = Fm⟦ ϕ ⟧ ℳ.∧ Fm⟦ ψ ⟧
Fm⟦ ϕ ∨ ψ ⟧ = Fm⟦ ϕ ⟧ ℳ.∨ Fm⟦ ψ ⟧
Fm⟦ ⊤ ⟧ = ℳ.⊤
Fm⟦ ⊥ ⟧ = ℳ.⊥

Ctxt⟦_⟧ : context → ℳ.Carrier
Ctxt⟦ ε ⟧ = ℳ.⊤
Ctxt⟦ Γ -, ϕ ⟧ = Ctxt⟦ Γ ⟧ ℳ.∧ Fm⟦ ϕ ⟧

Assump⟦_⟧ : ∀ {Γ ϕ} → ϕ ∈ Γ → Ctxt⟦ Γ ⟧ ℳ.≤ Fm⟦ ϕ ⟧
Assump⟦ here ⟧   = ℳ.x∧y≤y _ _
Assump⟦ next x ⟧ = ℳ.trans (ℳ.x∧y≤x _ _) Assump⟦ x ⟧

Proof⟦_⟧ : ∀ {Γ ϕ} → Γ ⊢ ϕ → Ctxt⟦ Γ ⟧ ℳ.≤ Fm⟦ ϕ ⟧
Proof⟦ assump x ⟧ = Assump⟦ x ⟧
Proof⟦ top ⟧ = ℳ.maximum _
Proof⟦ andI π₁ π₂ ⟧ = ℳ.∧-greatest Proof⟦ π₁ ⟧ Proof⟦ π₂ ⟧
Proof⟦ andE1 π ⟧ = ℳ.trans Proof⟦ π ⟧ (ℳ.x∧y≤x _ _)
Proof⟦ andE2 π ⟧ = ℳ.trans Proof⟦ π ⟧ (ℳ.x∧y≤y _ _)
Proof⟦ bot π ⟧ = ℳ.trans Proof⟦ π ⟧ (ℳ.minimum _)
Proof⟦ orI1 π ⟧ = ℳ.trans Proof⟦ π ⟧ (ℳ.x≤x∨y _ _)
Proof⟦ orI2 π ⟧ = ℳ.trans Proof⟦ π ⟧ (ℳ.y≤x∨y _ _)
Proof⟦ orE π π₁ π₂ ⟧ =
  ℳ.trans Proof⟦ π ⟧
           (ℳ.∨-least (ℳ.trans (ℳ.∧-greatest (ℳ.maximum _) ℳ.refl) Proof⟦ π₁ ⟧)
                       (ℳ.trans (ℳ.∧-greatest (ℳ.maximum _) ℳ.refl) Proof⟦ π₂ ⟧))
