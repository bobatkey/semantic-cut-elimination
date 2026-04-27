{-# OPTIONS --postfix-projections --safe #-}

open import Data.Product using (proj₁; proj₂)
open import MIPL.Model

module MIPL.Interpretation {a} (Atom : Set a)
   {c} {ℓ₁} {ℓ₂}
   (ℳ : CCPoset Atom c ℓ₁ ℓ₂)
   where

open import MIPL.Formula Atom
open import MIPL.NaturalDeduction Atom

module ℳ = CCPoset ℳ

------------------------------------------------------------------------------

Fm⟦_⟧ : formula → ℳ.Carrier
Fm⟦ `atom a ⟧ = ℳ.atom a
Fm⟦ ϕ `⇒ ψ ⟧ = Fm⟦ ϕ ⟧ ℳ.⇒ Fm⟦ ψ ⟧
Fm⟦ ϕ `∧ ψ ⟧ = Fm⟦ ϕ ⟧ ℳ.∧ Fm⟦ ψ ⟧
Fm⟦ `⊤ ⟧ = ℳ.⊤

Ctxt⟦_⟧ : context → ℳ.Carrier
Ctxt⟦ ε ⟧      = ℳ.⊤
Ctxt⟦ Γ -, ϕ ⟧ = Ctxt⟦ Γ ⟧ ℳ.∧ Fm⟦ ϕ ⟧

Assump⟦_⟧ : ∀ {Γ ϕ} → ϕ ∈ Γ → Ctxt⟦ Γ ⟧ ℳ.≤ Fm⟦ ϕ ⟧
Assump⟦ here ⟧   = ℳ.x∧y≤y _ _
Assump⟦ next x ⟧ = ℳ.trans (ℳ.x∧y≤x _ _) Assump⟦ x ⟧

Proof⟦_⟧ : ∀ {Γ ϕ} → Γ ⊢ ϕ → Ctxt⟦ Γ ⟧ ℳ.≤ Fm⟦ ϕ ⟧
Proof⟦ assump x ⟧ = Assump⟦ x ⟧
Proof⟦ impI π ⟧ = ℳ.transpose-⇒ Proof⟦ π ⟧
Proof⟦ impE π₁ π₂ ⟧ =
  ℳ.trans (ℳ.∧-greatest ℳ.refl Proof⟦ π₂ ⟧) (ℳ.transpose-∧ Proof⟦ π₁ ⟧)
Proof⟦ andI π₁ π₂ ⟧ = ℳ.∧-greatest Proof⟦ π₁ ⟧ Proof⟦ π₂ ⟧
Proof⟦ andE1 π ⟧ = ℳ.trans Proof⟦ π ⟧ (ℳ.x∧y≤x _ _)
Proof⟦ andE2 π ⟧ = ℳ.trans Proof⟦ π ⟧ (ℳ.x∧y≤y _ _)
Proof⟦ trueI ⟧ = ℳ.maximum _
