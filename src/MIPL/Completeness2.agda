{-# OPTIONS --postfix-projections --safe #-}

module MIPL.Completeness2 {a} (Atom : Set a) where

open import Level using (suc; _⊔_; lift)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import MIPL.Formula Atom
open import MIPL.NaturalDeduction Atom
open import MIPL.Model Atom
open import MIPL.Frame2 Atom
open import MIPL.SyntacticFrame2 Atom

-- Semantic Entailment, with respect to frames
_⨾_⊧_ : Frame a a a → context → formula → Set a
F ⨾ Γ ⊧ ϕ = Ctxt⟦ Γ ⟧ ℳ.≤ Fm⟦ ϕ ⟧
  where ℳ = model F
        open import MIPL.Interpretation Atom ℳ

_⊧_ : context → formula → Set (a ⊔ suc a)
Γ ⊧ ϕ = (F : Frame a a a) → F ⨾ Γ ⊧ ϕ

soundness : ∀ {Γ ϕ} → Γ ⊢ ϕ → Γ ⊧ ϕ
soundness π F = Proof⟦ π ⟧
  where ℳ = model F
        open import MIPL.Interpretation Atom ℳ

open import Algebra.Ordered.Construction.LowerSet

module _ where

  ℳ : CCPoset (suc a) a a
  ℳ = model syntacticFrame

  open import MIPL.Interpretation Atom ℳ

  open LowerSet

  mutual
    reflect : ∀ Γ ϕ → Γ ⊢ ϕ → Fm⟦ ϕ ⟧ .ICarrier Γ
    reflect Γ (`atom x) π = π
    reflect Γ (ϕ `⇒ ψ) π {Δ} Δ≤Γ x = reflect Δ ψ (impE (rename Δ≤Γ π) (reify Δ ϕ x))
    reflect Γ (ϕ `∧ ψ) π = reflect Γ ϕ (andE1 π) , reflect Γ ψ (andE2 π)
    reflect Γ `⊤ _ = lift tt

    reify : ∀ Γ ϕ → Fm⟦ ϕ ⟧ .ICarrier Γ → Γ ⊢ ϕ
    reify Γ (`atom a) π = π
    reify Γ (ϕ `⇒ ψ) f = impI (reify _ _ (f next (reflect _ ϕ (assump here))))
    reify Γ (ϕ `∧ ψ) (π₁ , π₂) = andI (reify Γ ϕ π₁) (reify Γ ψ π₂)
    reify Γ `⊤ π = trueI

  reflect-context : ∀ Γ → Ctxt⟦ Γ ⟧ .ICarrier Γ
  reflect-context ε = lift tt
  reflect-context (Γ -, ϕ) =
    Ctxt⟦ Γ ⟧ .≤-closed next (reflect-context Γ) ,
    reflect (Γ -, ϕ) ϕ (assump here)

completeness : ∀ {Γ ϕ} → Γ ⊧ ϕ → Γ ⊢ ϕ
completeness {Γ} {ϕ} σ =
  reify Γ ϕ (σ syntacticFrame .*≤* (reflect-context Γ))
