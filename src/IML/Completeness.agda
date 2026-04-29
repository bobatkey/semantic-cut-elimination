{-# OPTIONS --postfix-projections --safe #-}

module IML.Completeness {a} (Atom : Set a) {- c ℓ₁ ℓ₂ -} where

open import Level using (suc; _⊔_; lift)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import IML.Formula Atom
open import IML.NaturalDeduction Atom
open import IML.Model Atom
open import IML.Frame Atom
open import IML.SyntacticFrame Atom

-- For completeness:
--
--   If Γ ⊨ ϕ,
--   then for all F, Γx ≤ ϕx
--   so in the syntactic frame, Γχ ≤ ϕχ
-- need to prove:
--   (a): always have ϕ ∈ ⟦ϕ⟧      -- reflect
--   (b): if χ ∈ ⟦ϕ⟧, then χ ⊢ ϕ   -- reify

-- Semantic Entailment, with respect to frames
_⨾_⊧_ : Frame a a a → context → formula → Set a
F ⨾ Γ ⊧ ϕ = Ctxt⟦ Γ ⟧ ℳ.≤ Fm⟦ ϕ ⟧
  where ℳ = model F
        open import IML.Interpretation Atom ℳ

_⊧_ : context → formula → Set (a ⊔ suc a)
Γ ⊧ ϕ = (F : Frame a a a) → F ⨾ Γ ⊧ ϕ

soundness : ∀ {Γ ϕ} → Γ ⊢ ϕ → Γ ⊧ ϕ
soundness π F = Proof⟦ π ⟧
  where ℳ = model F
        open import IML.Interpretation Atom ℳ

open import Algebra.Ordered.Construction.ZeroPlusIdeal

module _ where

  ℳ : ModalHeytingAlgebra (suc a) a a
  ℳ = model syntacticFrame

  open import IML.Interpretation Atom ℳ

  open Ideal

  -- Could also say "η ϕ ≈ Fm⟦ ϕ ⟧", and if η is an order embedding we
  -- get the result?
  --
  -- This proof uses too much special stuff from the syntactic frame,
  -- the η (Yoneda) version is much simpler.

  mutual
    reflect : ∀ ϕ → Fm⟦ ϕ ⟧ .ICarrier ϕ
    reflect (`atom x) = leaf (lift (assump here))
    reflect (ϕ `⇒ ψ) {Γ} Γ≤ϕ⇒ψ ϕ∈Γ =
      Fm⟦ ψ ⟧ .≤-closed (impE Γ≤ϕ⇒ψ (reify _ _ ϕ∈Γ)) (reflect ψ)
    reflect (ϕ `∧ ψ) =
      Fm⟦ ϕ ⟧ .≤-closed (andE1 (assump here)) (reflect ϕ) ,
      Fm⟦ ψ ⟧ .≤-closed (andE2 (assump here)) (reflect ψ)
    reflect (ϕ `∨ ψ) =
      node (leaf (inj₁ (reflect ϕ)))
           (leaf (inj₂ (reflect ψ)))
           (assump here)
    reflect `⊤ = lift tt
    reflect `⊥ = bot (assump here)
    reflect (`◯ ϕ) = leaf (ϕ , assump here , reflect ϕ)

    reify : ∀ ϕ ψ → Fm⟦ ϕ ⟧ .ICarrier ψ → ε -, ψ ⊢ ϕ
    reify (`atom x) Γ (leaf (lift π)) = π
    reify (`atom x) Γ (bot π) = falseE π
    reify (`atom x) Γ (node π₁ π₂ π) =
      orE π (rename (Ren-wk next) (reify (`atom x) _ π₁))
            (rename (Ren-wk next) (reify (`atom x) _ π₂))
    reify (ϕ `⇒ ψ) Γ π = impI (subst σ (reify ψ _ x))
      where x : Fm⟦ ψ ⟧ .ICarrier (Γ `∧ ϕ)
            x = π (andE1 (assump here)) (Fm⟦ ϕ ⟧ .≤-closed (andE2 (assump here)) (reflect ϕ))

            σ : Sub (ε -, Γ -, ϕ) (ε -, (Γ `∧ ϕ))
            σ here = andI (assump (next here)) (assump here)
    reify (ϕ `∧ ψ) Γ (π₁ , π₂) = andI (reify ϕ Γ π₁) (reify ψ Γ π₂)
    reify (ϕ `∨ ψ) Γ (leaf (inj₁ π)) = orI1 (reify ϕ Γ π)
    reify (ϕ `∨ ψ) Γ (leaf (inj₂ π)) = orI2 (reify ψ Γ π)
    reify (ϕ `∨ ψ) Γ (bot π) = falseE π
    reify (ϕ `∨ ψ) Γ (node π₁ π₂ π) =
      orE π (rename (Ren-wk next) (reify _ _ π₁))
            (rename (Ren-wk next) (reify _ _ π₂))
    reify `⊤ Γ π = trueI
    reify `⊥ Γ (bot π) = π
    reify `⊥ Γ (node π₁ π₂ π) =
      orE π (rename (Ren-wk next) (reify `⊥ _ π₁))
            (rename (Ren-wk next) (reify `⊥ _ π₂))
    reify (`◯ ϕ) Γ (leaf (ψ , Γ≤◯ψ , χ∈⟦ϕ⟧)) = mono Γ≤◯ψ (reify _ _ χ∈⟦ϕ⟧)
    reify (`◯ ϕ) Γ (bot π) = falseE π
    reify (`◯ ϕ) Γ (node π₁ π₂ π) =
      orE π (rename (Ren-wk next) (reify _ _ π₁))
            (rename (Ren-wk next) (reify _ _ π₂))

  reflect-context : ∀ Γ → Ctxt⟦ Γ ⟧ .ICarrier (context→formula Γ)
  reflect-context ε = reflect `⊤
  reflect-context (Γ -, ϕ) =
    (Ctxt⟦ Γ ⟧ .≤-closed (andE1 (assump here)) (reflect-context Γ)) ,
    (Fm⟦ ϕ ⟧ .≤-closed (andE2 (assump here)) (reflect ϕ))

completeness : ∀ {Γ ϕ} → Γ ⊧ ϕ → Γ ⊢ ϕ
completeness {Γ} {ϕ} σ =
  subst (context-Sub Γ) (reify ϕ _ (σ syntacticFrame .*≤* (reflect-context Γ)))
