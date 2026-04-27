{-# OPTIONS --postfix-projections --safe #-}

module MIPL.Completeness {a} (Atom : Set a) where

open import Level using (suc; _⊔_; lift)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import MIPL.Formula Atom
open import MIPL.NaturalDeduction Atom
open import MIPL.Model Atom
open import MIPL.Frame Atom
open import MIPL.SyntacticFrame Atom

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

  -- Could also say "η ϕ ≈ Fm⟦ ϕ ⟧", and if η is an order embedding we
  -- get the result?
  --
  -- This proof uses too much special stuff from the syntactic frame,
  -- the η (Yoneda) version is much simpler.

  mutual
    reflect : ∀ ϕ → Fm⟦ ϕ ⟧ .ICarrier ϕ
    reflect (`atom x) = lift (assump here)
    reflect (ϕ `⇒ ψ) {χ} χ≤ϕ⇒ψ χ∈⟦ϕ⟧ =
      Fm⟦ ψ ⟧ .≤-closed (impE χ≤ϕ⇒ψ (reify _ χ∈⟦ϕ⟧)) (reflect ψ)
    reflect (ϕ `∧ ψ) =
      Fm⟦ ϕ ⟧ .≤-closed (andE1 (assump here)) (reflect ϕ) ,
      Fm⟦ ψ ⟧ .≤-closed (andE2 (assump here)) (reflect ψ)
    reflect `⊤ = lift tt

    reify : ∀ {Γ} ϕ → Fm⟦ ϕ ⟧ .ICarrier Γ → ε -, Γ ⊢ ϕ
    reify (`atom a) (lift π) = π
    reify (ϕ `⇒ ψ) π = impI (subst σ (reify ψ x))
      where x : Fm⟦ ψ ⟧ .ICarrier (_ `∧ ϕ)
            x = π (andE1 (assump here)) (Fm⟦ ϕ ⟧ .≤-closed (andE2 (assump here)) (reflect ϕ))

            σ : Sub (ε -, _ -, ϕ) (ε -, (_ `∧ ϕ))
            σ here = andI (assump (next here)) (assump here)
    reify (ϕ `∧ ψ) (π₁ , π₂) = andI (reify ϕ π₁) (reify ψ π₂)
    reify `⊤ π = trueI

  reflect-context : ∀ Γ → Ctxt⟦ Γ ⟧ .ICarrier (context→formula Γ)
  reflect-context ε = reflect `⊤
  reflect-context (Γ -, ϕ) =
    Ctxt⟦ Γ ⟧ .≤-closed (andE1 (assump here)) (reflect-context Γ) ,
    Fm⟦ ϕ ⟧ .≤-closed (andE2 (assump here)) (reflect ϕ)

completeness : ∀ {Γ ϕ} → Γ ⊧ ϕ → Γ ⊢ ϕ
completeness {Γ} {ϕ} σ =
  subst (context-Sub Γ) (reify ϕ (σ syntacticFrame .*≤* (reflect-context Γ)))
