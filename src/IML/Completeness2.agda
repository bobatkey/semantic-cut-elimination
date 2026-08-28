{-# OPTIONS --postfix-projections --safe #-}

module IML.Completeness2 {a} (Atom : Set a) where

open import Level using (suc; _⊔_; lift)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import IML.Formula Atom
open import IML.NaturalDeduction Atom
open import IML.Model Atom
open import IML.Frame2 Atom
open import IML.SyntacticFrame2 Atom

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

module _ where

  module SF = Frame syntacticFrame

  ℳ : ModalHeytingAlgebra (suc a) a a
  ℳ = model syntacticFrame

  open import IML.Interpretation Atom ℳ

  import Algebra.Ordered.Construction.LowerSet SF.poset as L
  import Algebra.Ordered.Construction.Covered SF.poset SF.Cover SF.Cover-≤ SF.Elem SF.Elem-≤ as Cl
  open Cl.StrongProduct SF.isCover using (𝐂-isStrongClosureOp)
  import Algebra.Ordered.Construction.Closed.HeytingAlgebra
             L.heytingAlgebra 𝐂-isStrongClosureOp as M

  open M.Elt
  open M._≤_
  open L.LowerSet
  open L._≤_

  mutual
    reflect : ∀ Γ ϕ → Γ ⊢ ϕ → Fm⟦ ϕ ⟧ .elt .ICarrier Γ
    reflect Γ (`atom at) π = Cl.leaf π
    reflect Γ (ϕ `⇒ ψ) π {Δ} Δ≤Γ x = reflect Δ ψ (impE (rename Δ≤Γ π) (reify Δ ϕ x))
    reflect Γ (ϕ `∧ ψ) π = reflect Γ ϕ (andE1 π) , reflect Γ ψ (andE2 π)
    reflect Γ (ϕ `∨ ψ) π = Cl.split (inj₁ (ϕ , ψ , π))
      (λ { Δ (inj₁ ρ) → Cl.leaf (inj₁ (reflect Δ ϕ (rename ρ (assump here))))
         ; Δ (inj₂ ρ) → Cl.leaf (inj₂ (reflect Δ ψ (rename ρ (assump here)))) })
    reflect Γ `⊤ π = lift tt
    reflect Γ `⊥ π = Cl.split (inj₂ π) λ { _ () }
    reflect Γ (`◯ ϕ) π = Cl.leaf (ε -, ϕ , (ϕ , π , ≤-refl) , reflect _ ϕ (assump here))

    reify : ∀ Γ ϕ → Fm⟦ ϕ ⟧ .elt .ICarrier Γ → Γ ⊢ ϕ
    reify Γ (`atom at) (Cl.leaf π) = π
    reify Γ (`atom at) (Cl.split (inj₁ (ϕ , ψ , Γ⊢ϕ∨ψ)) x) =
      orE Γ⊢ϕ∨ψ (reify (Γ -, ϕ) (`atom at) (x _ (inj₁ ≤-refl)))
                 (reify (Γ -, ψ) (`atom at) (x _ (inj₂ ≤-refl)))
    reify Γ (`atom at) (Cl.split (inj₂ Γ⊢⊥) _) = falseE Γ⊢⊥
    reify Γ (ϕ `⇒ ψ) x =
      impI (reify (Γ -, ϕ) ψ (x {Γ -, ϕ} next (reflect (Γ -, ϕ) ϕ (assump here))))
    reify Γ (ϕ `∧ ψ) (x , y) = andI (reify Γ ϕ x) (reify Γ ψ y)
    reify Γ (ϕ `∨ ψ) (Cl.leaf (inj₁ x)) = orI1 (reify _ _ x)
    reify Γ (ϕ `∨ ψ) (Cl.leaf (inj₂ y)) = orI2 (reify _ _ y)
    reify Γ (ϕ `∨ ψ) (Cl.split (inj₁ (χ₁ , χ₂ , Γ⊢χ₁∨χ₂)) x) =
      orE Γ⊢χ₁∨χ₂
          (reify _ _ (x _ (inj₁ ≤-refl)))
          (reify _ _ (x _ (inj₂ ≤-refl)))
    reify Γ (ϕ `∨ ψ) (Cl.split (inj₂ Γ⊢⊥) _) = falseE Γ⊢⊥
    reify Γ `⊤ x = trueI
    reify Γ `⊥ (Cl.split (inj₁ (χ₁ , χ₂ , Γ⊢χ₁∨χ₂)) x) =
      orE Γ⊢χ₁∨χ₂
          (reify _ _ (x _ (inj₁ ≤-refl)))
          (reify _ _ (x _ (inj₂ ≤-refl)))
    reify Γ `⊥ (Cl.split (inj₂ Γ⊢⊥) _) = falseE Γ⊢⊥
    reify Γ (`◯ ϕ) (Cl.leaf (Δ , (ψ , Γ⊢◯ψ , ψ≤Δ) , x)) = mono Γ⊢◯ψ (rename ψ≤Δ (reify _ _ x))
    reify Γ (`◯ ϕ) (Cl.split (inj₁ (χ₁ , χ₂ , Γ⊢χ₁∨χ₂)) x) =
      orE Γ⊢χ₁∨χ₂
          (reify _ _ (x _ (inj₁ ≤-refl)))
          (reify _ _ (x _ (inj₂ ≤-refl)))
    reify Γ (`◯ ϕ) (Cl.split (inj₂ Γ⊢⊥) _) = falseE Γ⊢⊥

  reflect-context : ∀ Γ → Ctxt⟦ Γ ⟧ .elt .ICarrier Γ
  reflect-context ε = lift tt
  reflect-context (Γ -, ϕ) =
    Ctxt⟦ Γ ⟧ .elt .≤-closed next (reflect-context Γ) ,
    reflect _ ϕ (assump here)

  -- completeness / normalisation
  completeness : ∀ {Γ ϕ} → Γ ⊧ ϕ → Γ ⊢ ϕ
  completeness {Γ} {ϕ} σ =
    reify Γ ϕ (σ syntacticFrame .*≤* .*≤* (reflect-context Γ))
