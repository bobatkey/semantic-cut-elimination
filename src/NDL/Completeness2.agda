{-# OPTIONS --postfix-projections --safe #-}

module NDL.Completeness2 {a} (Atom : Set a) where

open import Level using (suc; _⊔_; lift)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import NDL.Formula Atom
open import NDL.NaturalDeduction Atom
open import NDL.Model Atom
open import NDL.Frame2 Atom
open import NDL.SyntacticFrame2 Atom

_⨾_⊧_ : Frame a a a → context → formula → Set a
F ⨾ Γ ⊧ ϕ = Ctxt⟦ Γ ⟧ ℳ.≤ Fm⟦ ϕ ⟧
  where ℳ = model F
        open import NDL.Interpretation Atom ℳ

_⊧_ : context → formula → Set (a ⊔ suc a)
Γ ⊧ ϕ = (F : Frame a a a) → F ⨾ Γ ⊧ ϕ

soundness : ∀ {Γ ϕ} → Γ ⊢ ϕ → Γ ⊧ ϕ
soundness π F = Proof⟦ π ⟧
  where ℳ = model F
        open import NDL.Interpretation Atom ℳ

module _ where

  module SF = Frame syntacticFrame

  ℳ : NDLModel (suc a) a a
  ℳ = model syntacticFrame

  open import NDL.Interpretation Atom ℳ

  import Algebra.Ordered.Construction.LowerSet SF.poset as L
  import Algebra.Ordered.Construction.Covered SF.poset SF.Cover SF.Cover-≤ SF.Elem SF.Elem-≤ as Cl
  import Algebra.Ordered.Construction.Closed L.≤-poset Cl.𝐂-isClosureOp as M
  open M.BoundedLattice L.isBoundedLattice using (isBoundedLattice)


  open M.Elt
  open M._≤_
  open L.LowerSet
  open L._≤_

  mutual
    reflect : ∀ Γ ϕ → Γ ⊢ ϕ → Fm⟦ ϕ ⟧ .elt .ICarrier Γ
    reflect Γ (`atom at) π = Cl.leaf π
    reflect Γ (ϕ `∧ ψ) π = reflect Γ ϕ (andE1 π) , reflect Γ ψ (andE2 π)
    reflect Γ (ϕ `∨ ψ) π = Cl.split (inj₁ (ϕ , ψ , π))
      (λ { Δ (inj₁ ρ) → Cl.leaf (inj₁ (reflect Δ ϕ (rename ρ (assump here))))
         ; Δ (inj₂ ρ) → Cl.leaf (inj₂ (reflect Δ ψ (rename ρ (assump here)))) })
    reflect Γ `⊤ π = lift tt
    reflect Γ `⊥ π = Cl.split (inj₂ π) λ { _ () }

    reify : ∀ Γ ϕ → Fm⟦ ϕ ⟧ .elt .ICarrier Γ → Γ ⊢ ϕ
    reify Γ (`atom at) (Cl.leaf π) = π
    reify Γ (`atom at) (Cl.split (inj₁ (ϕ , ψ , Γ⊢ϕ∨ψ)) x) =
      orE Γ⊢ϕ∨ψ
          (reify _ _ (x _ (inj₁ ≤-refl)))
          (reify _ _ (x _ (inj₂ ≤-refl)))
    reify Γ (`atom at) (Cl.split (inj₂ Γ⊢⊥) _) = falseE Γ⊢⊥
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

  reflect-context : ∀ Γ → Ctxt⟦ Γ ⟧ .elt .ICarrier Γ
  reflect-context ε = lift tt
  reflect-context (Γ -, ϕ) =
    Ctxt⟦ Γ ⟧ .elt .≤-closed next (reflect-context Γ) ,
    reflect _ ϕ (assump here)

  -- completeness / normalisation
  completeness : ∀ {Γ ϕ} → Γ ⊧ ϕ → Γ ⊢ ϕ
  completeness {Γ} {ϕ} σ =
    reify Γ ϕ (σ syntacticFrame .*≤* .*≤* (reflect-context Γ))
