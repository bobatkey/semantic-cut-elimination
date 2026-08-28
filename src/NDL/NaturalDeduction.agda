{-# OPTIONS --postfix-projections --safe #-}

module NDL.NaturalDeduction {a} (Atom : Set a) where

open import NDL.Formula Atom

data context : Set a where
  ε    : context
  _-,_ : context → formula → context

infixl 25 _-,_

data _∈_ : formula → context → Set a where
  here : ∀ {Γ ϕ}   →         ϕ ∈ Γ -, ϕ
  next : ∀ {Γ ϕ ψ} → ϕ ∈ Γ → ϕ ∈ Γ -, ψ

data _⊢_ : context → formula → Set a where
  assump : ∀ {Γ ϕ} → ϕ ∈ Γ → Γ ⊢ ϕ

  trueI  : ∀ {Γ} → Γ ⊢ `⊤

  andI   : ∀ {Γ ϕ ψ} → Γ ⊢ ϕ → Γ ⊢ ψ → Γ ⊢ (ϕ `∧ ψ)
  andE1  : ∀ {Γ ϕ ψ} → Γ ⊢ (ϕ `∧ ψ) → Γ ⊢ ϕ
  andE2  : ∀ {Γ ϕ ψ} → Γ ⊢ (ϕ `∧ ψ) → Γ ⊢ ψ

  falseE : ∀ {Γ ϕ} → Γ ⊢ `⊥ → Γ ⊢ ϕ

  orI1   : ∀ {Γ ϕ ψ} → Γ ⊢ ϕ → Γ ⊢ (ϕ `∨ ψ)
  orI2   : ∀ {Γ ϕ ψ} → Γ ⊢ ψ → Γ ⊢ (ϕ `∨ ψ)
  orE    : ∀ {Γ ϕ ψ χ} → Γ ⊢ (ϕ `∨ ψ) → ε -, ϕ ⊢ χ → ε -, ψ ⊢ χ → Γ ⊢ χ

Ren : context → context → Set a
Ren Γ Δ = ∀ {ϕ} → ϕ ∈ Δ → ϕ ∈ Γ

rename : ∀ {Γ Δ χ} → Ren Γ Δ → Δ ⊢ χ → Γ ⊢ χ
rename ρ (assump x) = assump (ρ x)
rename ρ (andI π₁ π₂) = andI (rename ρ π₁) (rename ρ π₂)
rename ρ (andE1 π) = andE1 (rename ρ π)
rename ρ (andE2 π) = andE2 (rename ρ π)
rename ρ (orI1 π) = orI1 (rename ρ π)
rename ρ (orI2 π) = orI2 (rename ρ π)
rename ρ (orE π π₁ π₂) = orE (rename ρ π) π₁ π₂
rename ρ trueI = trueI
rename ρ (falseE π) = falseE (rename ρ π)

Sub : context → context → Set a
Sub Γ Δ = ∀ {ϕ} → ϕ ∈ Δ → Γ ⊢ ϕ

subst : ∀ {Γ Δ χ} → Sub Γ Δ → Δ ⊢ χ → Γ ⊢ χ
subst σ (assump x) = σ x
subst σ trueI = trueI
subst σ (andI π₁ π₂) = andI (subst σ π₁) (subst σ π₂)
subst σ (andE1 π) = andE1 (subst σ π)
subst σ (andE2 π) = andE2 (subst σ π)
subst σ (falseE π) = falseE (subst σ π)
subst σ (orI1 π) = orI1 (subst σ π)
subst σ (orI2 π) = orI2 (subst σ π)
subst σ (orE π₁ π₂ π₃) = orE (subst σ π₁) π₂ π₃

context→formula : context → formula
context→formula ε        = `⊤
context→formula (Γ -, ϕ) = context→formula Γ `∧ ϕ

context-Sub : ∀ Γ → Sub Γ (ε -, context→formula Γ)
context-Sub ε here = trueI
context-Sub (Γ -, ϕ) here = andI (subst (λ {ϕ = ϕ₁} z → assump (next z)) (context-Sub Γ here)) (assump here)
