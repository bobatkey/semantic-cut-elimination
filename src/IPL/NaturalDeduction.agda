{-# OPTIONS --postfix-projections --safe #-}

module IPL.NaturalDeduction {a} (A : Set a) where

open import IPL.Formula A

data context : Set a where
  ε    : context
  _-,_ : context → formula → context

infixl 25 _-,_

data _∈_ : formula → context → Set a where
  here : ∀ {Γ ϕ}   →         ϕ ∈ Γ -, ϕ
  next : ∀ {Γ ϕ ψ} → ϕ ∈ Γ → ϕ ∈ Γ -, ψ

data _⊢_ : context → formula → Set a where
  assump : ∀ {Γ ϕ} → ϕ ∈ Γ → Γ ⊢ ϕ

  impI   : ∀ {Γ ϕ ψ} → Γ -, ϕ ⊢ ψ → Γ ⊢ (ϕ `⇒ ψ)
  impE   : ∀ {Γ ϕ ψ} → Γ ⊢ (ϕ `⇒ ψ) → Γ ⊢ ϕ → Γ ⊢ ψ

  andI   : ∀ {Γ ϕ ψ} → Γ ⊢ ϕ → Γ ⊢ ψ → Γ ⊢ (ϕ `∧ ψ)
  andE1  : ∀ {Γ ϕ ψ} → Γ ⊢ (ϕ `∧ ψ) → Γ ⊢ ϕ
  andE2  : ∀ {Γ ϕ ψ} → Γ ⊢ (ϕ `∧ ψ) → Γ ⊢ ψ

  orI1   : ∀ {Γ ϕ ψ} → Γ ⊢ ϕ → Γ ⊢ (ϕ `∨ ψ)
  orI2   : ∀ {Γ ϕ ψ} → Γ ⊢ ψ → Γ ⊢ (ϕ `∨ ψ)
  orE    : ∀ {Γ ϕ ψ χ} → Γ ⊢ (ϕ `∨ ψ) → Γ -, ϕ ⊢ χ → Γ -, ψ ⊢ χ → Γ ⊢ χ

  trueI  : ∀ {Γ} → Γ ⊢ `⊤

  falseE : ∀ {Γ χ} → Γ ⊢ `⊥ → Γ ⊢ χ

Ren : context → context → Set a
Ren Γ Δ = ∀ {ϕ} → ϕ ∈ Δ → ϕ ∈ Γ

Ren-wk : ∀ {Γ Δ ϕ} → Ren Γ Δ → Ren (Γ -, ϕ) (Δ -, ϕ)
Ren-wk ρ here     = here
Ren-wk ρ (next x) = next (ρ x)

rename : ∀ {Γ Δ χ} → Ren Γ Δ → Δ ⊢ χ → Γ ⊢ χ
rename ρ (assump x) = assump (ρ x)
rename ρ (impI π) = impI (rename (Ren-wk ρ) π)
rename ρ (impE π₁ π₂) = impE (rename ρ π₁) (rename ρ π₂)
rename ρ (andI π₁ π₂) = andI (rename ρ π₁) (rename ρ π₂)
rename ρ (andE1 π) = andE1 (rename ρ π)
rename ρ (andE2 π) = andE2 (rename ρ π)
rename ρ (orI1 π) = orI1 (rename ρ π)
rename ρ (orI2 π) = orI2 (rename ρ π)
rename ρ (orE π π₁ π₂) =
  orE (rename ρ π) (rename (Ren-wk ρ) π₁) (rename (Ren-wk ρ) π₂)
rename ρ trueI = trueI
rename ρ (falseE π) = falseE (rename ρ π)

weaken : ∀ {Γ ϕ χ} → Γ ⊢ χ → Γ -, ϕ ⊢ χ
weaken = rename next

Sub : context → context → Set a
Sub Γ Δ = ∀ {ϕ} → ϕ ∈ Δ → Γ ⊢ ϕ

Sub-wk : ∀ {Γ Δ ϕ} → Sub Γ Δ → Sub (Γ -, ϕ) (Δ -, ϕ)
Sub-wk σ here     = assump here
Sub-wk σ (next x) = weaken (σ x)

subst : ∀ {Γ Δ χ} → Sub Γ Δ → Δ ⊢ χ → Γ ⊢ χ
subst σ (assump x) = σ x
subst σ (impI π) = impI (subst (Sub-wk σ) π)
subst σ (impE π₁ π₂) = impE (subst σ π₁) (subst σ π₂)
subst σ (andI π₁ π₂) = andI (subst σ π₁) (subst σ π₂)
subst σ (andE1 π) = andE1 (subst σ π)
subst σ (andE2 π) = andE2 (subst σ π)
subst σ (orI1 π) = orI1 (subst σ π)
subst σ (orI2 π) = orI2 (subst σ π)
subst σ (orE π π₁ π₂) = orE (subst σ π) (subst (Sub-wk σ) π₁) (subst (Sub-wk σ) π₂)
subst σ trueI = trueI
subst σ (falseE π) = falseE (subst σ π)

context→formula : context → formula
context→formula ε        = `⊤
context→formula (Γ -, ϕ) = context→formula Γ `∧ ϕ

Sub-ext : ∀ {Γ Δ ϕ} → Sub Γ Δ → Γ ⊢ ϕ → Sub Γ (Δ -, ϕ)
Sub-ext σ π here = π
Sub-ext σ π (next x) = σ x

Sub-emp : ∀ {Γ} → Sub Γ ε
Sub-emp ()

-- context-Sub : ∀ Γ → Sub (ε -, context→formula Γ) Γ
-- context-Sub ε ()
-- context-Sub (Γ -, ϕ) here = andE2 (assump here)
-- context-Sub (Γ -, ϕ) (next x) = subst (Sub-ext Sub-emp (andE1 (assump here))) (context-Sub Γ x)

context-Sub : ∀ Γ → Sub Γ (ε -, context→formula Γ)
context-Sub ε here = trueI
context-Sub (Γ -, ϕ) here = andI (rename next (context-Sub Γ here)) (assump here)
