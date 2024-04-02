{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level using (lift; lower)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_; _◅◅_)

module BV.CutElim {a} (Atom : Set a) where

open import BV.Formula Atom
open import BV.Base Atom as BV
import BV.Symmetric Atom as SBV
import BV.Frame

open BV.Frame.FrameModel BV.frame
  using
    ( Chu
    ; ==>-trans
    ; ⟦I⟧
    ; _==>_
    ; module P
    ; module M
    ; module D
    ; embed
    ; ⟦¬⟧)
  renaming
    ( model to analyticModel
    )

open import BV.Interpretation Atom analyticModel (λ A → embed (`- A))

open Chu
open P

interactᵖ : ∀ P Q → ((ηᵖ Q) M.⇨ᵖ M.εᵖ) M.∙ᵖ (ηᵖ (P `⊗ Q)) ≤ᵖ ηᵖ P
interactᵖ P Q ._≤ᵖ_.*≤ᵖ* {P′} (Q′ , R′ , P′⟶⋆Q′⅋R , ϕ , lift R≤P⊗Q) = lift P′⟶⋆P
  where
    P′⟶⋆P : P′ ⟶⋆ P
    P′⟶⋆P = P′⟶⋆Q′⅋R
          ◅◅ `⅋⟩⋆ R≤P⊗Q
          ◅◅ (bwd `⅋-comm ◅ ε)
          ◅◅ (step `switch ◅ ε)
          ◅◅ `⊗⟩⋆ (bwd `⅋-comm ◅ ε)
          ◅◅ `⊗⟩⋆ (ϕ {Q} (lift ε)) .lower
          ◅◅ (fwd `⊗-identityʳ ◅ ε)

mutual
  reflect : ∀ P → ηᵖ P P.≤ᵖ ⟦ P ⟧ .neg
  reflect `I = 
    P.≤ᵖ-refl
  reflect (P `◁ Q) = 
    ≤ᵖ-trans D.ηᵖ-preserve-◁ᵖ (D.◁ᵖ-mono (reflect P) (reflect Q))
  reflect (`+ A) =
    M.⇨ᵖ-residual-to (≤ᵖ-trans M.ηᵖ-preserve-∙ᵖ⁻¹ (ηᵖ-mono ((step `axiom) ◅ ε)))
  reflect (`- A) = 
    P.≤ᵖ-refl
  reflect (P `⅋ Q) =
    ≤ᵖ-trans M.ηᵖ-preserve-∙ᵖ (M.∙ᵖ-mono (reflect P) (reflect Q))
  reflect (P `⊗ Q) = 
    ⟨ M.⇨ᵖ-residual-to (≤ᵖ-trans (M.∙ᵖ-mono (reify Q) ≤ᵖ-refl) (≤ᵖ-trans (interactᵖ P Q) (reflect P)))
    , M.⇨ᵖ-residual-to (≤ᵖ-trans (M.∙ᵖ-mono (reify P) (ηᵖ-mono (fwd `⊗-comm ◅ ε))) (≤ᵖ-trans (interactᵖ Q P) (reflect Q))) ⟩ᵖ
  reify : ∀ P → ⟦ P ⟧ .pos ≤ᵖ P.ηᵖ P M.⇨ᵖ D.ιᵖ
  reify P = 
    M.⇨ᵖ-residual-to 
      (≤ᵖ-trans (M.∙ᵖ-comm _ _ .proj₁) 
        (≤ᵖ-trans (M.∙ᵖ-mono ≤ᵖ-refl (reflect P)) 
          (≤ᵖ-trans (⟦ P ⟧ .int) D.εᵖ≤ιᵖ)))

  reify′ : ∀ P → ⟦ P ⟧ .pos ≤ᵖ P.ηᵖ P M.⇨ᵖ M.εᵖ
  reify′ P =
    M.⇨ᵖ-residual-to 
      (≤ᵖ-trans (M.∙ᵖ-comm _ _ .proj₁) 
        (≤ᵖ-trans (M.∙ᵖ-mono ≤ᵖ-refl (reflect P)) (⟦ P ⟧ .int)))

open _==>_

main-lemma : ∀ P → ⟦ P ⟧ ==> ⟦¬⟧ (embed P)
main-lemma P .fpos = reify′ P
main-lemma P .fneg = reflect P

sem-cut-elim : ∀ P → ⟦I⟧ ==> ⟦ P ⟧ → P ⟶⋆ `I
sem-cut-elim P I==>P = q ._≤ᵖ_.*≤ᵖ* (lift ε) .lower
  where p : ⟦I⟧ ==> ⟦¬⟧ (embed P)
        p = ==>-trans I==>P (main-lemma P)

        q : ηᵖ P ≤ᵖ D.ιᵖ
        q = ≤ᵖ-trans (p .fneg) D.εᵖ≤ιᵖ

cut-elim : (P : Formula) → (P SBV.⟶⋆ `I) → P ⟶⋆ `I
cut-elim P prf = sem-cut-elim P ⟦ prf ⟧steps
