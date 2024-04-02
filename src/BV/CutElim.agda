{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level using (lift; lower)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_; _◅◅_)

module BV.CutElim {a} (Atom : Set a) where

open import BV.Formula Atom
open import BV.Base Atom as BV
import BV.Symmetric Atom as SBV
open import BV.Frame
open FrameModel BV.frame
  using
    ( Chu
    ; module L
    ; module C
    ; embed
    )
  renaming
    ( model to analyticModel
    )
open C using (Chu; pos; neg; int; _==>_; fpos; fneg)
open import BV.Interpretation Atom analyticModel (λ A → embed (`- A))

interactᵖ : ∀ P Q → ((L.ηᵖ Q) L.⊸ᵖ L.εᵖ) L.⅋ᵖ (L.ηᵖ (P `⊗ Q)) L.≤ᵖ L.ηᵖ P
interactᵖ P Q .L.*≤ᵖ* {P′} (Q′ , R′ , P′⟶⋆Q′⅋R , ϕ , lift R≤P⊗Q) = lift P′⟶⋆P
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
  reflect : ∀ P → L.ηᵖ P L.≤ᵖ ⟦ P ⟧ .neg
  reflect `I = 
    L.≤ᵖ-refl
  reflect (P `◁ Q) = 
    L.≤ᵖ-trans L.ηᵖ-preserve-◁ᵖ (L.◁ᵖ-mono (reflect P) (reflect Q))
  reflect (`+ A) =
    L.⊸ᵖ-residual-to (L.≤ᵖ-trans L.ηᵖ-preserve-⅋ᵖ⁻¹ (L.ηᵖ-mono ((step `axiom) ◅ ε)))
  reflect (`- A) = 
    L.≤ᵖ-refl
  reflect (P `⅋ Q) =
    L.≤ᵖ-trans L.ηᵖ-preserve-⅋ᵖ (L.⅋ᵖ-mono (reflect P) (reflect Q))
  reflect (P `⊗ Q) = 
    L.⟨ L.⊸ᵖ-residual-to (L.≤ᵖ-trans (L.⅋ᵖ-mono (reify Q) L.≤ᵖ-refl) (L.≤ᵖ-trans (interactᵖ P Q) (reflect P)))
      , L.⊸ᵖ-residual-to (L.≤ᵖ-trans (L.⅋ᵖ-mono (reify P) (L.ηᵖ-mono (fwd `⊗-comm ◅ ε))) (L.≤ᵖ-trans (interactᵖ Q P) (reflect Q))) ⟩ᵖ
  reify : ∀ P → ⟦ P ⟧ .pos L.≤ᵖ L.ηᵖ P L.⊸ᵖ L.ιᵖ
  reify P = 
    L.⊸ᵖ-residual-to 
      (L.≤ᵖ-trans (L.⅋ᵖ-comm _ _ .proj₁) 
        (L.≤ᵖ-trans (L.⅋ᵖ-mono L.≤ᵖ-refl (reflect P)) 
          (L.≤ᵖ-trans (⟦ P ⟧ .int) L.εᵖ≤ιᵖ)))

  reify′ : ∀ P → ⟦ P ⟧ .pos L.≤ᵖ L.ηᵖ P L.⊸ᵖ L.εᵖ
  reify′ P =
    L.⊸ᵖ-residual-to 
      (L.≤ᵖ-trans (L.⅋ᵖ-comm _ _ .proj₁) 
        (L.≤ᵖ-trans (L.⅋ᵖ-mono L.≤ᵖ-refl (reflect P)) (⟦ P ⟧ .int)))

main-lemma : ∀ P → ⟦ P ⟧ ==> C.¬ (embed P)
main-lemma P .fpos = reify′ P
main-lemma P .fneg = reflect P

sem-cut-elim : ∀ P → C.ε ==> ⟦ P ⟧ → P ⟶⋆ `I
sem-cut-elim P I==>P = q .L.*≤ᵖ* (lift ε) .lower
  where p : C.ε ==> C.¬ (embed P)
        p = C.==>-trans I==>P (main-lemma P)
        q : L.ηᵖ P L.≤ᵖ L.ιᵖ
        q = L.≤ᵖ-trans (p .fneg) L.εᵖ≤ιᵖ

cut-elim : (P : Formula) → (P SBV.⟶⋆ `I) → P ⟶⋆ `I
cut-elim P prf = sem-cut-elim P ⟦ prf ⟧steps
