{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level using (lift; lower)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_; _◅◅_)

module MAUV.CutElim {a} (Atom : Set a) where

open import MAUV.Formula Atom
open import MAUV.Base Atom as MAUV
import MAUV.Symmetric Atom as SMAUV
open import MAUV.Frame
open FrameModel MAUV.frame
  using
    ( Chu
    ; module L
    ; module I
    ; module C
    ; embed
    )
  renaming
    ( model to analyticModel
    )
open C using (Chu; pos; neg; int; _≤_; fpos; fneg)
open import MAUV.Interpretation Atom analyticModel (λ A → embed (`- A))

interactᴾ : (P Q : Formula) → (I.U (I.η Q) L.⊸ I.U I.ι) L.⅋ L.η (P `⊗ Q) L.≤ L.η P
interactᴾ P Q .L.*≤* {x} (y , z , x≤y⅋z , ϕ₁ , lift z≤P⊗Q) =
  lift (x≤y⅋z
        ◅◅ (`⅋⟩⋆ z≤P⊗Q)
        ◅◅ (bwd `⅋-comm ◅ ε)
        ◅◅ (step `switch ◅ ε)
        ◅◅ (`⊗⟩⋆ ((bwd `⅋-comm ◅ ε) ◅◅ (ϕ₁ {Q} ((I.leaf Q (lift ε)) , ε)) .lower))
        ◅◅ fwd `⊗-identityʳ ◅ ε)

interact : (P Q : Formula) → (I.η Q I.⊸ I.ι) I.⅋ I.η (P `⊗ Q) I.≤ I.η P
interact P Q =
    I.≤-trans (I.⅋-mono I.counit⁻¹ I.≤-refl)
    (I.≤-trans (I.α-monoidal .proj₁)
    (I.α-mono (L.≤-trans (L.⅋-mono I.U⊸ L.≤-refl) (interactᴾ P Q))))

mutual
  reflect : (P : Formula) → I.η P I.≤ ⟦ P ⟧ .neg
  reflect `I = I.≤-refl
  reflect `𝟘 = I.⊤-maximum _
  reflect `⊤ = I.η-preserve-⊥ᶜ
  reflect (`+ A) =
    I.⊸-residual-to (I.≤-trans I.η-preserve-∙⁻¹ (I.η-mono ((step `axiom) ◅ ε)))
  reflect (`- A) =
    I.≤-refl
  reflect (P `⅋ Q) =
    I.≤-trans I.η-preserve-∙ (I.⅋-mono (reflect P) (reflect Q))
  reflect (P `⊗ Q) =
    I.∧-greatest
      (I.⊸-residual-to (I.≤-trans (I.⅋-mono (reify Q) I.≤-refl) (I.≤-trans (interact P Q) (reflect P))))
      (I.⊸-residual-to (I.≤-trans (I.⅋-mono (reify P) (I.η-mono (fwd `⊗-comm ◅ ε))) (I.≤-trans (interact Q P) (reflect Q))))
  reflect (P `& Q) =
    I.≤-trans I.η-preserve-∨ 
      (I.∨-least
        (I.≤-trans (reflect P) I.x≤x∨y)
        (I.≤-trans (reflect Q) I.y≤x∨y))
  reflect (P `⊕ Q) =
    I.∧-greatest
      (I.≤-trans (I.η-mono (step `left ◅ ε)) (reflect P))
      (I.≤-trans (I.η-mono (step `right ◅ ε)) (reflect Q))
  reflect (P `◁ Q) = I.≤-trans I.η-preserve-◁ (I.◁-mono (reflect P) (reflect Q))

  reify : (P : Formula) → ⟦ P ⟧ .pos I.≤ I.α (L.η P) I.⊸ I.ι
  reify P = I.⊸-residual-to (I.≤-trans (I.⅋-comm _ _ .proj₁)
                               (I.≤-trans (I.⅋-mono I.≤-refl (reflect P))
                               (I.≤-trans (⟦ P ⟧ .int) I.ε≤ι)))

  reify' : (P : Formula) → ⟦ P ⟧ .pos I.≤ I.α (L.η P) I.⊸ I.ε
  reify' P = I.⊸-residual-to (I.≤-trans (I.⅋-comm _ _ .proj₁)
                                (I.≤-trans (I.⅋-mono I.≤-refl (reflect P))
                                (⟦ P ⟧ .int)))

main-lemma : (P : Formula) → ⟦ P ⟧ ≤ C.¬ (embed P)
main-lemma P .fpos = reify' P
main-lemma P .fneg = reflect P

sem-cut-elim : (P : Formula) → C.ε ≤ ⟦ P ⟧ → P ⟶⋆ `I
sem-cut-elim P I≤P = q .I.*≤* (I.leaf P (lift ε) , ε) .lower
  where p : C.ε ≤ C.¬ (embed P)
        p = C.≤-trans I≤P (main-lemma P)
        q : I.η P I.≤ I.ι
        q = I.≤-trans (p .fneg) I.ε≤ι

cut-elim : (P : Formula) → (P SMAUV.⟶⋆ `I) → P ⟶⋆ `I
cut-elim P prf = sem-cut-elim P ⟦ prf ⟧steps
