{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level using (lift; lower)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_; _◅◅_)

module MAV.CutElim {a} (Atom : Set a) where

open import MAV.Formula Atom
open import MAV.Base Atom as MAV
import MAV.Symmetric Atom as SMAV
open import MAV.Frame
open FrameModel MAV.frame
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
open C using (Chu; pos; neg; int; _==>_; fpos; fneg)
open import MAV.Interpretation Atom analyticModel (λ A → embed (`- A))

interactᴾ : (P Q : Formula) → (I.U (I.ηⁱ Q) L.⊸ I.U I.ιⁱ) L.⅋ L.η (P `⊗ Q) L.≤ L.η P
interactᴾ P Q .L.*≤* {x} (y , z , x≤y⅋z , ϕ₁ , lift z≤P⊗Q) =
  lift (x≤y⅋z
        ◅◅ (`⅋⟩⋆ z≤P⊗Q)
        ◅◅ (bwd `⅋-comm ◅ ε)
        ◅◅ (step `switch ◅ ε)
        ◅◅ (`⊗⟩⋆ ((bwd `⅋-comm ◅ ε) ◅◅ (ϕ₁ {Q} ((I.leaf Q (lift ε)) , ε)) .lower))
        ◅◅ fwd `⊗-identityʳ ◅ ε)

interact : (P Q : Formula) → (I.ηⁱ Q I.⊸ⁱ I.ιⁱ) I.⅋ⁱ I.ηⁱ (P `⊗ Q) I.≤ⁱ I.ηⁱ P
interact P Q =
    I.≤ⁱ-trans (I.⅋ⁱ-mono I.counit⁻¹ I.≤ⁱ-refl)
    (I.≤ⁱ-trans (I.α-monoidal .proj₁)
    (I.α-mono (L.≤-trans (L.⅋-mono I.U⊸ⁱ L.≤-refl) (interactᴾ P Q))))

mutual
  reflect : (P : Formula) → I.ηⁱ P I.≤ⁱ ⟦ P ⟧ .neg
  reflect `I = I.≤ⁱ-refl
  reflect (`+ A) =
    I.⊸ⁱ-residual-to (I.≤ⁱ-trans I.ηⁱ-preserve-∙⁻¹ (I.ηⁱ-mono ((step `axiom) ◅ ε)))
  reflect (`- A) = 
    I.≤ⁱ-refl
  reflect (P `⅋ Q) = 
    I.≤ⁱ-trans I.ηⁱ-preserve-∙ (I.⅋ⁱ-mono (reflect P) (reflect Q))
  reflect (P `⊗ Q) = 
    I.⟨ I.⊸ⁱ-residual-to (I.≤ⁱ-trans (I.⅋ⁱ-mono (reify Q) I.≤ⁱ-refl) (I.≤ⁱ-trans (interact P Q) (reflect P))) 
      , I.⊸ⁱ-residual-to (I.≤ⁱ-trans (I.⅋ⁱ-mono (reify P) (I.ηⁱ-mono (fwd `⊗-comm ◅ ε))) (I.≤ⁱ-trans (interact Q P) (reflect Q))) ⟩ⁱ
  reflect (P `& Q) = 
    I.≤ⁱ-trans I.η-preserve-∨ⁱ I.[ (I.≤ⁱ-trans (reflect P) I.inj₁ⁱ) , (I.≤ⁱ-trans (reflect Q) I.inj₂ⁱ) ]ⁱ
  reflect (P `⊕ Q) = 
    I.⟨ I.≤ⁱ-trans (I.ηⁱ-mono (step `left ◅ ε)) (reflect P)
      , I.≤ⁱ-trans (I.ηⁱ-mono (step `right ◅ ε)) (reflect Q) ⟩ⁱ
  reflect (P `◁ Q) = I.≤ⁱ-trans I.ηⁱ-preserve-◁ (I.◁ⁱ-mono (reflect P) (reflect Q))

  reify : (P : Formula) → ⟦ P ⟧ .pos I.≤ⁱ I.α (L.η P) I.⊸ⁱ I.ιⁱ
  reify P = I.⊸ⁱ-residual-to (I.≤ⁱ-trans (I.⅋ⁱ-comm _ _ .proj₁)
                               (I.≤ⁱ-trans (I.⅋ⁱ-mono I.≤ⁱ-refl (reflect P))
                               (I.≤ⁱ-trans (⟦ P ⟧ .int) I.εⁱ≤ιⁱ)))

  reify' : (P : Formula) → ⟦ P ⟧ .pos I.≤ⁱ I.α (L.η P) I.⊸ⁱ I.εⁱ
  reify' P = I.⊸ⁱ-residual-to (I.≤ⁱ-trans (I.⅋ⁱ-comm _ _ .proj₁)
                                (I.≤ⁱ-trans (I.⅋ⁱ-mono I.≤ⁱ-refl (reflect P))
                                (⟦ P ⟧ .int)))

-- {-
--   -- I think this only works if we allow the dual of every rule in MAV.Base?
--   --
--   -- If it did, and we had general identity-expansion, then we'd get a slightly slicker proof?
--   --
--   -- Seems to be a problem with ◁ being preserved in both directions?
--   reify0 : (P : Formula) → ⟦ P ⟧ .pos ≤ⁱ α (L.η (`¬ P))
--   reify0 `I = I.≤ⁱ-refl
--   reify0 (`+ x) = I.≤ⁱ-refl
--   reify0 (`- x) = I.≤ⁱ-refl
--   reify0 (P `⅋ Q) = I.≤ⁱ-trans proj₁ⁱ {!!}  -- ⟦Q⟧⁻ ⊸ ⟦P⟧⁺ ≤ ηQ ⊸ η(¬P)
--   reify0 (P `⊗ Q) = I.≤ⁱ-trans (I.⅋ⁱ-mono (reify0 P) (reify0 Q)) I.ηⁱ-preserve-∙⁻¹
--   reify0 (P `& Q) =
--     I.≤ⁱ-trans ⟨ (I.≤ⁱ-trans proj₁ⁱ (reify0 P)) , (I.≤ⁱ-trans proj₂ⁱ (reify0 Q)) ⟩ⁱ
--              {!!} -- need to preserve meets!
--   reify0 (P `⊕ Q) = [ (I.≤ⁱ-trans (reify0 P) (α-mono (η-mono {!!}))) , {!!} ]ⁱ -- need injections into _`&_
--   reify0 (P `◁ Q) = I.≤ⁱ-trans (I.◁ⁱ-mono (reify0 P) (reify0 Q)) {!!}
-- -}

main-lemma : (P : Formula) → ⟦ P ⟧ ==> C.¬ (embed P)
main-lemma P .fpos = reify' P
main-lemma P .fneg = reflect P

sem-cut-elim : (P : Formula) → C.ε ==> ⟦ P ⟧ → P ⟶⋆ `I
sem-cut-elim P I==>P = q .I.*≤ⁱ* (I.leaf P (lift ε) , ε) .lower
  where p : C.ε ==> C.¬ (embed P)
        p = C.==>-trans I==>P (main-lemma P)
        q : I.ηⁱ P I.≤ⁱ I.ιⁱ
        q = I.≤ⁱ-trans (p .fneg) I.εⁱ≤ιⁱ

cut-elim : (P : Formula) → (P SMAV.⟶⋆ `I) → P ⟶⋆ `I
cut-elim P prf = sem-cut-elim P ⟦ prf ⟧steps
