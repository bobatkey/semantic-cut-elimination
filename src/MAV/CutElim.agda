{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level using (lift; lower)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_; _◅◅_)

module MAV.CutElim {a} (Atom : Set a) where

open import MAV.Structure Atom
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
open C using (Chu; pos; neg; int; _≤_; fpos; fneg)
open import MAV.Interpretation Atom analyticModel (λ A → embed (`- A))

interactᴾ : (P Q : Structure) → (I.U (I.η Q) L.⊸ I.U I.ι) L.⅋ L.η (P `⊗ Q) L.≤ L.η P
interactᴾ P Q .L.*≤* {x} (y , z , x≤y⅋z , ϕ₁ , lift z≤P⊗Q) =
  lift (x≤y⅋z
        ◅◅ (`⅋⟩⋆ z≤P⊗Q)
        ◅◅ (bwd `⅋-comm ◅ ε)
        ◅◅ (step `switch ◅ ε)
        ◅◅ (`⊗⟩⋆ ((bwd `⅋-comm ◅ ε) ◅◅ (ϕ₁ {Q} (I.leaf (lift ε))) .lower))
        ◅◅ fwd `⊗-identityʳ ◅ ε)

interact : (P Q : Structure) → (I.η Q I.⊸ I.ι) I.⅋ I.η (P `⊗ Q) I.≤ I.η P
interact P Q =
    I.≤-trans (I.⅋-mono I.counit⁻¹ I.≤-refl)
    (I.≤-trans (I.α-monoidal .proj₁)
    (I.α-mono (L.≤-trans (L.⅋-mono I.U⊸ L.≤-refl) (interactᴾ P Q))))

mutual
  reflect : (P : Structure) → I.η P I.≤ ⟦ P ⟧ .neg
  reflect `I = I.≤-refl
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

  reify : (P : Structure) → ⟦ P ⟧ .pos I.≤ I.α (L.η P) I.⊸ I.ι
  reify P = I.⊸-residual-to (I.≤-trans (I.⅋-comm _ _ .proj₁)
                               (I.≤-trans (I.⅋-mono I.≤-refl (reflect P))
                               (I.≤-trans (⟦ P ⟧ .int) I.ε≤ι)))

  reify' : (P : Structure) → ⟦ P ⟧ .pos I.≤ I.α (L.η P) I.⊸ I.ε
  reify' P = I.⊸-residual-to (I.≤-trans (I.⅋-comm _ _ .proj₁)
                                (I.≤-trans (I.⅋-mono I.≤-refl (reflect P))
                                (⟦ P ⟧ .int)))

-- {-
--   -- I think this only works if we allow the dual of every rule in MAV.Base?
--   --
--   -- If it did, and we had general identity-expansion, then we'd get a slightly slicker proof?
--   --
--   -- Seems to be a problem with ◁ being preserved in both directions?
--   reify0 : (P : Structure) → ⟦ P ⟧ .pos ≤ α (L.η (`¬ P))
--   reify0 `I = I.≤-refl
--   reify0 (`+ x) = I.≤-refl
--   reify0 (`- x) = I.≤-refl
--   reify0 (P `⅋ Q) = I.≤-trans proj₁ {!!}  -- ⟦Q⟧⁻ ⊸ ⟦P⟧⁺ ≤ ηQ ⊸ η(¬P)
--   reify0 (P `⊗ Q) = I.≤-trans (I.⅋-mono (reify0 P) (reify0 Q)) I.η-preserve-∙⁻¹
--   reify0 (P `& Q) =
--     I.≤-trans ⟨ (I.≤-trans proj₁ (reify0 P)) , (I.≤-trans proj₂ (reify0 Q)) ⟩
--              {!!} -- need to preserve meets!
--   reify0 (P `⊕ Q) = [ (I.≤-trans (reify0 P) (α-mono (η-mono {!!}))) , {!!} ] -- need injections into _`&_
--   reify0 (P `◁ Q) = I.≤-trans (I.◁-mono (reify0 P) (reify0 Q)) {!!}
-- -}

main-lemma : (P : Structure) → ⟦ P ⟧ ≤ C.¬ (embed P)
main-lemma P .fpos = reify' P
main-lemma P .fneg = reflect P

sem-cut-elim : (P : Structure) → C.ε ≤ ⟦ P ⟧ → P ⟶⋆ `I
sem-cut-elim P I≤P = q .I.*≤* (I.leaf (lift ε)) .lower
  where p : C.ε ≤ C.¬ (embed P)
        p = C.≤-trans I≤P (main-lemma P)
        q : I.η P I.≤ I.ι
        q = I.≤-trans (p .fneg) I.ε≤ι

cut-elim : (P : Structure) → (P SMAV.⟶⋆ `I) → P ⟶⋆ `I
cut-elim P prf = sem-cut-elim P ⟦ prf ⟧steps
