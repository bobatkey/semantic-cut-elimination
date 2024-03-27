{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level using (lift; lower)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary using (Preorder)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_; _◅◅_)

module MAV.CutElim {a} (Atom : Set a) where

open import MAV.Formula Atom
open import MAV.Base Atom as MAV
import MAV.Symmetric Atom as SMAV
import MAV.Frame

open MAV.Frame.FrameModel MAV.frame
  using (Chu; module S; tidyup; ⟦I⟧; _==>_; module P; module MS; module M◁; module M; module D; embed; ⟦¬⟧)
  renaming (model to analyticModel)

open import MAV.Interpretation Atom analyticModel (λ A → embed (`- A))

open Chu
open P
open S
open S.Ideal
open S._≤ⁱ_
open P._≤ᵖ_

-- (η Q ⊸ U ι) ∙ η (P ⊗ Q) ≤ η P
interactᵖ : ∀ P Q → (U (ηⁱ Q) M.⇨ᵖ U M◁.ιⁱ) M.∙ᵖ ηᵖ (P `⊗ Q) ≤ᵖ P.ηᵖ P
interactᵖ P Q .*≤ᵖ* {x} (y , z , x≤y⅋z , ϕ₁ , lift z≤P⊗Q) =
  lift (x≤y⅋z
        ◅◅ (y `⅋⟩⋆ z≤P⊗Q)
        ◅◅ (bwd (`⅋-comm _ _) ◅ ε)
        ◅◅ (step `switch ◅ ε)
        ◅◅ (P `⊗⟩⋆ ((bwd (`⅋-comm _ _) ◅ ε) ◅◅ (ϕ₁ {Q} ((leaf Q (lift ε)) , ε)) .lower))
        ◅◅ fwd (`⊗-identityʳ _) ◅ ε)

interact : ∀ P Q → (ηⁱ Q MS.⊸ⁱ M◁.ιⁱ) MS.∙ⁱ ηⁱ (P `⊗ Q) ≤ⁱ ηⁱ P
interact P Q =
  ≤ⁱ-trans (MS.∙ⁱ-mono counit⁻¹ ≤ⁱ-refl)
 (≤ⁱ-trans (MS.α-monoidal .proj₁)
 (α-mono (≤ᵖ-trans (M.∙ᵖ-mono MS.U⊸ⁱ ≤ᵖ-refl) (interactᵖ P Q))))

mutual
  reflect : ∀ P → ηⁱ P S.≤ⁱ ⟦ P ⟧ .neg
  reflect `I = S.≤ⁱ-refl
  reflect (`+ A) =
    MS.⊸ⁱ-residual-to (≤ⁱ-trans MS.ηⁱ-preserve-∙⁻¹ (ηⁱ-mono ((step `axiom) ◅ ε)))
  reflect (`- A) = S.≤ⁱ-refl
  reflect (P `⅋ Q) = ≤ⁱ-trans MS.ηⁱ-preserve-∙ (MS.∙ⁱ-mono (reflect P) (reflect Q))
  reflect (P `⊗ Q) = ⟨ MS.⊸ⁱ-residual-to (≤ⁱ-trans (MS.∙ⁱ-mono (reify Q) ≤ⁱ-refl) (≤ⁱ-trans (interact P Q) (reflect P)))
                      , MS.⊸ⁱ-residual-to (≤ⁱ-trans (MS.∙ⁱ-mono (reify P) (ηⁱ-mono (fwd (`⊗-comm _ _) ◅ ε))) (≤ⁱ-trans (interact Q P) (reflect Q))) ⟩ⁱ
  reflect (P `& Q) = ≤ⁱ-trans η-preserve-+ [ (≤ⁱ-trans (reflect P) inj₁ⁱ) , (≤ⁱ-trans (reflect Q) inj₂ⁱ) ]ⁱ
  reflect (P `⊕ Q) = ⟨ ≤ⁱ-trans (ηⁱ-mono (step `left ◅ ε)) (reflect P) ,
                        ≤ⁱ-trans (ηⁱ-mono (step `right ◅ ε)) (reflect Q) ⟩ⁱ
  reflect (P `◁ Q) = ≤ⁱ-trans M◁.ηⁱ-preserve-◁ (M◁.◁ⁱ-mono (reflect P) (reflect Q))

  reify : ∀ P → ⟦ P ⟧ .pos ≤ⁱ α (P.ηᵖ P) MS.⊸ⁱ M◁.ιⁱ
  reify P = MS.⊸ⁱ-residual-to (≤ⁱ-trans (MS.∙ⁱ-comm _ _ .proj₁)
                               (≤ⁱ-trans (MS.∙ⁱ-mono ≤ⁱ-refl (reflect P))
                               (≤ⁱ-trans (⟦ P ⟧ .int) D.εⁱ≤ιⁱ)))

  reify' : ∀ P → ⟦ P ⟧ .pos ≤ⁱ α (P.ηᵖ P) MS.⊸ⁱ MS.εⁱ
  reify' P = MS.⊸ⁱ-residual-to (≤ⁱ-trans (MS.∙ⁱ-comm _ _ .proj₁)
                                (≤ⁱ-trans (MS.∙ⁱ-mono ≤ⁱ-refl (reflect P))
                                (⟦ P ⟧ .int)))

{-
  -- I think this only works if we allow the dual of every rule in MAV.Base?
  --
  -- If it did, and we had general identity-expansion, then we'd get a slightly slicker proof?
  --
  -- Seems to be a problem with ◁ being preserved in both directions?
  reify0 : ∀ P → ⟦ P ⟧ .pos ≤ⁱ α (P.ηᵖ (`¬ P))
  reify0 `I = S.≤ⁱ-refl
  reify0 (`+ x) = S.≤ⁱ-refl
  reify0 (`- x) = S.≤ⁱ-refl
  reify0 (P `⅋ Q) = ≤ⁱ-trans proj₁ⁱ {!!}  -- ⟦Q⟧⁻ ⊸ ⟦P⟧⁺ ≤ ηQ ⊸ η(¬P)
  reify0 (P `⊗ Q) = ≤ⁱ-trans (MS.∙ⁱ-mono (reify0 P) (reify0 Q)) MS.ηⁱ-preserve-∙⁻¹
  reify0 (P `& Q) =
    ≤ⁱ-trans ⟨ (≤ⁱ-trans proj₁ⁱ (reify0 P)) , (≤ⁱ-trans proj₂ⁱ (reify0 Q)) ⟩ⁱ
             {!!} -- need to preserve meets!
  reify0 (P `⊕ Q) = [ (≤ⁱ-trans (reify0 P) (α-mono (ηᵖ-mono {!!}))) , {!!} ]ⁱ -- need injections into _`&_
  reify0 (P `◁ Q) = ≤ⁱ-trans (M◁.◁ⁱ-mono (reify0 P) (reify0 Q)) {!!}
-}


morphism : ∀ P → ⟦ P ⟧ ==> ⟦¬⟧ (embed P)
morphism P ._==>_.fpos = reify' P
morphism P ._==>_.fneg = reflect P

sem-cut-elim : ∀ P → ⟦I⟧ ==> ⟦ P ⟧ → P ⟶⋆ `I
sem-cut-elim P I==>P = tidyup (≤ⁱ-trans (reflect P) (I==>P ._==>_.fneg) .*≤ⁱ* (leaf P (lift ε) , ε))

cut-elim : (P : Formula) → (P SMAV.⟶⋆ `I) → P ⟶⋆ `I
cut-elim P prf = sem-cut-elim P ⟦ prf ⟧steps
