{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level using (lift)
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
  using (embedDual; Chu; module S; tidyup; ⟦I⟧; _==>_; module P; module MS; module M◁; module M)
  renaming (model to analyticModel)

open import MAV.Interpretation Atom analyticModel
  (λ A → embedDual (`- A) (`+ A) (step `axiom ◅ ε))

open Chu
open P
open S
open S.Ideal
open S._≤ⁱ_
open P._≤ᵖ_

-- (η Q ⊸ U ε) ∙ η (P ⊗ Q) ≤ η P
interactᵖ : ∀ P Q → (U (α (P.ηᵖ Q)) M.⇨ᵖ U MS.εⁱ) M.∙ᵖ ηᵖ (P `⊗ Q) ≤ᵖ P.ηᵖ P
interactᵖ P Q .*≤ᵖ* {x} (y , z , x≤y⅋z , ϕ₁ , lift z≤P⊗Q) =
  lift (x≤y⅋z
        ◅◅ (y `⅋⟩⋆ z≤P⊗Q)
        ◅◅ (bwd (`⅋-comm _ _) ◅ ε)
        ◅◅ (step `switch ◅ ε)
        ◅◅ (P `⊗⟩⋆ ((bwd (`⅋-comm _ _) ◅ ε) ◅◅ tidyup (ϕ₁ {Q} ((leaf Q (lift ε)) , ε))))
        ◅◅ fwd (`⊗-identityʳ _) ◅ ε)

interact : ∀ P Q → (α (P.ηᵖ Q) MS.⊸ⁱ MS.εⁱ) MS.∙ⁱ α (P.ηᵖ (P `⊗ Q)) ≤ⁱ α (P.ηᵖ P)
interact P Q =
  ≤ⁱ-trans (MS.∙ⁱ-mono counit⁻¹ ≤ⁱ-refl)
 (≤ⁱ-trans (MS.α-monoidal .proj₁)
 (α-mono (≤ᵖ-trans (M.∙ᵖ-mono MS.U⊸ⁱ ≤ᵖ-refl) (interactᵖ P Q))))

mutual
  reflect : ∀ P → S.α (P.ηᵖ P) S.≤ⁱ ⟦ P ⟧ .neg
  reflect `I = S.≤ⁱ-refl
  reflect (`+ A) = S.≤ⁱ-refl
  reflect (`- A) = S.≤ⁱ-refl
  reflect (P `⅋ Q) = ≤ⁱ-trans MS.ηⁱ-preserve-∙ (MS.∙ⁱ-mono (reflect P) (reflect Q))
  reflect (P `⊗ Q) = ⟨ MS.⊸ⁱ-residual-to (≤ⁱ-trans (MS.∙ⁱ-mono (reify Q) ≤ⁱ-refl) (≤ⁱ-trans (interact P Q) (reflect P)))
                      , MS.⊸ⁱ-residual-to (≤ⁱ-trans (MS.∙ⁱ-mono (reify P) (α-mono (ηᵖ-mono (fwd (`⊗-comm _ _) ◅ ε)))) (≤ⁱ-trans (interact Q P) (reflect Q))) ⟩ⁱ
  reflect (P `& Q) = ≤ⁱ-trans η-preserve-+ [ (≤ⁱ-trans (reflect P) inj₁ⁱ) , (≤ⁱ-trans (reflect Q) inj₂ⁱ) ]ⁱ
  reflect (P `⊕ Q) = ⟨ ≤ⁱ-trans (α-mono (ηᵖ-mono (step `left ◅ ε))) (reflect P) ,
                        ≤ⁱ-trans (α-mono (ηᵖ-mono (step `right ◅ ε))) (reflect Q) ⟩ⁱ
  reflect (P `◁ Q) = ≤ⁱ-trans M◁.ηⁱ-preserve-◁ (M◁.◁ⁱ-mono (reflect P) (reflect Q))

  reify : ∀ P → ⟦ P ⟧ .pos ≤ⁱ α (P.ηᵖ P) MS.⊸ⁱ MS.εⁱ
  reify P = MS.⊸ⁱ-residual-to (≤ⁱ-trans (MS.∙ⁱ-comm _ _ .proj₁)
                                (≤ⁱ-trans (MS.∙ⁱ-mono ≤ⁱ-refl (reflect P))
                                          (⟦ P ⟧ .int)))

sem-cut-elim : ∀ P → ⟦I⟧ ==> ⟦ P ⟧ → P ⟶⋆ `I
sem-cut-elim P I==>P = tidyup (≤ⁱ-trans (reflect P) (I==>P ._==>_.fneg) .*≤ⁱ* (leaf P (lift ε) , ε))

{-
mutual
  reflect : ∀ P → ⟦ P ⟧ .neg .ICarrier P
  reflect `I = S.leaf `I (lift ε) , ε
  reflect (`+ A) = S.leaf (`+ A) (lift ε) , ε
  reflect (`- A) = S.leaf (`- A) (lift ε) , ε
  reflect (P `⅋ Q) = S.leaf (P `⅋ Q) (P , Q , ε , reflect P , reflect Q) , ε
  reflect (P `⊗ Q) .proj₁ {R} x =
    ⟦ P ⟧ .neg .≤-closed
      (step `switch ◅ P `⊗⟩ fwd (`⅋-comm Q R) ◅ (P `⊗⟩⋆ reify Q R x) ◅◅ fwd (`⊗-identityʳ P) ◅ ε)
      (reflect P)
  reflect (P `⊗ Q) .proj₂ {R} x =
    ⟦ Q ⟧ .neg .≤-closed
      (fwd (`⊗-comm P Q) `⟨⅋ R ◅ step `switch ◅ Q `⊗⟩ fwd (`⅋-comm P R) ◅ Q `⊗⟩⋆ reify P R x ◅◅ fwd (`⊗-identityʳ Q) ◅ ε)
      (reflect Q)
  reflect (P `& Q) =
    S.node (S.leaf P (inj₁ (reflect P))) (S.leaf Q (inj₂ (reflect Q))) , ε
  reflect (P `⊕ Q) =
    ⟦ P ⟧ .neg .≤-closed (step `left ◅ ε) (reflect P) ,
    ⟦ Q ⟧ .neg .≤-closed (step `right ◅ ε) (reflect Q)
  reflect (P `◁ Q) =
    P , Q , ε , reflect P , reflect Q

  reify : ∀ P R → ⟦ P ⟧ .pos .ICarrier R → (R `⅋ P) MAV.⟶⋆ `I
  reify P R ϕ =
    tidyup (⟦ P ⟧ .int .*≤ⁱ* {R `⅋ P} (S.leaf (R `⅋ P) (R , P , ε , ϕ , reflect P) , ε))

-- if 'P′ is provable, then it has a cut-free proof
sem-cut-elim : ∀ P → ⟦I⟧ ==> ⟦ P ⟧ → P ⟶⋆ `I
sem-cut-elim P prf = tidyup (prf ._==>_.fneg .*≤ⁱ* {P} (reflect P))
-}

cut-elim : (P : Formula) → (P SMAV.⟶⋆ `I) → P ⟶⋆ `I
cut-elim P prf = sem-cut-elim P ⟦ prf ⟧steps
