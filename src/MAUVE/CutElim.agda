{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level using (lift; lower)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_; _◅◅_)

module MAUVE.CutElim {a} (Atom : Set a) where

open import MAUVE.Structure Atom
open import MAUVE.Base Atom as MAUVE
import MAUVE.Symmetric Atom as SMAUVE
open import MAUVE.Frame
open FrameModel MAUVE.frame
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
open import MAUVE.Interpretation Atom analyticModel (λ A → embed (`- A))

interactᴾ : (P Q : Structure) → (I.U (I.η Q) L.⊸ I.U I.ι) L.⅋ L.η (P `⊗ Q) L.≤ L.η P
interactᴾ P Q .L.*≤* {x} (y , z , x≤y⅋z , ϕ₁ , lift z≤P⊗Q) =
  lift (x≤y⅋z
        ◅◅ (`⅋⟩⋆ z≤P⊗Q)
        ◅◅ (bwd `⅋-comm ◅ ε)
        ◅◅ (step `switch ◅ ε)
        ◅◅ (`⊗⟩⋆ ((bwd `⅋-comm ◅ ε) ◅◅ (ϕ₁ {Q} ((I.leaf Q (lift ε)) , ε)) .lower))
        ◅◅ fwd `⊗-identityʳ ◅ ε)

interact : (P Q : Structure) → (I.η Q I.⊸ I.ι) I.⅋ I.η (P `⊗ Q) I.≤ I.η P
interact P Q =
    I.≤-trans (I.⅋-mono I.counit⁻¹ I.≤-refl)
    (I.≤-trans (I.α-monoidal .proj₁)
    (I.α-mono (L.≤-trans (L.⅋-mono I.U⊸ L.≤-refl) (interactᴾ P Q))))

interact-！ᴸ : ∀ P → (L.！ (L.η P L.⊸ I.U I.ι) L.⅋ L.η (`! P)) L.≤ L.ε
interact-！ᴸ P .L.*≤* {P'} (Q , R , P'⟶⋆QR , (Q' , Q≤Q' , ?Q' , ϕ) , lift R≤!P)  =
  lift P'⟶⋆I
  where
    promote : ∀ {S T} → L.!-context T → `! S `⅋ T ⟶⋆ `! (S `⅋ T)
    promote L.nil = (fwd `⅋-identityʳ ◅ ε) ◅◅ (`!⟩⋆ (bwd `⅋-identityʳ ◅ ε))
    promote (L.pair c d) = (bwd `⅋-assoc ◅ ε) ◅◅ (promote c `⟨⅋⋆) ◅◅ promote d ◅◅ (`!⟩⋆ (fwd `⅋-assoc ◅ ε))
    promote L.leaf = (`⅋⟩⋆ (step `δ ◅ ε)) ◅◅ (step `p ◅ ε)

    P'⟶⋆I : P' ⟶⋆ `I
    P'⟶⋆I = P'⟶⋆QR
         ◅◅ (Q≤Q' `⟨⅋⋆)
         ◅◅ (`⅋⟩⋆ R≤!P)
         ◅◅ (fwd `⅋-comm ◅ ε)
         ◅◅ promote ?Q'
         ◅◅ (`!⟩⋆ (fwd `⅋-comm ◅ ε))
         ◅◅ (`!⟩⋆ (ϕ {P} (lift ε) .lower))
         ◅◅ step `e ◅ ε

interact-！ : ∀ P → (I.！ (I.η P I.⊸ I.ι) I.⅋ I.η (`! P)) I.≤ I.ε
interact-！ P =
  I.≤-trans
    (I.α-monoidal .proj₁)
    (I.α-mono (L.≤-trans (L.⅋-mono (L.！-mono (L.≤-trans I.U⊸ help)) L.≤-refl)
                         (interact-！ᴸ P)))
  where help : (I.U (I.η P)) L.⊸ (I.U I.ι) L.≤ L.η P L.⊸ I.U I.ι
        help = L.⊸-residual-to (L.≤-trans (L.⅋-mono I.unit L.≤-refl)
                                          (L.⊸-residual-from L.≤-refl))

mutual
  reflect : (P : Structure) → I.η P I.≤ ⟦ P ⟧ .neg
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
  reflect (`? P) =
    I.≤-trans I.η-preserve-！ (I.！-mono (reflect P))
  reflect (`! P) =
    I.⊸-residual-to (I.≤-trans (I.⅋-mono (I.！-mono (reify P)) I.≤-refl) (interact-！ P))


  reify : (P : Structure) → ⟦ P ⟧ .pos I.≤ I.α (L.η P) I.⊸ I.ι
  reify P = I.⊸-residual-to (I.≤-trans (I.⅋-comm _ _ .proj₁)
                               (I.≤-trans (I.⅋-mono I.≤-refl (reflect P))
                               (I.≤-trans (⟦ P ⟧ .int) I.ε≤ι)))

  reify' : (P : Structure) → ⟦ P ⟧ .pos I.≤ I.α (L.η P) I.⊸ I.ε
  reify' P = I.⊸-residual-to (I.≤-trans (I.⅋-comm _ _ .proj₁)
                                (I.≤-trans (I.⅋-mono I.≤-refl (reflect P))
                                (⟦ P ⟧ .int)))

main-lemma : (P : Structure) → ⟦ P ⟧ ≤ C.¬ (embed P)
main-lemma P .fpos = reify' P
main-lemma P .fneg = reflect P

sem-cut-elim : (P : Structure) → C.ε ≤ ⟦ P ⟧ → P ⟶⋆ `I
sem-cut-elim P I≤P = q .I.*≤* (I.leaf P (lift ε) , ε) .lower
  where p : C.ε ≤ C.¬ (embed P)
        p = C.≤-trans I≤P (main-lemma P)
        q : I.η P I.≤ I.ι
        q = I.≤-trans (p .fneg) I.ε≤ι

cut-elim : (P : Structure) → (P SMAUVE.⟶⋆ `I) → P ⟶⋆ `I
cut-elim P prf = sem-cut-elim P ⟦ prf ⟧steps
