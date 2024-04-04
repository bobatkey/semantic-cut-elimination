{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level using (lift; lower)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_; _◅◅_)

module NEL.CutElim {a} (Atom : Set a) where

open import NEL.Formula Atom
open import NEL.Base Atom as NEL
import NEL.Symmetric Atom as SNEL
open import NEL.Frame
open FrameModel NEL.frame
  using
    ( Chu
    ; module L
    ; module C
    ; embed
    )
  renaming
    ( model to analyticModel
    )
open C using (Chu; pos; neg; int; _≤_; fpos; fneg)
open import NEL.Interpretation Atom analyticModel (λ A → embed (`- A))

interact : ∀ P Q → ((L.η Q) L.⊸ L.ε) L.⅋ (L.η (P `⊗ Q)) L.≤ L.η P
interact P Q .L.*≤* {P′} (Q′ , R′ , P′⟶⋆Q′⅋R , ϕ , lift R≤P⊗Q) = lift P′⟶⋆P
  where
    P′⟶⋆P : P′ ⟶⋆ P
    P′⟶⋆P = P′⟶⋆Q′⅋R
          ◅◅ `⅋⟩⋆ R≤P⊗Q
          ◅◅ (bwd `⅋-comm ◅ ε)
          ◅◅ (step `switch ◅ ε)
          ◅◅ `⊗⟩⋆ (bwd `⅋-comm ◅ ε)
          ◅◅ `⊗⟩⋆ (ϕ {Q} (lift ε)) .lower
          ◅◅ (fwd `⊗-identityʳ ◅ ε)

interact-！ : ∀ P → (L.！ (L.η P L.⊸ L.ε) L.⅋ L.η (`! P)) L.≤ L.ε
interact-！ P .L.*≤* {P'} (Q , R , P'⟶⋆QR , (Q' , Q≤?Q' , ϕ) , lift R≤!P) =
  lift P'⟶⋆I
  where
    P'⟶⋆I : P' ⟶⋆ `I
    P'⟶⋆I = P'⟶⋆QR
         ◅◅ (Q≤?Q' `⟨⅋⋆)
         ◅◅ (`⅋⟩⋆ R≤!P)
         ◅◅ (fwd `⅋-comm ◅ ε)
         ◅◅ (step `p ◅ ε)
         ◅◅ (`!⟩⋆ (fwd `⅋-comm ◅ ε))
         ◅◅ (`!⟩⋆ (ϕ {P} (lift ε) .lower))
         ◅◅ step `e ◅ ε

mutual
  reflect : ∀ P → L.η P L.≤ ⟦ P ⟧ .neg
  reflect `I =
    L.≤-refl
  reflect (P `◁ Q) =
    L.≤-trans L.η-preserve-◁ (L.◁-mono (reflect P) (reflect Q))
  reflect (`+ A) =
    L.⊸-residual-to (L.≤-trans L.η-preserve-⅋⁻¹ (L.η-mono ((step `axiom) ◅ ε)))
  reflect (`- A) =
    L.≤-refl
  reflect (`? P) =
    L.≤-trans L.η-preserve-！ (L.！-mono (reflect P))
  reflect (`! P) =
    L.⊸-residual-to (L.≤-trans (L.⅋-mono (L.！-mono (reify P)) L.≤-refl) (interact-！ P))
  reflect (P `⅋ Q) =
    L.≤-trans L.η-preserve-⅋ (L.⅋-mono (reflect P) (reflect Q))
  reflect (P `⊗ Q) =
    L.⟨ L.⊸-residual-to (L.≤-trans (L.⅋-mono (reify Q) L.≤-refl) (L.≤-trans (interact P Q) (reflect P)))
      , L.⊸-residual-to (L.≤-trans (L.⅋-mono (reify P) (L.η-mono (fwd `⊗-comm ◅ ε))) (L.≤-trans (interact Q P) (reflect Q))) ⟩

  reify : ∀ P → ⟦ P ⟧ .pos L.≤ L.η P L.⊸ L.ι
  reify P =
    L.⊸-residual-to
      (L.≤-trans (L.⅋-comm _ _ .proj₁)
        (L.≤-trans (L.⅋-mono L.≤-refl (reflect P))
          (L.≤-trans (⟦ P ⟧ .int) L.ε≤ι)))

  reify′ : ∀ P → ⟦ P ⟧ .pos L.≤ L.η P L.⊸ L.ε
  reify′ P =
    L.⊸-residual-to
      (L.≤-trans (L.⅋-comm _ _ .proj₁)
        (L.≤-trans (L.⅋-mono L.≤-refl (reflect P)) (⟦ P ⟧ .int)))

main-lemma : ∀ P → ⟦ P ⟧ ≤ C.¬ (embed P)
main-lemma P .fpos = reify′ P
main-lemma P .fneg = reflect P

sem-cut-elim : ∀ P → C.ε ≤ ⟦ P ⟧ → P ⟶⋆ `I
sem-cut-elim P I≤P = q .L.*≤* (lift ε) .lower
  where p : C.ε ≤ C.¬ (embed P)
        p = C.≤-trans I≤P (main-lemma P)
        q : L.η P L.≤ L.ι
        q = L.≤-trans (p .fneg) L.ε≤ι

cut-elim : (P : Formula) → (P SNEL.⟶⋆ `I) → P ⟶⋆ `I
cut-elim P prf = sem-cut-elim P ⟦ prf ⟧steps
