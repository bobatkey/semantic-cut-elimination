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
  using (embedDual; Chu; module S; tidyup; ⟦I⟧; _==>_)
  renaming (model to analyticModel)

open import MAV.Interpretation Atom analyticModel
  (λ A → embedDual (`- A) (`+ A) (step `axiom ◅ ε))

open Chu
open S.Ideal
open S._≤ⁱ_

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

cut-elim : (P : Formula) → (P SMAV.⟶⋆ `I) → P ⟶⋆ `I
cut-elim P prf = sem-cut-elim P ⟦ prf ⟧steps
