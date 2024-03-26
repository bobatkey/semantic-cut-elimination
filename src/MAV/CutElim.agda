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
open S.Sheaf
open S._≤ˢ_

mutual
  okada : ∀ P → ⟦ P ⟧ .neg .ICarrier P
  okada `I = S.leaf (`I , lift ε) , ε
  okada (`+ A) = S.leaf (`+ A , lift ε) , ε
  okada (`- A) = S.leaf (`- A , lift ε) , ε
  okada (P `⅋ Q) = S.leaf (P `⅋ Q , P , Q , ε , okada P , okada Q) , ε
  okada (P `⊗ Q) .proj₁ {R} x =
    ⟦ P ⟧ .neg .≤-closed
      (step `switch ◅ (P `⊗⟩⋆ (eq-fwd (`⅋-comm _ _) ◅ okada⁺ Q R x) ◅◅ eq-fwd (`⊗-identityʳ _) ◅ ε))
      (okada P)
  okada (P `⊗ Q) .proj₂ {R} x =
    ⟦ Q ⟧ .neg .≤-closed
      (eq-fwd (`⊗-comm _ _) `⟨⅋ R ◅ step `switch ◅ Q `⊗⟩ eq-fwd (`⅋-comm _ _) ◅ Q `⊗⟩⋆ okada⁺ P R x ◅◅ eq-fwd (`⊗-identityʳ _) ◅ ε)
      (okada Q)
  okada (P `& Q) =
    S.node (S.leaf (P , inj₁ (okada P))) (S.leaf (Q , inj₂ (okada Q))) , ε
  okada (P `⊕ Q) =
    ⟦ P ⟧ .neg .≤-closed (step `left ◅ ε) (okada P) ,
    ⟦ Q ⟧ .neg .≤-closed (step `right ◅ ε) (okada Q)
  okada (P `◁ Q) =
    P , Q , ε , okada P , okada Q

  okada⁺ : ∀ P R → ⟦ P ⟧ .pos .ICarrier R → (R `⅋ P) MAV.⟶⋆ `I
  okada⁺ P R ϕ =
    tidyup (⟦ P ⟧ .int .*≤ˢ* {R `⅋ P} (S.leaf (R `⅋ P , R , P , ε , ϕ , okada P) , ε))

-- if 'P′ is provable, then it has a cut-free proof
sem-cut-elim : ∀ P → ⟦I⟧ ==> ⟦ P ⟧ → P ⟶⋆ `I
sem-cut-elim P prf = tidyup (prf ._==>_.fneg .*≤ˢ* {P} (okada P))

cut-elim : (P : Formula) → (P SMAV.⟶⋆ `I) → P ⟶⋆ `I
cut-elim P prf = sem-cut-elim P ⟦ prf ⟧steps
