{-# OPTIONS --postfix-projections --safe --without-K #-}

module MAV.CutElim (Atom : Set) where

open import Level using (0ℓ; lift; lower; Lift; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_; _◅◅_)

open import MAV.Formula Atom
open import MAV.Base Atom as MAV
import MAV.Symmetric Atom as SMAV
import MAV.Frame

open MAV.Frame.FrameModel MAV.frame
  using (embedDual; Chu; module S; tidyup; ⟦I⟧; _==>_)
  renaming (model to analyticModel)

open import MAV.Interpretation Atom analyticModel
  (λ a → embedDual (`- a) (`+ a) (`⅋-comm ◅ `axiom ◅ ε))

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
      (`switch⋆ ◅◅ (P `⊗⟩⋆ (`⅋-comm ◅ okada2 Q R x) ◅◅ `⊗-unit ◅ ε))
      (okada P)
  okada (P `⊗ Q) .proj₂ {R} x =
    ⟦ Q ⟧ .neg .≤-closed
      (`⊗-comm `⟨⅋ R ◅ `switch⋆ ◅◅ Q `⊗⟩⋆ (`⅋-comm ◅ okada2 P R x) ◅◅ `⊗-unit ◅ ε)
      (okada Q)
  okada (P `& Q) =
    S.node (S.leaf (P , inj₁ (okada P))) (S.leaf (Q , inj₂ (okada Q))) , ε
  okada (P `⊕ Q) =
    ⟦ P ⟧ .neg .≤-closed (`left ◅ ε) (okada P) ,
    ⟦ Q ⟧ .neg .≤-closed (`right ◅ ε) (okada Q)
  okada (P `▷ Q) =
    P , Q , ε , okada P , okada Q

  okada2 : ∀ P R → ⟦ P ⟧ .pos .ICarrier R → (R `⅋ P) MAV.⟶⋆ `I
  okada2 P R ϕ =
    tidyup (⟦ P ⟧ .int .*≤ˢ* {R `⅋ P} (S.leaf (R `⅋ P , R , P , ε , ϕ , okada P) , ε))

-- if 'P′ is provable, then it has a cut-free proof
sem-cut-elim : ∀ P → ⟦I⟧ ==> ⟦ P ⟧ → P ⟶⋆ `I
sem-cut-elim P prf = tidyup (prf ._==>_.fneg .*≤ˢ* {P} (okada P))

cut-elim : (P : Formula) → (P SMAV.⟶⋆ `I) → P ⟶⋆ `I
cut-elim P prf = sem-cut-elim P ⟦ prf ⟧steps
