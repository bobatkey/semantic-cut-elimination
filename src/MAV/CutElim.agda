{-# OPTIONS --postfix-projections --safe --without-K #-}

module MAV.CutElim (Atom : Set) where

open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (0ℓ; lift; lower; Lift; suc)
open import Prelude
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties as Star

open import MAV.Formula Atom
open import MAV.Base Atom as MAV
import MAV.Symmetric Atom as SMAV

private
  variable
    A A′ : Atom
    P P′ : Formula
    Q Q′ : Formula
    R R′ : Formula
    S S′ : Formula

------------------------------------------------------------------------------
-- Construct the syntactic model from presheaves and chu. We can turn
-- MAV into A *-autonomous category with finite products and
-- coproducts in such A way that we can deduce cut-elimination is
-- admissible.

import Algebra.PreSheaf
import Algebra.Sheaf
import Algebra.Chu

module P = Algebra.PreSheaf MAV.⟶*-Poset
module M = P.LiftIsCommutativePomonoid `⅋-isCommutativePomonoid
module S = Algebra.Sheaf `&-Pomagma
module MS = S.LiftIsCommutativePomonoid `⅋-isCommutativePomonoid {!!}
module M▷ = S.LiftIsPomonoid `▷-isPomonoid (λ w x y z → `medial ◅ ε) (`tidy ◅ ε)
module D = S.LiftIsDuoidal `⅋-`▷-isDuoidal
                           (λ x y → `⅋-comm ◅ ε , `⅋-comm ◅ ε)
                           {!!}
                           (λ w x y z → `medial ◅ ε)
                           (`tidy ◅ ε)

open S._≤ˢ_
open S.Sheaf

-- The units of the two monoids are equal (thanks to the tidy rule)
units-iso : MS.εˢ S.≈ˢ M▷.ιˢ
units-iso .proj₁ .*≤ˢ* {x} (t , x≤t) = M▷.ιˢ .≤-closed x≤t (M▷.ιˢ .∨-closed t)
units-iso .proj₂ .*≤ˢ* {x} x≤I = S.leaf (x , x≤I) , ε

{-
module CC = Chu.Construction
    S.≤S-isPreorder
    MS.⊗-isMonoid MS.⊗-sym MS.⊸-isClosure
    S.∧S-isMeet S.∨S-isJoin
    MS.I
    renaming (_⊗_ to _⟦⊗⟧_;
              _⅋_ to _⟦⅋⟧_;
              _&_ to _⟦&⟧_;
              _⊕_ to _⟦⊕⟧_;
              I to ⟦I⟧;
              ¬ to ⟦¬⟧) hiding (⅋-mono; ⅋-sym)

open CC
open CC.Chu
open CC.SelfDual M▷.▷-isMonoid
        (S.≤S-trans (M▷.▷-mono (D.units-iso .proj₁) S.≤S-refl) (M▷.▷-lunit .proj₁))
        (D.units-iso .proj₂)
        D.⊗-▷-isDuoidal
open P._≤P_

Chu-mix : ⟦I⟧ ≅ ⟦¬⟧ ⟦I⟧
Chu-mix .proj₁ .Chu.Construction._==>_.fpos = S.≤S-refl
Chu-mix .proj₁ .Chu.Construction._==>_.fneg = S.≤S-refl
Chu-mix .proj₂ .Chu.Construction._==>_.fpos = S.≤S-refl
Chu-mix .proj₂ .Chu.Construction._==>_.fneg = S.≤S-refl

I-eq-J : ⟦I⟧ ≅ J
I-eq-J .proj₁ .Chu.Construction._==>_.fpos = units-iso .proj₁
I-eq-J .proj₁ .Chu.Construction._==>_.fneg = units-iso .proj₂
I-eq-J .proj₂ .Chu.Construction._==>_.fpos = units-iso .proj₂
I-eq-J .proj₂ .Chu.Construction._==>_.fneg = units-iso .proj₁

ChuModel : SMAV.Model (suc (suc 0ℓ)) 0ℓ
ChuModel .SMAV.Model.Carrier = Chu
ChuModel .SMAV.Model._≤_ = _==>_
ChuModel .SMAV.Model.¬_ = ⟦¬⟧
ChuModel .SMAV.Model.I = ⟦I⟧
ChuModel .SMAV.Model.J = J
ChuModel .SMAV.Model._⊗_ = _⟦⊗⟧_
ChuModel .SMAV.Model._▷_ = _⍮_
ChuModel .SMAV.Model._&_ = _⟦&⟧_
ChuModel .SMAV.Model.≤-isPreorder = ==>-isPreorder
ChuModel .SMAV.Model.⊗-isMonoid = ⊗-isMonoid
ChuModel .SMAV.Model.⊗-sym = ⊗-sym
ChuModel .SMAV.Model.⊗-*aut = ⊗-isStarAutonomous
ChuModel .SMAV.Model.mix = Chu-mix
ChuModel .SMAV.Model.&-isMeet = &-isMeet
ChuModel .SMAV.Model.▷-isMonoid = ⍮-isMonoid
ChuModel .SMAV.Model.I-eq-J = I-eq-J
ChuModel .SMAV.Model.▷-self-dual = self-dual
ChuModel .SMAV.Model.⊗-▷-isDuoidal = ⊗-⍮-isDuoidal

_>>>_ = ⟶*-trans

-- The atom interaction law in PreSheaves
atom-int : ∀ A → (P.η (`- A) M.• P.η (`+ A)) P.≤P P.η `I
atom-int A .*≤P* P (p₁ , p₂ , p≤p₁p₂ , lift p₁≤a , lift p₂≤-A) .lower =
   p≤p₁p₂ >>> (`⅋-mono p₁≤a p₂≤-A >>> (`⅋-comm ◅ `axiom ◅ ε))

atom : Atom → Chu
atom A .pos = S.α (P.η (`- A))
atom A .neg = S.α (P.η (`+ A))
atom A .int = S.≤S-trans (MS.α-monoidal .proj₁) (S.α-mono (atom-int A))

open SMAV.Interpretation ChuModel atom

tidyup-lem : (t : S.Tree (Σ[ P ∈ Formula ] (Lift 0ℓ (P ⟶* `I)))) →
             S.join t ⟶* `I
tidyup-lem (S.lf (P , lift p⟶*I)) = p⟶*I
tidyup-lem (S.br S t) = `&-mono (tidyup-lem S) (tidyup-lem t) >>> (`tidy ◅ ε)

tidyup : ∀ {P} → MS.I .SCarrier P → P ⟶* `I
tidyup (t , p⟶*t) = p⟶*t >>> tidyup-lem t

mutual
  okada : ∀ P → ⟦ P ⟧ .neg .SCarrier P
  okada `I = S.lf (`I , lift ε) , ε
  okada (`+ A) = S.lf (`+ A , lift ε) , ε
  okada (`- A) = S.lf (`- A , lift ε) , ε
  okada (P `⅋ Q) = S.lf (P `⅋ Q , P , Q , ε , okada P , okada Q) , ε
  okada (P `⊗ Q) .proj₁ R x =
    ⟦ P ⟧ .neg .S≤-closed
      ((`switch ◅ ε) >>> ((P `⊗⟩* (`⅋-sym >>> okada2 Q R x)) >>> (`⊗-unit ◅ ε)))
      (okada P)
  okada (P `⊗ Q) .proj₂ R x =
    ⟦ Q ⟧ .neg .S≤-closed
      ((`⊗-comm `⟨⅋ R ◅ `switch ◅ ε) >>> ((Q `⊗⟩* (`⅋-sym >>> okada2 P R x)) >>> (`⊗-unit ◅ ε)))
      (okada Q)
  okada (P `& Q) =
    S.br (S.lf (P , inj₁ (okada P))) (S.lf (Q , inj₂ (okada Q))) , ε
  okada (P `⊕ Q) =
    ⟦ P ⟧ .neg .S≤-closed (`left ◅ ε) (okada P) ,
    ⟦ Q ⟧ .neg .S≤-closed (`right ◅ ε) (okada Q)
  okada (P `▷ Q) =
    P , Q , ε , okada P , okada Q

  okada2 : ∀ P R → ⟦ P ⟧ .pos .SCarrier R → (R `⅋ P) ⟶* `I
  okada2 P R ϕ =
    tidyup (⟦ P ⟧ .int .*≤S* (R `⅋ P) (S.lf (R `⅋ P , R , P , ε , ϕ , okada P) , ε))

-- if 'P′ is provable, then it has A cut-free proof
sem-cut-elim : ∀ P → ⟦I⟧ ==> ⟦ P ⟧ → P ⟶* `I
sem-cut-elim P prf = tidyup (prf ._==>_.fneg .*≤S* P (okada P))

cut-elim : (P : Formula) → (P SMAV.⟶* `I) → P ⟶* `I
cut-elim P prf = sem-cut-elim P ⟦ prf ⟧steps
-}
