{-# OPTIONS --postfix-projections --safe --without-K #-}

module MAV.CutElimination (Atom : Set) where

open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (0ℓ; lift; lower; Lift; suc)
open import Prelude
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)
import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties as Star

open import MAV.Formula Atom

private
  variable
    A A′ : Atom
    P P′ : Formula
    Q Q′ : Formula
    R R′ : Formula
    S S′ : Formula

infix 5 _⟶_

-- One step of the “analytic” proof system
data _⟶_ : Formula → Formula → Set where
  `axiom    : `+ A `⅋ `- A ⟶ `I

  `tidy     : `I `& `I ⟶ `I
  `switch   : (P `⊗ Q) `⅋ R ⟶ P `⊗ (Q `⅋ R)
  `sequence : (P `▷ Q) `⅋ (R `▷ S) ⟶ (P `⅋ R) `▷ (Q `⅋ S)
  `left     : P `⊕ Q ⟶ P
  `right    : P `⊕ Q ⟶ Q
  `external : (P `& Q) `⅋ R ⟶ (P `⅋ R) `& (Q `⅋ R)
  `medial   : (P `▷ Q) `& (R `▷ S) ⟶ (P `& R) `▷ (Q `& S)

  -- _`⟨⊗_      : P ⟶ P′ → (Q : Formula) → P `⊗ Q ⟶ P′ `⊗ Q
  _`⊗⟩_      : (P : Formula) → Q ⟶ Q′ → P `⊗ Q ⟶ P `⊗ Q′
  -- `⊗-assoc   : P `⊗ (Q `⊗ R) ⟶ (P `⊗ Q) `⊗ R
  -- `⊗-assoc⁻¹ : (P `⊗ Q) `⊗ R ⟶ P `⊗ (Q `⊗ R)
  `⊗-comm    : P `⊗ Q ⟶ Q `⊗ P
  `⊗-unit    : P `⊗ `I ⟶ P
  -- `⊗-unit⁻¹  : P ⟶ (P `⊗ `I)

  _`⟨⅋_      : P ⟶ P′ → (Q : Formula) → (P `⅋ Q) ⟶ (P′ `⅋ Q)
  _`⅋⟩_      : (P : Formula) → Q ⟶ Q′ → (P `⅋ Q) ⟶ (P `⅋ Q′)
  `⅋-assoc   : (P `⅋ (Q `⅋ R)) ⟶ ((P `⅋ Q) `⅋ R)
  `⅋-assoc⁻¹ : ((P `⅋ Q) `⅋ R) ⟶ (P `⅋ (Q `⅋ R))
  `⅋-comm    : (P `⅋ Q) ⟶ (Q `⅋ P)
  `⅋-unit    : (P `⅋ `I) ⟶ P
  `⅋-unit⁻¹  : P ⟶ (P `⅋ `I)

  _`⟨▷_      : P ⟶ P′ → (Q : Formula) → (P `▷ Q) ⟶ (P′ `▷ Q)
  _`▷⟩_      : (P : Formula) → Q ⟶ Q′ → (P `▷ Q) ⟶ (P `▷ Q′)
  `▷-assoc   : (P `▷ (Q `▷ R)) ⟶ ((P `▷ Q) `▷ R)
  `▷-assoc⁻¹ : ((P `▷ Q) `▷ R) ⟶ (P `▷ (Q `▷ R))
  `▷-runit   : (P `▷ `I) ⟶ P
  `▷-runit⁻¹ : P ⟶ (P `▷ `I)
  `▷-lunit   : (`I `▷ P) ⟶ P
  `▷-lunit⁻¹ : P ⟶ (`I `▷ P)

  _`⟨&_      : P ⟶ P′ → (Q : Formula) → (P `& Q) ⟶ (P′ `& Q)
  _`&⟩_      : (P : Formula) → Q ⟶ Q′ → (P `& Q) ⟶ (P `& Q′)


infix  5 _⟶*_

_⟶*_ : Formula → Formula → Set
_⟶*_ = Star _⟶_

------------------------------------------------------------------------------
-- Turning the proof system into A pre-order

⟶*-refl : ∀ {P} → P ⟶* P
⟶*-refl = ε

⟶*-trans : P ⟶* Q → Q ⟶* R → P ⟶* R
⟶*-trans ε           q⟶*R = q⟶*R
⟶*-trans (x ◅ p⟶*Q) q⟶*R = x ◅ ⟶*-trans p⟶*Q q⟶*R

⟶*-isPreorder : IsPreorder _⟶*_
⟶*-isPreorder .IsPreorder.refl = ⟶*-refl
⟶*-isPreorder .IsPreorder.trans = ⟶*-trans

-- ⅋ is A monoid in the proof system
_`⅋⟩*_ : (P : Formula) → Q ⟶* Q′ → (P `⅋ Q) ⟶* (P `⅋ Q′)
P `⅋⟩* ε = ε
P `⅋⟩* (x ◅ ϕ) = (P `⅋⟩ x) ◅ (P `⅋⟩* ϕ)

_`⟨⅋*_ : P ⟶* P′ → (Q : Formula) →  (P `⅋ Q) ⟶* (P′ `⅋ Q)
ε       `⟨⅋* Q = ε
(x ◅ ϕ) `⟨⅋* Q = (x `⟨⅋ Q) ◅ (ϕ `⟨⅋* Q)

`⅋-mono : (P ⟶* P′) → (Q ⟶* Q′) → (P `⅋ Q) ⟶* (P′ `⅋ Q′)
`⅋-mono {P = P} {Q′ = Q′} f g = ⟶*-trans (P `⅋⟩* g) (f `⟨⅋* Q′)

`⅋-isMonoid : IsMonoid ⟶*-isPreorder _`⅋_ `I
`⅋-isMonoid .IsMonoid.mono = `⅋-mono
`⅋-isMonoid .IsMonoid.assoc = `⅋-assoc⁻¹ ◅ ε , `⅋-assoc ◅ ε
`⅋-isMonoid .IsMonoid.lunit = `⅋-comm ◅ `⅋-unit ◅ ε , `⅋-unit⁻¹ ◅ `⅋-comm ◅ ε
`⅋-isMonoid .IsMonoid.runit = `⅋-unit ◅ ε , `⅋-unit⁻¹ ◅ ε

`⅋-sym : P `⅋ Q ⟶* Q `⅋ P
`⅋-sym = `⅋-comm ◅ ε

-- ▷ is A monoid in the proof system
_`▷⟩*_ : (P : Formula) → Q ⟶* Q′ → P `▷ Q ⟶* P `▷ Q′
P `▷⟩* ε = ε
P `▷⟩* (x ◅ ϕ) = (P `▷⟩ x) ◅ (P `▷⟩* ϕ)

_`⟨▷*_ : P ⟶* P′ → (Q : Formula) → P `▷ Q ⟶* P′ `▷ Q
ε       `⟨▷* Q = ε
(x ◅ ϕ) `⟨▷* Q = (x `⟨▷ Q) ◅ (ϕ `⟨▷* Q)

`▷-mono : (P ⟶* P′) → (Q ⟶* Q′) → (P `▷ Q) ⟶* (P′ `▷ Q′)
`▷-mono {P = P} {Q′ = Q′} f g = ⟶*-trans (P `▷⟩* g) (f `⟨▷* Q′)

`▷-isMonoid : IsMonoid ⟶*-isPreorder _`▷_ `I
`▷-isMonoid .IsMonoid.mono = `▷-mono
`▷-isMonoid .IsMonoid.assoc = `▷-assoc⁻¹ ◅ ε , `▷-assoc ◅ ε
`▷-isMonoid .IsMonoid.lunit = `▷-lunit ◅ ε , `▷-lunit⁻¹ ◅ ε
`▷-isMonoid .IsMonoid.runit = `▷-runit ◅ ε , `▷-runit⁻¹ ◅ ε

⅋-`▷-isDuoidal : IsDuoidal ⟶*-isPreorder `⅋-isMonoid `▷-isMonoid
⅋-`▷-isDuoidal .IsDuoidal.exchange = `sequence ◅ ε
⅋-`▷-isDuoidal .IsDuoidal.mu = `⅋-unit ◅ ε

-- & is A monotone operator
_`&⟩*_ : (P : Formula) → Q ⟶* Q′ → P `& Q ⟶* P `& Q′
P `&⟩* ε = ε
P `&⟩* (x ◅ ϕ) = (P `&⟩ x) ◅ (P `&⟩* ϕ)

_`⟨&*_ : P ⟶* P′ → (Q : Formula) → (P `& Q) ⟶* (P′ `& Q)
ε       `⟨&* Q = ε
(x ◅ ϕ) `⟨&* Q = (x `⟨& Q) ◅ (ϕ `⟨&* Q)

`&-mono : P ⟶* P′ → Q ⟶* Q′ → P `& Q ⟶* P′ `& Q′
`&-mono {P = P} {Q′ = Q′} f g = ⟶*-trans (P `&⟩* g) (f `⟨&* Q′)

-- _⊗_ is A monotone operator
_`⊗⟩*_ : (P : Formula) → Q ⟶* Q′ → (P `⊗ Q) ⟶* (P `⊗ Q′)
P `⊗⟩* ε = ε
P `⊗⟩* (x ◅ ϕ) = (P `⊗⟩ x) ◅ (P `⊗⟩* ϕ)

-- _`⟨⊗*_ : P ⟶* P′ → (Q : Formula) → (P `⊗ Q) ⟶* (P′ `⊗ Q)
-- ε       `⟨⊗* Q = ε
-- (x ◅ ϕ) `⟨⊗* Q = (x `⟨⊗ Q) ◅ (ϕ `⟨⊗* Q)






------------------------------------------------------------------------------
-- Construct the syntactic model from presheaves and chu. We can turn
-- MAV into A *-autonomous category with finite products and
-- coproducts in such A way that we can deduce cut-elimination is
-- admissible.

import PreSheaf
import Chu
module P = PreSheaf ⟶*-isPreorder
module M = P.Monoid `⅋-isMonoid
module S = P.Sheaf _`&_ `&-mono
module MS = S.SMonoid2 `⅋-isMonoid `⅋-sym (`external ◅ ε)
module M▷ = S.SMonoid1 `▷-isMonoid (`medial ◅ ε) (`tidy ◅ ε)
module D = S.SDuoidal `⅋-isMonoid `⅋-sym (`external ◅ ε) `▷-isMonoid (`medial ◅ ε) (`tidy ◅ ε) ⅋-`▷-isDuoidal

open S._≤S_
open S.Sheaf

-- The units of the two monoids are equal (thanks to the tidy rule)
units-iso : MS.I S.≃S M▷.I
units-iso .proj₁ .*≤S* x (t , x≤t) = M▷.I .S≤-closed x≤t (M▷.I .Sclosed t)
units-iso .proj₂ .*≤S* x x≤I = S.lf (x , x≤I) , ε

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

open import MAV.Base Atom
    using (Model; module Interpretation; test; test-id)
    renaming (_⟶*_ to _s⟶*_)

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

ChuModel : Model (suc (suc 0ℓ)) 0ℓ
ChuModel .Model.Carrier = Chu
ChuModel .Model._≤_ = _==>_
ChuModel .Model.¬_ = ⟦¬⟧
ChuModel .Model.I = ⟦I⟧
ChuModel .Model.J = J
ChuModel .Model._⊗_ = _⟦⊗⟧_
ChuModel .Model._▷_ = _⍮_
ChuModel .Model._&_ = _⟦&⟧_
ChuModel .Model.≤-isPreorder = ==>-isPreorder
ChuModel .Model.⊗-isMonoid = ⊗-isMonoid
ChuModel .Model.⊗-sym = ⊗-sym
ChuModel .Model.⊗-*aut = ⊗-isStarAutonomous
ChuModel .Model.mix = Chu-mix
ChuModel .Model.&-isMeet = &-isMeet
ChuModel .Model.▷-isMonoid = ⍮-isMonoid
ChuModel .Model.I-eq-J = I-eq-J
ChuModel .Model.▷-self-dual = self-dual
ChuModel .Model.⊗-▷-isDuoidal = ⊗-⍮-isDuoidal

_>>>_ = ⟶*-trans

-- The atom interaction law in PreSheaves
atom-int : ∀ A → (P.η (`- A) M.• P.η (`+ A)) P.≤P P.η `I
atom-int A .*≤P* P (p₁ , p₂ , p≤p₁p₂ , lift p₁≤a , lift p₂≤-A) .lower =
   p≤p₁p₂ >>> (`⅋-mono p₁≤a p₂≤-A >>> (`⅋-comm ◅ `axiom ◅ ε))

atom : Atom → Chu
atom A .pos = S.α (P.η (`- A))
atom A .neg = S.α (P.η (`+ A))
atom A .int = S.≤S-trans (MS.α-monoidal .proj₁) (S.α-mono (atom-int A))

open Interpretation ChuModel atom

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

cut-elim : (P : Formula) → (P s⟶* `I) → P ⟶* `I
cut-elim P prf = sem-cut-elim P ⟦ prf ⟧steps


-- An example:
--
--  Normalising A proof that (`I `⊕ `I) `▷ (`I `& `I) ⊸ (`I `⊕ `I) `▷ (`I `& `I):

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

normalised-proof : (test `⅋ `¬ test) ⟶* `I
normalised-proof = `⅋-comm ◅
                   `⅋-comm ◅
                   `⅋-comm ◅
                   `sequence ◅
                   (`⅋-comm `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
                   (`⅋-comm `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
                   (`external `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
                   (((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-comm) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
                   (((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-comm) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
                   (((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-comm) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
                   (((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-unit) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
                   (((`I `⅋ (`I `⊕ `I)) `&⟩ `right) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
                   ((`⅋-comm `⟨& `I) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
                   ((`⅋-comm `⟨& `I) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
                   ((`⅋-comm `⟨& `I) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
                   ((`⅋-unit `⟨& `I) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
                   ((`left `⟨& `I) `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
                   (`tidy `⟨▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ◅
                   `▷-lunit ◅
                   `⅋-comm ◅
                   `external ◅
                   ((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-comm) ◅
                   ((`I `⅋ (`I `⊕ `I)) `&⟩ (`right `⟨⅋ `I)) ◅
                   ((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-comm) ◅
                   ((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-unit) ◅
                   (`⅋-comm `⟨& `I) ◅
                   ((`left `⟨⅋ `I) `⟨& `I) ◅
                   (`⅋-comm `⟨& `I) ◅ (`⅋-unit `⟨& `I) ◅ `tidy ◅ ε

test-norm : cut-elim _ test-id ≡ normalised-proof
test-norm = refl
 