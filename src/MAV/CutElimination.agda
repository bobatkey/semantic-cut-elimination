{-# OPTIONS --postfix-projections --safe --without-K #-}

module MAV.CutElimination (At : Set) where

open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (0ℓ; lift; lower; Lift; suc)
open import Prelude

open import MAV.Formula At

private
  variable
    a a′ a₁ a₂ : At
    p p′ p₁ p₂ : Formula
    q q′ q₁ q₂ : Formula
    r r′ r₁ r₂ : Formula
    s s′ s₁ s₂ : Formula

infix 5 _⟶_

-- One step of the “analytic” proof system
data _⟶_ : Formula → Formula → Set where
  `axiom    : `+ a `⅋ `- a ⟶ `I

  `tidy     : `I `& `I ⟶ `I
  `switch   : (p `⊗ q) `⅋ r ⟶ p `⊗ (q `⅋ r)
  `sequence : (p `▷ q) `⅋ (r `▷ s) ⟶ (p `⅋ r) `▷ (q `⅋ s)
  `left     : p `⊕ q ⟶ p
  `right    : p `⊕ q ⟶ q
  `external : (p `& q) `⅋ r ⟶ (p `⅋ r) `& (q `⅋ r)
  `medial   : (p `▷ q) `& (r `▷ s) ⟶ (p `& r) `▷ (q `& s)

  -- _⟨`⊗_      : p ⟶ p′ → (q : Formula) → p `⊗ q ⟶ p′ `⊗ q
  _`⊗⟩_      : (p : Formula) → q ⟶ q′ → p `⊗ q ⟶ p `⊗ q′
  -- `⊗-assoc   : p `⊗ (q `⊗ r) ⟶ (p `⊗ q) `⊗ r
  -- `⊗-assoc⁻¹ : (p `⊗ q) `⊗ r ⟶ p `⊗ (q `⊗ r)
  `⊗-comm    : p `⊗ q ⟶ q `⊗ p
  `⊗-unit    : p `⊗ `I ⟶ p
  -- `⊗-unit⁻¹  : p ⟶ (p `⊗ `I)

  _⟨`⅋_      : p ⟶ p′ → (q : Formula) → (p `⅋ q) ⟶ (p′ `⅋ q)
  _`⅋⟩_      : (p : Formula) → q ⟶ q′ → (p `⅋ q) ⟶ (p `⅋ q′)
  `⅋-assoc   : (p `⅋ (q `⅋ r)) ⟶ ((p `⅋ q) `⅋ r)
  `⅋-assoc⁻¹ : ((p `⅋ q) `⅋ r) ⟶ (p `⅋ (q `⅋ r))
  `⅋-comm    : (p `⅋ q) ⟶ (q `⅋ p)
  `⅋-unit    : (p `⅋ `I) ⟶ p
  `⅋-unit⁻¹  : p ⟶ (p `⅋ `I)

  _⟨`▷_      : p ⟶ p′ → (q : Formula) → (p `▷ q) ⟶ (p′ `▷ q)
  _`▷⟩_      : (p : Formula) → q ⟶ q′ → (p `▷ q) ⟶ (p `▷ q′)
  `▷-assoc   : (p `▷ (q `▷ r)) ⟶ ((p `▷ q) `▷ r)
  `▷-assoc⁻¹ : ((p `▷ q) `▷ r) ⟶ (p `▷ (q `▷ r))
  `▷-runit   : (p `▷ `I) ⟶ p
  `▷-runit⁻¹ : p ⟶ (p `▷ `I)
  `▷-lunit   : (`I `▷ p) ⟶ p
  `▷-lunit⁻¹ : p ⟶ (`I `▷ p)

  _⟨`&_      : p ⟶ p′ → (q : Formula) → (p `& q) ⟶ (p′ `& q)
  _`&⟩_      : (p : Formula) → q ⟶ q′ → (p `& q) ⟶ (p `& q′)


infix  5 _⟶*_
infixr 6 _∷_

data _⟶*_ : Formula → Formula → Set where
  ε : ∀ {p} → p ⟶* p
  _∷_ : p ⟶ q → q ⟶* r → p ⟶* r

------------------------------------------------------------------------------
-- Turning the proof system into a pre-order

⟶*-refl : ∀ {p} → p ⟶* p
⟶*-refl = ε

⟶*-trans : p ⟶* q → q ⟶* r → p ⟶* r
⟶*-trans ε           q⟶*r = q⟶*r
⟶*-trans (x ∷ p⟶*q) q⟶*r = x ∷ ⟶*-trans p⟶*q q⟶*r

⟶*-isPreorder : IsPreorder _⟶*_
⟶*-isPreorder .IsPreorder.refl = ⟶*-refl
⟶*-isPreorder .IsPreorder.trans = ⟶*-trans

-- ⅋ is a monoid in the proof system
_`⅋⟩*_ : (p : Formula) → q₁ ⟶* q₂ → (p `⅋ q₁) ⟶* (p `⅋ q₂)
p `⅋⟩* ε = ε
p `⅋⟩* (x ∷ ϕ) = (p `⅋⟩ x) ∷ (p `⅋⟩* ϕ)

_⟨`⅋*_ : p ⟶* p′ → (q : Formula) →  (p `⅋ q) ⟶* (p′ `⅋ q)
ε       ⟨`⅋* q = ε
(x ∷ ϕ) ⟨`⅋* q = (x ⟨`⅋ q) ∷ (ϕ ⟨`⅋* q)

`⅋-mono : (p ⟶* p′) → (q ⟶* q′) → (p `⅋ q) ⟶* (p′ `⅋ q′)
`⅋-mono {p = p} {q′ = q′} f g = ⟶*-trans (p `⅋⟩* g) (f ⟨`⅋* q′)

`⅋-isMonoid : IsMonoid ⟶*-isPreorder _`⅋_ `I
`⅋-isMonoid .IsMonoid.mono = `⅋-mono
`⅋-isMonoid .IsMonoid.assoc = `⅋-assoc⁻¹ ∷ ε , `⅋-assoc ∷ ε
`⅋-isMonoid .IsMonoid.lunit = `⅋-comm ∷ `⅋-unit ∷ ε , `⅋-unit⁻¹ ∷ `⅋-comm ∷ ε
`⅋-isMonoid .IsMonoid.runit = `⅋-unit ∷ ε , `⅋-unit⁻¹ ∷ ε

`⅋-sym : p `⅋ q ⟶* q `⅋ p
`⅋-sym = `⅋-comm ∷ ε

-- ▷ is a monoid in the proof system
_`▷⟩*_ : (p : Formula) → q₁ ⟶* q₂ → p `▷ q₁ ⟶* p `▷ q₂
p `▷⟩* ε = ε
p `▷⟩* (x ∷ ϕ) = (p `▷⟩ x) ∷ (p `▷⟩* ϕ)

_⟨`▷*_ : p ⟶* p′ → (q : Formula) → p `▷ q ⟶* p′ `▷ q
ε       ⟨`▷* q = ε
(x ∷ ϕ) ⟨`▷* q = (x ⟨`▷ q) ∷ (ϕ ⟨`▷* q)

`▷-mono : (p ⟶* p′) → (q ⟶* q′) → (p `▷ q) ⟶* (p′ `▷ q′)
`▷-mono {p = p} {q′ = q′} f g = ⟶*-trans (p `▷⟩* g) (f ⟨`▷* q′)

`▷-isMonoid : IsMonoid ⟶*-isPreorder _`▷_ `I
`▷-isMonoid .IsMonoid.mono = `▷-mono
`▷-isMonoid .IsMonoid.assoc = `▷-assoc⁻¹ ∷ ε , `▷-assoc ∷ ε
`▷-isMonoid .IsMonoid.lunit = `▷-lunit ∷ ε , `▷-lunit⁻¹ ∷ ε
`▷-isMonoid .IsMonoid.runit = `▷-runit ∷ ε , `▷-runit⁻¹ ∷ ε

⅋-`▷-isDuoidal : IsDuoidal ⟶*-isPreorder `⅋-isMonoid `▷-isMonoid
⅋-`▷-isDuoidal .IsDuoidal.exchange = `sequence ∷ ε
⅋-`▷-isDuoidal .IsDuoidal.mu = `⅋-unit ∷ ε

-- & is a monotone operator
_`&⟩*_ : (p : Formula) → q ⟶* q′ → p `& q ⟶* p `& q′
p `&⟩* ε = ε
p `&⟩* (x ∷ ϕ) = (p `&⟩ x) ∷ (p `&⟩* ϕ)

_⟨`&*_ : p ⟶* p′ → (q : Formula) → (p `& q) ⟶* (p′ `& q)
ε       ⟨`&* q = ε
(x ∷ ϕ) ⟨`&* q = (x ⟨`& q) ∷ (ϕ ⟨`&* q)

`&-mono : p ⟶* p′ → q ⟶* q′ → p `& q ⟶* p′ `& q′
`&-mono {p = p} {q′ = q′} f g = ⟶*-trans (p `&⟩* g) (f ⟨`&* q′)

-- _⊗_ is a monotone operator
_`⊗⟩*_ : (p : Formula) → q ⟶* q′ → (p `⊗ q) ⟶* (p `⊗ q′)
p `⊗⟩* ε = ε
p `⊗⟩* (x ∷ ϕ) = (p `⊗⟩ x) ∷ (p `⊗⟩* ϕ)

-- _⟨`⊗*_ : p ⟶* p′ → (q : Formula) → (p `⊗ q) ⟶* (p′ `⊗ q)
-- ε       ⟨`⊗* q = ε
-- (x ∷ ϕ) ⟨`⊗* q = (x `⟨⊗ q) ∷ (ϕ ⟨`⊗* q)






------------------------------------------------------------------------------
-- Construct the syntactic model from presheaves and chu. We can turn
-- MAV into a *-autonomous category with finite products and
-- coproducts in such a way that we can deduce cut-elimination is
-- admissible.

import PreSheaf
import Chu
module P = PreSheaf ⟶*-isPreorder
module M = P.Monoid `⅋-isMonoid
module S = P.Sheaf _`&_ `&-mono
module MS = S.SMonoid2 `⅋-isMonoid `⅋-sym (`external ∷ ε)
module M▷ = S.SMonoid1 `▷-isMonoid (`medial ∷ ε) (`tidy ∷ ε)
module D = S.SDuoidal `⅋-isMonoid `⅋-sym (`external ∷ ε) `▷-isMonoid (`medial ∷ ε) (`tidy ∷ ε) ⅋-`▷-isDuoidal

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

open import MAV.Base At
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
ChuModel .Model.¬ = ⟦¬⟧
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
atom-int : ∀ a → (P.η (`- a) M.• P.η (`+ a)) P.≤P P.η `I
atom-int a .*≤P* p (p₁ , p₂ , p≤p₁p₂ , lift p₁≤a , lift p₂≤-a) .lower =
   p≤p₁p₂ >>> (`⅋-mono p₁≤a p₂≤-a >>> (`⅋-comm ∷ `axiom ∷ ε))

atom : At → Chu
atom a .pos = S.α (P.η (`- a))
atom a .neg = S.α (P.η (`+ a))
atom a .int = S.≤S-trans (MS.α-monoidal .proj₁) (S.α-mono (atom-int a))

open Interpretation ChuModel atom

tidyup-lem : (t : S.Tree (Σ[ p ∈ Formula ] (Lift 0ℓ (p ⟶* `I)))) →
             S.join t ⟶* `I
tidyup-lem (S.lf (p , lift p⟶*I)) = p⟶*I
tidyup-lem (S.br s t) = `&-mono (tidyup-lem s) (tidyup-lem t) >>> (`tidy ∷ ε)

tidyup : ∀ {p} → MS.I .SCarrier p → p ⟶* `I
tidyup (t , p⟶*t) = p⟶*t >>> tidyup-lem t

mutual
  okada : ∀ p → ⟦ p ⟧ .neg .SCarrier p
  okada `I = S.lf (`I , lift ε) , ε
  okada (`+ a) = S.lf (`+ a , lift ε) , ε
  okada (`- a) = S.lf (`- a , lift ε) , ε
  okada (p `⅋ q) = S.lf (p `⅋ q , p , q , ε , okada p , okada q) , ε
  okada (p `⊗ q) .proj₁ r x =
    ⟦ p ⟧ .neg .S≤-closed
      ((`switch ∷ ε) >>> ((p `⊗⟩* (`⅋-sym >>> okada2 q r x)) >>> (`⊗-unit ∷ ε)))
      (okada p)
  okada (p `⊗ q) .proj₂ r x =
    ⟦ q ⟧ .neg .S≤-closed
      ((`⊗-comm ⟨`⅋ r ∷ `switch ∷ ε) >>> ((q `⊗⟩* (`⅋-sym >>> okada2 p r x)) >>> (`⊗-unit ∷ ε)))
      (okada q)
  okada (p `& q) =
    S.br (S.lf (p , inj₁ (okada p))) (S.lf (q , inj₂ (okada q))) , ε
  okada (p `⊕ q) =
    ⟦ p ⟧ .neg .S≤-closed (`left ∷ ε) (okada p) ,
    ⟦ q ⟧ .neg .S≤-closed (`right ∷ ε) (okada q)
  okada (p `▷ q) =
    p , q , ε , okada p , okada q

  okada2 : ∀ p r → ⟦ p ⟧ .pos .SCarrier r → (r `⅋ p) ⟶* `I
  okada2 p r ϕ =
    tidyup (⟦ p ⟧ .int .*≤S* (r `⅋ p) (S.lf (r `⅋ p , r , p , ε , ϕ , okada p) , ε))

-- if 'p′ is provable, then it has a cut-free proof
sem-cut-elim : ∀ p → ⟦I⟧ ==> ⟦ p ⟧ → p ⟶* `I
sem-cut-elim p prf = tidyup (prf ._==>_.fneg .*≤S* p (okada p))

cut-elim : (p : Formula) → (p s⟶* `I) → p ⟶* `I
cut-elim p prf = sem-cut-elim p ⟦ prf ⟧steps


-- An example:
--
--  Normalising a proof that (`I `⊕ `I) `▷ (`I `& `I) ⊸ (`I `⊕ `I) `▷ (`I `& `I):

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

normalised-proof : (test `⅋ `¬ test) ⟶* `I
normalised-proof = `⅋-comm ∷
                   `⅋-comm ∷
                   `⅋-comm ∷
                   `sequence ∷
                   (`⅋-comm ⟨`▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ∷
                   (`⅋-comm ⟨`▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ∷
                   (`external ⟨`▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ∷
                   (((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-comm) ⟨`▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ∷
                   (((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-comm) ⟨`▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ∷
                   (((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-comm) ⟨`▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ∷
                   (((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-unit) ⟨`▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ∷
                   (((`I `⅋ (`I `⊕ `I)) `&⟩ `right) ⟨`▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ∷
                   ((`⅋-comm ⟨`& `I) ⟨`▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ∷
                   ((`⅋-comm ⟨`& `I) ⟨`▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ∷
                   ((`⅋-comm ⟨`& `I) ⟨`▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ∷
                   ((`⅋-unit ⟨`& `I) ⟨`▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ∷
                   ((`left ⟨`& `I) ⟨`▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ∷
                   (`tidy ⟨`▷ ((`I `⊕ `I) `⅋ (`I `& `I))) ∷
                   `▷-lunit ∷
                   `⅋-comm ∷
                   `external ∷
                   ((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-comm) ∷
                   ((`I `⅋ (`I `⊕ `I)) `&⟩ (`right ⟨`⅋ `I)) ∷
                   ((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-comm) ∷
                   ((`I `⅋ (`I `⊕ `I)) `&⟩ `⅋-unit) ∷
                   (`⅋-comm ⟨`& `I) ∷
                   ((`left ⟨`⅋ `I) ⟨`& `I) ∷
                   (`⅋-comm ⟨`& `I) ∷ (`⅋-unit ⟨`& `I) ∷ `tidy ∷ ε

test-norm : cut-elim _ test-id ≡ normalised-proof
test-norm = refl
 