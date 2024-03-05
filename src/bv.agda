{-# OPTIONS --postfix-projections --safe --without-K #-}

module bv (At : Set) where

open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (0ℓ; lift; lower; Lift)
open import basics

data fmla : Set where
  I : fmla
  +at -at : At → fmla
  _⅋_ _⊗_ _&_ _⊕_ _▷_ : fmla → fmla → fmla

¬ : fmla → fmla
¬ I = I
¬ (+at a) = -at a
¬ (-at a) = +at a
¬ (p ⅋ q) = ¬ p ⊗ ¬ q
¬ (p ⊗ q) = ¬ p ⅋ ¬ q
¬ (p & q) = ¬ p ⊕ ¬ q
¬ (p ⊕ q) = ¬ p & ¬ q
¬ (p ▷ q) = ¬ p ▷ ¬ q

_⊸_ : fmla → fmla → fmla
p ⊸ q = ¬ p ⅋ q

-- One step of the proof system
data _⟶_ : fmla → fmla → Set where
  axiom    : ∀ {a} → (+at a ⅋ -at a) ⟶ I

  tidy     : (I & I) ⟶ I
  switch   : ∀ {p q r} → ((p ⊗ q) ⅋ r) ⟶ (p ⊗ (q ⅋ r))
  sequence : ∀ {p q r s} → ((p ▷ q) ⅋ (r ▷ s)) ⟶ ((p ⅋ r) ▷ (q ⅋ s))
  left     : ∀ {p q} → (p ⊕ q) ⟶ p
  right    : ∀ {p q} → (p ⊕ q) ⟶ q
  external : ∀ {p q r} → ((p & q) ⅋ r) ⟶ ((p ⅋ r) & (q ⅋ r))
  medial   : ∀ {p q r s} → ((p ▷ q) & (r ▷ s)) ⟶ ((p & r) ▷ (q & s))

  --  _⟨⊗_      : ∀ {p p'} → p ⟶ p' → (q : fmla) → (p ⊗ q) ⟶ (p' ⊗ q)
  _⊗⟩_      : ∀ {q q'} → (p : fmla) → q ⟶ q' → (p ⊗ q) ⟶ (p ⊗ q')
  -- ⊗-assoc   : ∀ {p q r} → (p ⊗ (q ⊗ r)) ⟶ ((p ⊗ q) ⊗ r)
  -- ⊗-assoc⁻¹ : ∀ {p q r} → ((p ⊗ q) ⊗ r) ⟶ (p ⊗ (q ⊗ r))
  ⊗-comm    : ∀ {p q} → (p ⊗ q) ⟶ (q ⊗ p)    -- could replace this with "switch-right"
  ⊗-unit    : ∀ {p}   → (p ⊗ I) ⟶ p
  --  ⊗-unit⁻¹  : ∀ {p}   → p ⟶ (p ⊗ I)

  _⟨⅋_      : ∀ {p p'} → p ⟶ p' → (q : fmla) → (p ⅋ q) ⟶ (p' ⅋ q)
  _⅋⟩_      : ∀ {q q'} → (p : fmla) → q ⟶ q' → (p ⅋ q) ⟶ (p ⅋ q')
  ⅋-assoc   : ∀ {p q r} → (p ⅋ (q ⅋ r)) ⟶ ((p ⅋ q) ⅋ r)
  ⅋-assoc⁻¹ : ∀ {p q r} → ((p ⅋ q) ⅋ r) ⟶ (p ⅋ (q ⅋ r))
  ⅋-comm    : ∀ {p q} → (p ⅋ q) ⟶ (q ⅋ p)
  ⅋-unit    : ∀ {p}   → (p ⅋ I) ⟶ p
  ⅋-unit⁻¹  : ∀ {p}   → p ⟶ (p ⅋ I)

  _⟨▷_      : ∀ {p p'} → p ⟶ p' → (q : fmla) → (p ▷ q) ⟶ (p' ▷ q)
  _▷⟩_      : ∀ {q q'} → (p : fmla) → q ⟶ q' → (p ▷ q) ⟶ (p ▷ q')
  ▷-assoc   : ∀ {p q r} → (p ▷ (q ▷ r)) ⟶ ((p ▷ q) ▷ r)
  ▷-assoc⁻¹ : ∀ {p q r} → ((p ▷ q) ▷ r) ⟶ (p ▷ (q ▷ r))
  ▷-runit   : ∀ {p}   → (p ▷ I) ⟶ p
  ▷-runit⁻¹ : ∀ {p}   → p ⟶ (p ▷ I)
  ▷-lunit   : ∀ {p}   → (I ▷ p) ⟶ p
  ▷-lunit⁻¹ : ∀ {p}   → p ⟶ (I ▷ p)

  _⟨&_      : ∀ {p p'} → p ⟶ p' → (q : fmla) → (p & q) ⟶ (p' & q)
  _&⟩_      : ∀ {q q'} → (p : fmla) → q ⟶ q' → (p & q) ⟶ (p & q')

  -- Not needed:
  -- _⟨⊕_      : ∀ {p p'} → p ⟶ p' → (q : fmla) → (p ⊕ q) ⟶ (p' ⊕ q)
  -- _⊕⟩_      : ∀ {q q'} → (p : fmla) → q ⟶ q' → (p ⊕ q) ⟶ (p ⊕ q')


data _⟶*_ : fmla → fmla → Set where
  ε : ∀ {p} → p ⟶* p
  _∷_ : ∀ {p q r} → p ⟶ q → q ⟶* r → p ⟶* r
infixr 6 _∷_

test1 : ((I & I) ⊸ I) ⟶* I
test1 = left ⟨⅋ I ∷ ⅋-unit ∷ ε

test2 : ((I ⊕ I) ⊸ I) ⟶* I
test2 = external ∷ (⅋-unit ⟨& (I ⅋ I)) ∷ I &⟩ ⅋-unit ∷ tidy ∷ ε

------------------------------------------------------------------------------

⟶*-refl : ∀ {p} → p ⟶* p
⟶*-refl = ε

⟶*-trans : ∀ {p q r} → p ⟶* q → q ⟶* r → p ⟶* r
⟶*-trans ε          q⟶*r = q⟶*r
⟶*-trans (x ∷ p⟶*q) q⟶*r = x ∷ ⟶*-trans p⟶*q q⟶*r

⟶*-isPreorder : IsPreorder _⟶*_
⟶*-isPreorder .IsPreorder.refl = ⟶*-refl
⟶*-isPreorder .IsPreorder.trans = ⟶*-trans

-- ⅋ is a monoid in the proof system
_⅋⟩*_ : ∀ p {q₁ q₂} → q₁ ⟶* q₂ → (p ⅋ q₁) ⟶* (p ⅋ q₂)
p ⅋⟩* ε = ε
p ⅋⟩* (x ∷ ϕ) = (p ⅋⟩ x) ∷ (p ⅋⟩* ϕ)

_⟨⅋*_ : ∀ {p₁ p₂} → p₁ ⟶* p₂ → ∀ q → (p₁ ⅋ q) ⟶* (p₂ ⅋ q)
ε ⟨⅋* q = ε
(x ∷ ϕ) ⟨⅋* q = (x ⟨⅋ q) ∷ (ϕ ⟨⅋* q)

⅋-mono : ∀ {p₁ q₁ p₂ q₂} → (p₁ ⟶* p₂) → (q₁ ⟶* q₂) → (p₁ ⅋ q₁) ⟶* (p₂ ⅋ q₂)
⅋-mono {p₁}{q₁}{p₂}{q₂} f g = ⟶*-trans (p₁ ⅋⟩* g) (f ⟨⅋* q₂)

⅋-isMonoid : IsMonoid ⟶*-isPreorder _⅋_ I
⅋-isMonoid .IsMonoid.mono = ⅋-mono
⅋-isMonoid .IsMonoid.assoc = ⅋-assoc⁻¹ ∷ ε , ⅋-assoc ∷ ε
⅋-isMonoid .IsMonoid.lunit = ⅋-comm ∷ ⅋-unit ∷ ε , ⅋-unit⁻¹ ∷ ⅋-comm ∷ ε
⅋-isMonoid .IsMonoid.runit = ⅋-unit ∷ ε , ⅋-unit⁻¹ ∷ ε

⅋-sym : ∀ {p q} → (p ⅋ q) ⟶* (q ⅋ p)
⅋-sym = ⅋-comm ∷ ε

-- ▷ is a monoid in the proof system
_▷⟩*_ : ∀ p {q₁ q₂} → q₁ ⟶* q₂ → (p ▷ q₁) ⟶* (p ▷ q₂)
p ▷⟩* ε = ε
p ▷⟩* (x ∷ ϕ) = (p ▷⟩ x) ∷ (p ▷⟩* ϕ)

_⟨▷*_ : ∀ {p₁ p₂} → p₁ ⟶* p₂ → ∀ q → (p₁ ▷ q) ⟶* (p₂ ▷ q)
ε ⟨▷* q = ε
(x ∷ ϕ) ⟨▷* q = (x ⟨▷ q) ∷ (ϕ ⟨▷* q)

▷-mono : ∀ {p₁ q₁ p₂ q₂} → (p₁ ⟶* p₂) → (q₁ ⟶* q₂) → (p₁ ▷ q₁) ⟶* (p₂ ▷ q₂)
▷-mono {p₁}{q₁}{p₂}{q₂} f g = ⟶*-trans (p₁ ▷⟩* g) (f ⟨▷* q₂)

▷-isMonoid : IsMonoid ⟶*-isPreorder _▷_ I
▷-isMonoid .IsMonoid.mono = ▷-mono
▷-isMonoid .IsMonoid.assoc = ▷-assoc⁻¹ ∷ ε , ▷-assoc ∷ ε
▷-isMonoid .IsMonoid.lunit = ▷-lunit ∷ ε , ▷-lunit⁻¹ ∷ ε
▷-isMonoid .IsMonoid.runit = ▷-runit ∷ ε , ▷-runit⁻¹ ∷ ε

⅋-▷-isDuoidal : IsDuoidal ⟶*-isPreorder ⅋-isMonoid ▷-isMonoid
⅋-▷-isDuoidal .IsDuoidal.exchange = sequence ∷ ε
⅋-▷-isDuoidal .IsDuoidal.mu = ⅋-unit ∷ ε

-- & is a monotone operator
_&⟩*_ : ∀ p {q₁ q₂} → q₁ ⟶* q₂ → (p & q₁) ⟶* (p & q₂)
p &⟩* ε = ε
p &⟩* (x ∷ ϕ) = (p &⟩ x) ∷ (p &⟩* ϕ)

_⟨&*_ : ∀ {p₁ p₂} → p₁ ⟶* p₂ → ∀ q → (p₁ & q) ⟶* (p₂ & q)
ε ⟨&* q = ε
(x ∷ ϕ) ⟨&* q = (x ⟨& q) ∷ (ϕ ⟨&* q)

&-mono : ∀ {p₁ q₁ p₂ q₂} → (p₁ ⟶* p₂) → (q₁ ⟶* q₂) → (p₁ & q₁) ⟶* (p₂ & q₂)
&-mono {p₁}{q₁}{p₂}{q₂} f g = ⟶*-trans (p₁ &⟩* g) (f ⟨&* q₂)

-- _⊗_ is a monotone operator
_⊗⟩*_ : ∀ p {q₁ q₂} → q₁ ⟶* q₂ → (p ⊗ q₁) ⟶* (p ⊗ q₂)
p ⊗⟩* ε = ε
p ⊗⟩* (x ∷ ϕ) = (p ⊗⟩ x) ∷ (p ⊗⟩* ϕ)

-- _⟨⊗*_ : ∀ {p₁ p₂} → p₁ ⟶* p₂ → ∀ q → (p₁ ⊗ q) ⟶* (p₂ ⊗ q)
-- ε ⟨⊗* q = ε
-- (x ∷ ϕ) ⟨⊗* q = (x ⟨⊗ q) ∷ (ϕ ⟨⊗* q)






------------------------------------------------------------------------------
-- Construct the syntactic model from presheaves and chu. We can turn
-- MAV into a *-autonomous category with finite products and
-- coproducts in such a way that we can deduce cut-elimination is
-- admissible.

import presheaf
import chu
module P = presheaf ⟶*-isPreorder
module M = P.Monoid ⅋-isMonoid
module S = P.sheaf _&_ &-mono
module MS = S.SMonoid2 ⅋-isMonoid ⅋-sym (external ∷ ε)
module M▷ = S.SMonoid1 ▷-isMonoid (medial ∷ ε) (tidy ∷ ε)
module D = S.SDuoidal ⅋-isMonoid ⅋-sym (external ∷ ε) ▷-isMonoid (medial ∷ ε) (tidy ∷ ε) ⅋-▷-isDuoidal

open S._≤S_
open S.Sheaf

-- The units of the two monoids are equal (thanks to the tidy rule)
units-iso : MS.I S.≃S M▷.I
units-iso .proj₁ .*≤S* x (t , x≤t) = M▷.I .S≤-closed x≤t (M▷.I .Sclosed t)
units-iso .proj₂ .*≤S* x x≤I = S.lf (x , x≤I) , ε

open chu.Construction
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

open SelfDual M▷.▷-isMonoid
        (S.≤S-trans (M▷.▷-mono (D.units-iso .proj₁) S.≤S-refl) (M▷.▷-lunit .proj₁))
        (D.units-iso .proj₂)
        D.⊗-▷-isDuoidal

open Chu
open P._≤P_

_>>>_ = ⟶*-trans

-- The atom interaction law in PreSheaves
atom-int : ∀ a → (P.η (-at a) M.• P.η (+at a)) P.≤P P.η I
atom-int a .*≤P* p (p₁ , p₂ , p≤p₁p₂ , lift p₁≤a , lift p₂≤-a) .lower =
   p≤p₁p₂ >>> (⅋-mono p₁≤a p₂≤-a >>> (⅋-comm ∷ axiom ∷ ε))

atom : At → Chu
atom a .pos = S.α (P.η (-at a))
atom a .neg = S.α (P.η (+at a))
atom a .int = S.≤S-trans (MS.α-monoidal .proj₁) (S.α-mono (atom-int a))

-- Interpretation of formulas in Chu
⟦_⟧ : fmla → Chu
⟦ I ⟧ = ⟦I⟧
⟦ +at a ⟧ = atom a
⟦ -at a ⟧ = ⟦¬⟧ (atom a)
⟦ p ⅋ q ⟧ = ⟦ p ⟧ ⟦⅋⟧ ⟦ q ⟧
⟦ p ⊗ q ⟧ = ⟦ p ⟧ ⟦⊗⟧ ⟦ q ⟧
⟦ p & q ⟧ = ⟦ p ⟧ ⟦&⟧ ⟦ q ⟧
⟦ p ⊕ q ⟧ = ⟦ p ⟧ ⟦⊕⟧ ⟦ q ⟧
⟦ p ▷ q ⟧ = ⟦ p ⟧ ⍮ ⟦ q ⟧

tidyup-lem : (t : S.tree (Σ[ p ∈ fmla ] (Lift 0ℓ (p ⟶* I)))) →
             S.join t ⟶* I
tidyup-lem (S.lf (p , lift p⟶*I)) = p⟶*I
tidyup-lem (S.br s t) = &-mono (tidyup-lem s) (tidyup-lem t) >>> (tidy ∷ ε)

tidyup : ∀ {p} → MS.I .SCarrier p → p ⟶* I
tidyup (t , p⟶*t) = p⟶*t >>> tidyup-lem t

mutual
  okada : ∀ p → ⟦ p ⟧ .neg .SCarrier p
  okada I = S.lf (I , lift ε) , ε
  okada (+at a) = S.lf (+at a , lift ε) , ε
  okada (-at a) = S.lf (-at a , lift ε) , ε
  okada (p ⅋ q) = S.lf (p ⅋ q , p , q , ε , okada p , okada q) , ε
  okada (p ⊗ q) .proj₁ r x =
    ⟦ p ⟧ .neg .S≤-closed
      ((switch ∷ ε) >>> ((p ⊗⟩* (⅋-sym >>> okada2 q r x)) >>> (⊗-unit ∷ ε)))
      (okada p)
  okada (p ⊗ q) .proj₂ r x =
    ⟦ q ⟧ .neg .S≤-closed
      ((⊗-comm ⟨⅋ r ∷ switch ∷ ε) >>> ((q ⊗⟩* (⅋-sym >>> okada2 p r x)) >>> (⊗-unit ∷ ε)))
      (okada q)
  okada (p & q) =
    S.br (S.lf (p , inj₁ (okada p))) (S.lf (q , inj₂ (okada q))) , ε
  okada (p ⊕ q) =
    ⟦ p ⟧ .neg .S≤-closed (left ∷ ε) (okada p) ,
    ⟦ q ⟧ .neg .S≤-closed (right ∷ ε) (okada q)
  okada (p ▷ q) =
    p , q , ε , okada p , okada q

  okada2 : ∀ p r → ⟦ p ⟧ .pos .SCarrier r → (r ⅋ p) ⟶* I
  okada2 p r ϕ =
    tidyup (⟦ p ⟧ .int .*≤S* (r ⅋ p) (S.lf (r ⅋ p , r , p , ε , ϕ , okada p) , ε))

-- if 'p' is provable, then it has a cut-free proof
cut-elim : ∀ p → ⟦I⟧ ==> ⟦ p ⟧ → p ⟶* I
cut-elim p prf = tidyup (prf ._==>_.fneg .*≤S* p (okada p))
