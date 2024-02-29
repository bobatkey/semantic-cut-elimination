{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level renaming (suc to lsuc) hiding (zero)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to [_⊎_])
open import Relation.Binary using (Setoid)
open import basics

module presheaf {a b} {A : Set a} {_≤_ : A → A → Set b} (≤-isPreorder : IsPreorder _≤_)
    where

open IsPreorder ≤-isPreorder

record PreSheaf : Set (lsuc (a ⊔ b)) where
  no-eta-equality
  field
    Carrier  : A → Set (a ⊔ b)
    ≤-closed : ∀ {x y} → x ≤ y → Carrier y → Carrier x
open PreSheaf

record _≤P_ (F G : PreSheaf) : Set (a ⊔ b) where
  no-eta-equality
  field
    *≤P* : ∀ x → F .Carrier x → G .Carrier x
open _≤P_

≤P-isPreorder : IsPreorder _≤P_
≤P-isPreorder .IsPreorder.refl .*≤P* x Fx = Fx
≤P-isPreorder .IsPreorder.trans F≤G G≤H .*≤P* x Fx = G≤H .*≤P* x (F≤G .*≤P* x Fx)

≤P-trans = ≤P-isPreorder .IsPreorder.trans

_≃P_ : PreSheaf → PreSheaf → Set (a ⊔ b)
_≃P_ = SymmetricClosure _≤P_

infix 4 _≤P_
infix 4 _≃P_

η : A → PreSheaf
η x .Carrier y = Lift a (y ≤ x)
η x .≤-closed z≤y y≤x = lift (trans z≤y (y≤x .lower))

-- Meets
_∧_ : PreSheaf → PreSheaf → PreSheaf
(F ∧ G) .Carrier x = F .Carrier x × G .Carrier x
(F ∧ G) .≤-closed x≤y (Fy , Gy) = F .≤-closed x≤y Fy , G .≤-closed x≤y Gy

∧-isMeet : IsMeet ≤P-isPreorder _∧_
∧-isMeet .IsMeet.π₁ .*≤P* _ = proj₁
∧-isMeet .IsMeet.π₂ .*≤P* _ = proj₂
∧-isMeet .IsMeet.⟨_,_⟩ m₁ m₂ .*≤P* x Fx = m₁ .*≤P* x Fx , m₂ .*≤P* x Fx

-- Joins
_∨_ : PreSheaf → PreSheaf → PreSheaf
(F ∨ G) .Carrier x = F .Carrier x ⊎ G .Carrier x
(F ∨ G) .≤-closed x≤y (inj₁ Fy) = inj₁ (F .≤-closed x≤y Fy)
(F ∨ G) .≤-closed x≤y (inj₂ Gy) = inj₂ (G .≤-closed x≤y Gy)

∨-isJoin : IsJoin ≤P-isPreorder _∨_
∨-isJoin .IsJoin.inl .*≤P* _ = inj₁
∨-isJoin .IsJoin.inr .*≤P* _ = inj₂
∨-isJoin .IsJoin.[_,_] m₁ m₂ .*≤P* x (inj₁ Fx) = m₁ .*≤P* x Fx
∨-isJoin .IsJoin.[_,_] m₁ m₂ .*≤P* x (inj₂ Fx) = m₂ .*≤P* x Fx

-- Every monoid on A induces a monoid on PreSheaf(A)
module Monoid {_∙_ : A → A → A} {ε : A} (∙-isMonoid : IsMonoid ≤-isPreorder _∙_ ε) where

  open IsMonoid ∙-isMonoid

  _•_ : PreSheaf → PreSheaf → PreSheaf
  (F • G) .Carrier x =
    Σ[ y ∈ A ] Σ[ z ∈ A ] (x ≤ (y ∙ z) × F .Carrier y × G .Carrier z)
  (F • G) .≤-closed x≤x' (y , z , x'≤yz , ϕ₁ , ϕ₂) =
    y , z , trans x≤x' x'≤yz , ϕ₁ , ϕ₂

  J : PreSheaf
  J = η ε

  •-mono : ∀ {F₁ G₁ F₂ G₂} → F₁ ≤P F₂ → G₁ ≤P G₂ → (F₁ • G₁) ≤P (F₂ • G₂)
  •-mono F₁≤F₂ G₁≤G₂ .*≤P* x (y , z , x≤yz , F₁y , G₁z) =
    y , z , x≤yz , F₁≤F₂ .*≤P* y F₁y , G₁≤G₂ .*≤P* z G₁z

  •-lunit : ∀ {F} → J • F ≃P F
  •-lunit {F} .proj₁ .*≤P* x (y , z , x≤yz , lift y≤ε , Fz) =
    F .≤-closed (trans x≤yz (trans (mono y≤ε refl) (lunit .proj₁))) Fz
  •-lunit {F} .proj₂ .*≤P* x Fx =
    ε , x , lunit .proj₂ , lift refl , Fx

  •-runit : ∀ {F} → F • J ≃P F
  •-runit {F} .proj₁ .*≤P* x (y , z , x≤yz , Fy , lift z≤ε) =
    F .≤-closed (trans x≤yz (trans (mono refl z≤ε) (runit .proj₁))) Fy
  •-runit {F} .proj₂ .*≤P* x Fx =
    x , ε , runit .proj₂ , Fx , lift refl

  •-assoc : ∀ {F G H} → (F • G) • H ≃P F • (G • H)
  •-assoc .proj₁ .*≤P* x (y , z , x≤yz , (u , v , y≤uv , Fu , Gv) , Hz) =
    u , v ∙ z , trans x≤yz (trans (mono y≤uv refl) (assoc .proj₁)) ,
    Fu ,
    (v , z , refl , Gv , Hz)
  •-assoc .proj₂ .*≤P* x (y , z , x≤yz , Fy , (u , v , z≤uv , Gu , Hv)) =
    y ∙ u , v , trans x≤yz (trans (mono refl z≤uv) (assoc .proj₂)) ,
    (y , u , refl , Fy , Gu) ,
    Hv

  •-isMonoid : IsMonoid ≤P-isPreorder _•_ J
  •-isMonoid .IsMonoid.mono {F₁}{G₁}{F₂}{G₂} = •-mono {F₁}{G₁}{F₂}{G₂}
  •-isMonoid .IsMonoid.assoc {F}{G}{H} = •-assoc {F}{G}{H}
  •-isMonoid .IsMonoid.lunit {F} = •-lunit {F}
  •-isMonoid .IsMonoid.runit {F} = •-runit {F}

  •-sym : (∀ {x y} → (x ∙ y) ≤ (y ∙ x)) → ∀ {F G} → F • G ≤P G • F
  •-sym ∙-sym .*≤P* x (y , z , x≤yz , Fy , Gz) = z , y , trans x≤yz ∙-sym , Gz , Fy

  -- FIXME: deducible from closure
  •-∨-distrib : ∀ {F G H} → (F • (G ∨ H)) ≤P ((F • G) ∨ (F • H))
  •-∨-distrib .*≤P* x (y , z , x≤yz , Fy , inj₁ Gz) = inj₁ (y , z , x≤yz , Fy , Gz)
  •-∨-distrib .*≤P* x (y , z , x≤yz , Fy , inj₂ Hz) = inj₂ (y , z , x≤yz , Fy , Hz)

  -- right-closed
  _-•_ : PreSheaf → PreSheaf → PreSheaf
  (F -• G) .Carrier x = ∀ y → F .Carrier y → G .Carrier (x ∙ y)
  (F -• G) .≤-closed x≤x' f y Fy = G .≤-closed (mono x≤x' refl) (f y Fy)

  closed : ∀ {F G H} → F • G ≤P H → F ≤P G -• H
  closed m .*≤P* x Fx y Gy = m .*≤P* (x ∙ y) (x , y , refl , Fx , Gy)

  eval : ∀ {F G} → (F -• G) • F ≤P G
  eval {F}{G} .*≤P* x (y , z , x≤yz , F-•Gy , Fz) = G .≤-closed x≤yz (F-•Gy z Fz)

  -•-isClosure : IsClosure ≤P-isPreorder •-isMonoid _-•_
  -•-isClosure .IsClosure.lambda = closed
  -•-isClosure .IsClosure.eval = eval

  -- and left-closed, but every monoid we care about is symmetric so
  -- I'll not bother.


-- FIXME: If we have two monoids in a duoidal relationship, then they
-- have this relationship on the presheaf preorder. Let's do the
-- simple case where they share a unit first.
module Duoidal {_∙_ : A → A → A} {_▷_ : A → A → A} {ι : A}
               (∙-isMonoid : IsMonoid ≤-isPreorder _∙_ ι)
               (▷-isMonoid : IsMonoid ≤-isPreorder _▷_ ι)
               (∙-▷-exchange : ∀ {w x y z} → ((w ▷ x) ∙ (y ▷ z)) ≤ ((w ∙ y) ▷ (x ∙ z)))
  where

  open Monoid ∙-isMonoid using (_•_)
  open Monoid ▷-isMonoid renaming (_•_ to _⍮_)
  open IsMonoid ∙-isMonoid

  •-⍮-exchange : ∀ {w x y z} → ((w ⍮ x) • (y ⍮ z)) ≤P ((w • y) ⍮ (x • z))
  •-⍮-exchange .*≤P* x
      (y , z , x≤yz , (y₁ , y₂ , y≤y₁y₂ , Wy₁ , Xy₂) ,
                      (z₁ , z₂ , z≤z₁z₂ , Yz₁ , Zz₂)) =
      (y₁ ∙ z₁) , y₂ ∙ z₂ ,
      trans x≤yz (trans (mono y≤y₁y₂ z≤z₁z₂) ∙-▷-exchange) ,
      (y₁ , z₁ , refl , Wy₁ , Yz₁) ,
      (y₂ , z₂ , refl , Xy₂ , Zz₂)


-- A particular kind of Grothendieck preorder sheaf
module sheaf (_&_ : A → A → A)
             (&-mono : ∀ {x₁ y₁ x₂ y₂} → x₁ ≤ x₂ → y₁ ≤ y₂ → (x₁ & y₁) ≤ (x₂ & y₂))
          where -- we have some binary operator that we want to name the joins

  data tree {a} (A : Set a) : Set a where
    lf : A → tree A
    br : tree A → tree A → tree A

  map-tree : ∀ {a b}{X : A → Set a}{Y : A → Set b} →
             ((x : A) → X x → Y x) → tree (Σ[ x ∈ A ] X x) → tree (Σ[ x ∈ A ] Y x)
  map-tree f (lf (a , x)) = lf (a , f a x)
  map-tree f (br s t) = br (map-tree f s) (map-tree f t)

  join : ∀ {X : A → Set (a ⊔ b)} → tree (Σ[ x ∈ A ] X x) → A
  join (lf (x , _)) = x
  join (br s t) = join s & join t

  map-join : ∀ {X Y : A → Set (a ⊔ b)} →
             (f : (x : A) → X x → Y x) →
             (t : tree (Σ[ x ∈ A ] X x)) →
             join t ≤ join (map-tree f t)
  map-join f (lf x) = refl
  map-join f (br s t) = &-mono (map-join f s) (map-join f t)

  flatten : {X : A → Set (a ⊔ b)} →
            tree (Σ[ x ∈ A ] (Σ[ t ∈ tree (Σ[ y ∈ A ] X y) ] x ≤ join t)) →
            tree (Σ[ y ∈ A ] X y)
  flatten (lf (x , t , ϕ)) = t
  flatten (br s t)         = br (flatten s) (flatten t)

  flatten-join : {X : A → Set (a ⊔ b)} →
                 (t : tree (Σ[ x ∈ A ] (Σ[ t ∈ tree (Σ[ y ∈ A ] X y) ] x ≤ join t))) →
                 join t ≤ join (flatten t)
  flatten-join (lf (x , t , ϕ)) = ϕ
  flatten-join (br s t) = &-mono (flatten-join s) (flatten-join t)

  record Sheaf : Set (lsuc (a ⊔ b)) where
    no-eta-equality
    field
      SCarrier  : A → Set (a ⊔ b)
      S≤-closed : ∀ {x y} → x ≤ y → SCarrier y → SCarrier x
      Sclosed   : (t : tree (Σ[ x ∈ A ] SCarrier x)) → SCarrier (join t)
  open Sheaf

  record _≤S_ (F G : Sheaf) : Set (a ⊔ b) where
    no-eta-equality
    field
      *≤S* : ∀ x → F .SCarrier x → G .SCarrier x
  open _≤S_

  ≤S-trans : ∀ {F G H} → F ≤S G → G ≤S H → F ≤S H
  ≤S-trans F≤G G≤H .*≤S* = λ x z → G≤H .*≤S* x (F≤G .*≤S* x z)

  ≤S-isPreorder : IsPreorder _≤S_
  ≤S-isPreorder .IsPreorder.refl .*≤S* x ϕ = ϕ
  ≤S-isPreorder .IsPreorder.trans = ≤S-trans

  _≃S_ = SymmetricClosure _≤S_

  ------------------------------------------------------------------------------
  -- Turn a presheaf into a sheaf by closing under imaginary joins
  α : PreSheaf → Sheaf
  α F .SCarrier x = Σ[ t ∈ tree (Σ[ x ∈ A ] F .Carrier x) ] (x ≤ join t)
  α F .S≤-closed x≤y (t , ψ) = t , trans x≤y ψ
  α F .Sclosed t = flatten t , flatten-join t

  α-mono : ∀ {F G} → F ≤P G → α F ≤S α G
  α-mono F≤G .*≤S* x (t , ψ) = map-tree (F≤G .*≤P*) t , trans ψ (map-join _ t)

  α-cong : ∀ {F G} → F ≃P G → α F ≃S α G
  α-cong (ϕ , ψ) = (α-mono ϕ) , (α-mono ψ)

  U : Sheaf → PreSheaf
  U F .Carrier  = F .SCarrier
  U F .≤-closed = F .S≤-closed

  U-mono : ∀ {F G} → F ≤S G → U F ≤P U G
  U-mono F≤G .*≤P* = F≤G .*≤S*

  U-cong : ∀ {F G} → F ≃S G → U F ≃P U G
  U-cong (ϕ , ψ) = (U-mono ϕ) , (U-mono ψ)

  -- We have a reflective sub order
  counit : ∀ {F} → α (U F) ≤S F
  counit {F} .*≤S* x (t , ψ) = F .S≤-closed ψ (F .Sclosed t)

  counit⁻¹ : ∀ {F} → F ≤S α (U F)
  counit⁻¹ {F} .*≤S* x ϕ = lf (x , ϕ) , refl

  counit-≃ : ∀ {F} → F ≃S α (U F)
  counit-≃ = counit⁻¹ , counit

  unit : ∀ F → F ≤P U (α F)
  unit F .*≤P* x ϕ = lf (x , ϕ) , refl

  ------------------------------------------------------------------------------
  -- The topology is subcanonical if _&_ is sub-idempotent.
  module _ (&-idem : ∀ {x} → (x & x) ≤ x) where

    joinJ : ∀ x (t : tree (Σ[ y ∈ A ] Lift a (y ≤ x))) → join t ≤ x
    joinJ x (lf (y , lift y≤x)) = y≤x
    joinJ x (br s t) = trans (&-mono (joinJ x s) (joinJ x t)) &-idem

    ηS : A → Sheaf
    ηS x .SCarrier y = Lift a (y ≤ x)
    ηS x .S≤-closed x₁≤y (lift y≤x) = lift (trans x₁≤y y≤x)
    ηS x .Sclosed t .lower = joinJ _ t

  ------------------------------------------------------------------------------
  -- Meets'n'joins
  _∧S_ : Sheaf → Sheaf → Sheaf
  (F ∧S G) .SCarrier x = F .SCarrier x × G .SCarrier x
  (F ∧S G) .S≤-closed x≤y (Fy , Gy) = (F .S≤-closed x≤y Fy) , (G .S≤-closed x≤y Gy)
  (F ∧S G) .Sclosed t =
    F .S≤-closed (map-join _ t) (F .Sclosed (map-tree (λ _ → proj₁) t)) ,
    G .S≤-closed (map-join _ t) (G .Sclosed (map-tree (λ _ → proj₂) t))

  ∧S-isMeet : IsMeet ≤S-isPreorder _∧S_
  ∧S-isMeet .IsMeet.π₁ .*≤S* _ = proj₁
  ∧S-isMeet .IsMeet.π₂ .*≤S* _ = proj₂
  ∧S-isMeet .IsMeet.⟨_,_⟩ m₁ m₂ .*≤S* x Fx = m₁ .*≤S* x Fx , m₂ .*≤S* x Fx

  _∨S_ : Sheaf → Sheaf → Sheaf
  F ∨S G = α (U F ∨ U G)

  inl : ∀ {F G} → F ≤S (F ∨S G)
  inl = ≤S-trans counit⁻¹ (α-mono (∨-isJoin .IsJoin.inl))

  inr : ∀ {F G} → G ≤S (F ∨S G)
  inr = ≤S-trans counit⁻¹ (α-mono (∨-isJoin .IsJoin.inr))

  [_,_]S : ∀ {F G H} → F ≤S H → G ≤S H → (F ∨S G) ≤S H
  [_,_]S {F}{G}{H} m₁ m₂ .*≤S* x (t , x≤t) =
    H .S≤-closed (trans x≤t (map-join _ t))
      (H .Sclosed (map-tree (λ x → [ m₁ .*≤S* x ⊎ m₂ .*≤S* x ]) t))

  ∨S-isJoin : IsJoin ≤S-isPreorder _∨S_
  ∨S-isJoin .IsJoin.inl = inl
  ∨S-isJoin .IsJoin.inr = inr
  ∨S-isJoin .IsJoin.[_,_] = [_,_]S

  ------------------------------------------------------------------------------
  -- Monoids 1 : if we have a 'medial'-type monoid, then the
  -- presheaf monoid definition is already a sheaf
  module SMonoid1 {_∙_ : A → A → A} {ε : A}
                  (∙-isMonoid : IsMonoid ≤-isPreorder _∙_ ε)
                  -- this is how it interacts with the 'join'
                  (medial : ∀ {w x y z} → ((w ∙ x) & (y ∙ z)) ≤ ((w & y) ∙ (x & z)))
                  (tidy   : (ε & ε) ≤ ε)
       where

    open IsMonoid ∙-isMonoid

    split : ∀ {F G : A → Set (a ⊔ b)} →
            (t : tree (Σ[ x ∈ A ] Σ[ y ∈ A ] Σ[ z ∈ A ] (x ≤ (y ∙ z)) × F y × G z)) →
            Σ[ t₁ ∈ tree (Σ[ x ∈ A ] F x) ]
            Σ[ t₂ ∈ tree (Σ[ x ∈ A ] G x) ]
              (join t ≤ (join t₁ ∙ join t₂))
    split (lf (x , y , z , x≤yz , Fy , Gz)) = lf (y , Fy) , lf (z , Gz) , x≤yz
    split (br s t) =
      let s₁ , s₂ , s≤s₁s₂ = split s
          t₁ , t₂ , t≤t₁t₂ = split t
      in
      br s₁ t₁ , br s₂ t₂ , trans (&-mono s≤s₁s₂ t≤t₁t₂) medial

    _▷_ : Sheaf → Sheaf → Sheaf
    (F ▷ G) .SCarrier x =
      Σ[ y ∈ A ] Σ[ z ∈ A ] (x ≤ (y ∙ z) × F .SCarrier y × G .SCarrier z)
    (F ▷ G) .S≤-closed x≤x' (y , z , x'≤yz , Fy , Gz) =
      y , z , trans x≤x' x'≤yz , Fy , Gz
    (F ▷ G) .Sclosed t =
      let ft , gt , t≤fg = split t in
      join ft , join gt , t≤fg , F .Sclosed ft , G .Sclosed gt

    -- FIXME: this is the same as 'tidyup' in 'bv.agda', and is a
    -- special case of joinJ above.
    collapse : (t : tree (Σ[ x ∈ A ] Lift a (x ≤ ε))) → join t ≤ ε
    collapse (lf (x , lift x≤ε)) = x≤ε
    collapse (br s t) = trans (&-mono (collapse s) (collapse t)) tidy

    I : Sheaf
    I .SCarrier x = Lift a (x ≤ ε)
    I .S≤-closed x≤y (lift y≤ε) = lift (trans x≤y y≤ε)
    I .Sclosed t = lift (collapse t)

    -- Associativity etc. are now the same as before, because the
    -- carrier is the same
    open Monoid ∙-isMonoid

    ▷-assoc : ∀ {F G H} → ((F ▷ G) ▷ H) ≃S (F ▷ (G ▷ H))
    ▷-assoc {F}{G}{H} .proj₁ .*≤S* = •-assoc {U F}{U G}{U H} .proj₁ .*≤P*
    ▷-assoc {F}{G}{H} .proj₂ .*≤S* = •-assoc {U F}{U G}{U H} .proj₂ .*≤P*

    ▷-lunit : ∀ {F} → (I ▷ F) ≃S F
    ▷-lunit {F} .proj₁ .*≤S* = •-lunit {U F} .proj₁ .*≤P*
    ▷-lunit {F} .proj₂ .*≤S* = •-lunit {U F} .proj₂ .*≤P*

    ▷-runit : ∀ {F} → (F ▷ I) ≃S F
    ▷-runit {F} .proj₁ .*≤S* = •-runit {U F} .proj₁ .*≤P*
    ▷-runit {F} .proj₂ .*≤S* = •-runit {U F} .proj₂ .*≤P*

    ▷-isMonoid : IsMonoid ≤S-isPreorder _▷_ I
    ▷-isMonoid .IsMonoid.mono m₁ m₂ .*≤S* = •-mono (U-mono m₁) (U-mono m₂) .*≤P*
    ▷-isMonoid .IsMonoid.assoc = ▷-assoc
    ▷-isMonoid .IsMonoid.lunit = ▷-lunit
    ▷-isMonoid .IsMonoid.runit = ▷-runit


  -- A commutative monoid that distributes over the 'join' also
  -- gives a monoid on sheaves.
  module SMonoid2 {_∙_ : A → A → A} {ε : A}
                  (∙-isMonoid : IsMonoid ≤-isPreorder _∙_ ε)
                  (∙-sym : ∀ {x y} → (x ∙ y) ≤ (y ∙ x))
                  (∙-&-distrib : ∀ {x y z} → ((x & y) ∙ z) ≤ ((x ∙ z) & (y ∙ z)))
                 where

    open IsMonoid ∙-isMonoid
    open Monoid ∙-isMonoid

    _⊗_ : Sheaf → Sheaf → Sheaf
    F ⊗ G = α (U F • U G)

    I : Sheaf
    I = α (η ε)

    -- α is strong monoidal from PreSheaf to Sheaf
    module _ {F G : PreSheaf} where
       mul : tree (Σ[ x ∈ A ] F .Carrier x) →
             tree (Σ[ x ∈ A ] G .Carrier x) →
             tree (Σ[ x ∈ A ] (F • G) .Carrier x)
       mul (lf (x , Fx)) (lf (y , Gy)) = lf (x ∙ y , x , y , refl , Fx , Gy)
       mul (lf x)        (br t₁ t₂)    = br (mul (lf x) t₁) (mul (lf x) t₂)
       mul (br s₁ s₂)    t             = br (mul s₁ t) (mul s₂ t)

       mul-join : (t₁ : tree (Σ[ x ∈ A ] F .Carrier x)) →
                  (t₂ : tree (Σ[ x ∈ A ] G .Carrier x)) →
                  (join t₁ ∙ join t₂) ≤ join (mul t₁ t₂)
       mul-join (lf x) (lf x₁) = refl
       mul-join (lf x) (br t₂ t₃) =
         trans ∙-sym
         (trans ∙-&-distrib
         (&-mono (trans ∙-sym (mul-join (lf x) t₂))
                 (trans ∙-sym (mul-join (lf x) t₃))))
       mul-join (br s₁ s₂) t =
         trans ∙-&-distrib (&-mono (mul-join s₁ t) (mul-join s₂ t))

       -- The 2nd and 3rd arguments are unpacked to satisfy the termination checker
       -- FIXME: this is essentially a map-and-join operation that preserves the first components
       lemma : ∀ x
               (t : tree (Σ[ y ∈ A ] (U (α F) • U (α G)) .Carrier y)) →
               x ≤ join t →
               Σ[ t ∈ tree (Σ[ x ∈ A ] ((F • G) .Carrier x)) ] (x ≤ join t)
       lemma x (lf (y , (y₁ , y₂ , y≤y₁y₂ , (t₁ , y₁≤t₁) , (t₂ , y₂≤t₂)))) x≤y =
         (mul t₁ t₂) , trans x≤y (trans y≤y₁y₂ (trans (mono y₁≤t₁ y₂≤t₂) (mul-join t₁ t₂)))
       lemma x (br s t) x≤s&t =
         let (t₁ , ϕ₁) = lemma (join s) s refl
             (t₂ , ϕ₂) = lemma (join t) t refl
         in br t₁ t₂ , trans x≤s&t (&-mono ϕ₁ ϕ₂)

       α-monoidal : (α F ⊗ α G) ≃S α (F • G)
       α-monoidal .proj₁ .*≤S* x (t , x≤t) = lemma x t x≤t
       α-monoidal .proj₂ = α-mono (•-mono (unit F) (unit G))

    module _ where
      open IsMonoid •-isMonoid renaming (cong to •-cong) -- ; assoc to •-assoc)
      open Setoid (setoidOf ≤P-isPreorder) renaming (refl to P-refl)

      ⊗-assoc : ∀ {F G H} → ((F ⊗ G) ⊗ H) ≃S (F ⊗ (G ⊗ H))
      ⊗-assoc {F}{G}{H} = begin
          ((F ⊗ G) ⊗ H)
        ≡⟨⟩
          α (U (α (U F • U G)) • U H)
        ≈⟨ α-cong (•-cong P-refl (U-cong counit-≃)) ⟩
          α (U (α (U F • U G)) • U (α (U H)))
        ≈⟨ α-monoidal ⟩
          α ((U F • U G) • U H)
        ≈⟨ α-cong •-assoc ⟩
          α (U F • (U G • U H))
        ≈˘⟨ α-monoidal ⟩
          α (U (α (U F)) • U (α (U G • U H)))
        ≈˘⟨ α-cong (•-cong (U-cong counit-≃) P-refl) ⟩
          (F ⊗ (G ⊗ H))
        ∎
        where open import Relation.Binary.Reasoning.Setoid (setoidOf ≤S-isPreorder)

      ⊗-lunit : ∀ {F} → (I ⊗ F) ≃S F
      ⊗-lunit {F} = begin
            I ⊗ F
          ≡⟨⟩
            α (U (α J) • U F)
          ≈⟨ α-cong (•-cong P-refl (U-cong counit-≃)) ⟩
            α (U (α J) • U (α (U F)))
          ≈⟨ α-monoidal ⟩
            α (J • U F)
          ≈⟨ α-cong •-lunit ⟩
            α (U F)
          ≈˘⟨ counit-≃ ⟩
            F
          ∎
          where open import Relation.Binary.Reasoning.Setoid (setoidOf ≤S-isPreorder)

      ⊗-runit : ∀ {F} → (F ⊗ I) ≃S F
      ⊗-runit {F} = begin
            F ⊗ I
          ≡⟨⟩
            α (U F • U (α J))
          ≈⟨ α-cong (•-cong (U-cong counit-≃) P-refl) ⟩
            α (U (α (U F)) • U (α J))
          ≈⟨ α-monoidal ⟩
            α (U F • J)
          ≈⟨ α-cong •-runit ⟩
            α (U F)
          ≈˘⟨ counit-≃ ⟩
            F
          ∎
          where open import Relation.Binary.Reasoning.Setoid (setoidOf ≤S-isPreorder)


    ⊗-isMonoid : IsMonoid ≤S-isPreorder _⊗_ I
    ⊗-isMonoid .IsMonoid.mono m₁ m₂ = α-mono (•-mono (U-mono m₁) (U-mono m₂))
    ⊗-isMonoid .IsMonoid.assoc = ⊗-assoc
    ⊗-isMonoid .IsMonoid.lunit = ⊗-lunit
    ⊗-isMonoid .IsMonoid.runit = ⊗-runit

    ⊗-sym : ∀ {F G} → (F ⊗ G) ≤S (G ⊗ F)
    ⊗-sym {F}{G} = α-mono (•-sym ∙-sym {U F} {U G})

    -- Residuals are automatically closed, relying on
    -- distributivity. Is this deducible from strong monoidality of
    -- α?
    ⊸-lemma : ∀ F G →
              (t : tree (Σ[ x ∈ A ] (∀ y → F .SCarrier y → G .SCarrier (x ∙ y)))) →
              (y : A) → F .SCarrier y →
              Σ[ t' ∈ tree (Σ[ x ∈ A ] (G .SCarrier x)) ] (join t ∙ y) ≤ join t'
    ⊸-lemma F G (lf (x , f)) y Fy = (lf (x ∙ y , f y Fy)) , refl
    ⊸-lemma F G (br s t)     y Fy =
      let (s' , sy≤s') = ⊸-lemma F G s y Fy
          (t' , ty≤t') = ⊸-lemma F G t y Fy
      in br s' t' , trans ∙-&-distrib (&-mono sy≤s' ty≤t')

    _⊸_ : Sheaf → Sheaf → Sheaf
    (F ⊸ G) .SCarrier x = ∀ y → F .SCarrier y → G .SCarrier (x ∙ y)
    (F ⊸ G) .S≤-closed x≤x' f y Fy = G .S≤-closed (mono x≤x' refl) (f y Fy)
    (F ⊸ G) .Sclosed t y Fy =
      let t' , ty≤y' = ⊸-lemma F G t y Fy in
      G .S≤-closed ty≤y' (G .Sclosed t')

    U⊸ : ∀ {F G} → U (F ⊸ G) ≤P (U F -• U G)
    U⊸ .*≤P* x f = f

    ⊸-isClosure : IsClosure ≤S-isPreorder ⊗-isMonoid _⊸_
    ⊸-isClosure .IsClosure.lambda {F}{G}{H} m .*≤S* x Fx y Gy =
      -- FIXME: find a more abstract way of doing this
      m .*≤S* (x ∙ y) ((lf (x ∙ y , x , y , refl , Fx , Gy)) , refl)
    ⊸-isClosure .IsClosure.eval =
       ≤S-trans (α-mono (•-mono U⊸ (≤P-isPreorder .IsPreorder.refl)))
       (≤S-trans (α-mono eval) counit)

-- FIXME: now prove that if we have two duoidal monoids on A, with
-- the appropriate interactions with _&_, then we get a pair of
-- duoidal monoids on sheaves.

-- α (U (A ▷ B) • U (C ▷ D)) ≅ α ((U A ▷ U B) • (U C ▷ U D)) ≤ α ((U A • U C) ▷ (U B • U D)) ≤ α (U ((A • C) ▷ (B • D)))