{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level
open import Algebra
open import Algebra.Definitions
open import Algebra.Ordered
open import Algebra.Ordered.Definitions
open import Algebra.Ordered.Consequences
open import Function using (flip)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; <_,_>)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit using (⊤; tt)
open import Relation.Binary
open import Relation.Binary.Construct.Core.Symmetric as SymCore using (SymCore)
open import Relation.Binary.Lattice
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
import Relation.Binary.Construct.Flip.EqAndOrd as Flip
open import Relation.Unary using (Pred)

-- FIXME: not sheaves! we do not necessarily know that α : PreSheaf →
-- Sheaf defined below preserves finite limits. This is an extra
-- property that would turn it into a preorder Grothendieck topos. I
-- guess that this would need _&_ to distribute over meets in A (if we
-- assume that A has meets)?
--
-- Alternatively, the closure of the closure operation
--
--     C X x = Σ[ t ∈ Tree (Σ[ x ∈ A ] X .ICarrier x) ] x ≤ join t

module Sheaf
    {c ℓ₁ ℓ₂}
    {Carrier : Set c}      -- The underlying set
    {_≈_ : Rel Carrier ℓ₁} -- The underlying equality relation
    {_≤_ : Rel Carrier ℓ₂} -- The underlying order relationm
    (isPartialOrder : IsPartialOrder _≈_ _≤_)
    {_&_ : Op₂ Carrier}
    (&-isPomagma : IsPomagma _≈_ _≤_ _&_)
  where

open IsPartialOrder isPartialOrder
  using ()
  renaming
    ( refl  to ≤-refl
    ; trans to ≤-trans
    )

open IsPomagma &-isPomagma
  using ()
  renaming
    ( mono  to &-mono
    )

open import PreSheaf isPartialOrder as P
  using
    ( PreSheaf
    ; ICarrier
    ; ≤-closed
    ; _≤ᵖ_
    ; *≤ᵖ*
    ; _≈ᵖ_
    ; _∨ᵖ_
    ; inj₁ᵖ
    ; inj₂ᵖ
    )

private
  variable
    w x y z : Carrier
    ℓw ℓx ℓy ℓz : Level
    X : Pred Carrier ℓx
    Y : Pred Carrier ℓy
    Z : Pred Carrier ℓz
    F F₁ F₂ : PreSheaf
    G G₁ G₂ : PreSheaf
    H H₁ H₂ : PreSheaf

data Tree {a} (A : Set a) : Set a where
  leaf : A → Tree A
  node : Tree A → Tree A → Tree A

map-Tree : (∀ x → X x → Y x) → Tree (∃ X) → Tree (∃ Y)
map-Tree f (leaf (x , Xx)) = leaf (x , f x Xx)
map-Tree f (node l r)      = node (map-Tree f l) (map-Tree f r)

join : Tree (∃ X) → Carrier
join (leaf (x , _)) = x
join (node l r) = join l & join r

map-join : (f : ∀ x → X x → Y x) →
            (t : Tree (∃ X)) →
            join t ≤ join (map-Tree f t)
map-join f (leaf _) = ≤-refl
map-join f (node l r) = &-mono (map-join f l) (map-join f r)

flatten : Tree (∃[ x ] (Σ[ t ∈ Tree (∃[ y ] X y) ] x ≤ join t)) →
          Tree (∃[ y ] X y)
flatten (leaf (x , t , ϕ)) = t
flatten (node l r)         = node (flatten l) (flatten r)

flatten-join : (t : Tree (∃[ x ] (Σ[ t ∈ Tree (∃[ y ] X y) ] x ≤ join t))) →
                join t ≤ join (flatten t)
flatten-join (leaf (x , t , ϕ)) = ϕ
flatten-join (node l r) = &-mono (flatten-join l) (flatten-join r)

record Sheaf : Set (suc (c ⊔ ℓ₂)) where
  no-eta-equality
  field
    SCarrier  : Carrier → Set (c ⊔ ℓ₂)
    ≤-closed : x ≤ y → SCarrier y → SCarrier x
    closed   : (t : Tree (∃ SCarrier)) → SCarrier (join t)
open Sheaf

private
  variable
    R R₁ R₂ : Sheaf
    S S₁ S₂ : Sheaf
    T T₁ T₂ : Sheaf

infix 4 _≤ˢ_

record _≤ˢ_ (R S : Sheaf) : Set (c ⊔ ℓ₂) where
  no-eta-equality
  field
    *≤ˢ* : ∀ x → R .SCarrier x → S .SCarrier x
open _≤ˢ_

infix 4 _≥ˢ_

_≥ˢ_ : Sheaf → Sheaf → Set (c ⊔ ℓ₂)
_≥ˢ_ = flip _≤ˢ_

infix 4 _≈ˢ_

_≈ˢ_ : Sheaf → Sheaf → Set (c ⊔ ℓ₂)
_≈ˢ_ = SymCore _≤ˢ_

≤ˢ-refl : R ≤ˢ R
≤ˢ-refl .*≤ˢ* x Sx = Sx

≤ˢ-trans : R ≤ˢ S → S ≤ˢ T → R ≤ˢ T
≤ˢ-trans R≤S S≤T .*≤ˢ* x z = S≤T .*≤ˢ* x (R≤S .*≤ˢ* x z)

≤ˢ-isPartialOrder : IsPartialOrder _≈ˢ_ _≤ˢ_
≤ˢ-isPartialOrder = SymCore.isPreorder⇒isPartialOrder _≤ˢ_ ≡-≤ˢ-isPreorder
  where
    ≡-≤ˢ-isPreorder : IsPreorder _≡_ _≤ˢ_
    ≡-≤ˢ-isPreorder = record 
      { isEquivalence = PropEq.isEquivalence 
      ; reflexive = λ { PropEq.refl → ≤ˢ-refl } 
      ; trans = ≤ˢ-trans
      }

------------------------------------------------------------------------------
-- Turn a presheaf into a sheaf by closing under imaginary joins

α : PreSheaf → Sheaf
α F .SCarrier x = Σ[ t ∈ Tree (∃[ x ] F .ICarrier x) ] (x ≤ join t)
α F .≤-closed x≤y (t , ψ) = t , ≤-trans x≤y ψ
α F .closed t = flatten t , flatten-join t

α-mono : F ≤ᵖ G → α F ≤ˢ α G
α-mono F≤G .*≤ˢ* x (t , ψ) = map-Tree (F≤G .*≤ᵖ*) t , ≤-trans ψ (map-join _ t)

α-cong : ∀ {F G} → F ≈ᵖ G → α F ≈ˢ α G
α-cong (ϕ , ψ) = α-mono ϕ , α-mono ψ

------------------------------------------------------------------------------
-- Turn a sheaf into a presheaf

U : Sheaf → PreSheaf
U F .ICarrier  = F .SCarrier
U F .≤-closed = F .≤-closed

U-mono : R ≤ˢ S → U R ≤ᵖ U S
U-mono R≤S .*≤ᵖ* = R≤S .*≤ˢ*

U-cong : R ≈ˢ S → U R ≈ᵖ U S
U-cong (ϕ , ψ) = (U-mono ϕ , U-mono ψ)

-- We have a reflective sub order
counit : α (U R) ≤ˢ R
counit {R} .*≤ˢ* x (t , ψ) = R .≤-closed ψ (R .closed t)

counit⁻¹ : R ≤ˢ α (U R)
counit⁻¹ {R} .*≤ˢ* x ϕ = leaf (x , ϕ) , ≤-refl

counit-≈ˢ : R ≈ˢ α (U R)
counit-≈ˢ = counit⁻¹ , counit

unit : F ≤ᵖ U (α F)
unit .*≤ᵖ* x ϕ = leaf (x , ϕ) , ≤-refl

------------------------------------------------------------------------------
-- Construct a meet semilattice for presheaves

_∧ˢ_ : Sheaf → Sheaf → Sheaf
(R ∧ˢ S) .SCarrier x = R .SCarrier x × S .SCarrier x
(R ∧ˢ S) .≤-closed x≤y (Ry , Sy) = (R .≤-closed x≤y Ry) , (S .≤-closed x≤y Sy)
(R ∧ˢ S) .closed t =
  R .≤-closed (map-join _ t) (R .closed (map-Tree (λ _ → proj₁) t)) ,
  S .≤-closed (map-join _ t) (S .closed (map-Tree (λ _ → proj₂) t))

proj₁ˢ : (R ∧ˢ S) ≤ˢ R
proj₁ˢ .*≤ˢ* x = proj₁

proj₂ˢ : (R ∧ˢ S) ≤ˢ S
proj₂ˢ .*≤ˢ* x = proj₂

⟨_,_⟩ˢ : R ≤ˢ S → R ≤ˢ T → R ≤ˢ (S ∧ˢ T)
⟨ T≤R , T≤S ⟩ˢ .*≤ˢ* x = < T≤R .*≤ˢ* x , T≤S .*≤ˢ* x >

∧ˢ-isMeetSemilattice : IsMeetSemilattice _≈ˢ_ _≤ˢ_ _∧ˢ_
∧ˢ-isMeetSemilattice = record
  { isPartialOrder = ≤ˢ-isPartialOrder
  ; infimum        = λ R S → (proj₁ˢ ,  proj₂ˢ , λ T → ⟨_,_⟩ˢ)
  }

--     -- FIXME: work out what is needed here; probably going to have to
--     -- work out how to state stability of _&_ under pullbacks.
--     preserveMeets : ∀ {F G} → α (F ∧ᵖ G) ≈ˢ (α F ∧ᵖS α G)
--     preserveMeets .proj₁ = ⟨ (α-mono π₁) , (α-mono π₂) ⟩
--     preserveMeets .proj₂ .*≤ˢ* = {!!} -- this would be true if _&_ distributed across meets, which we are not assuming here

------------------------------------------------------------------------------
-- Construct a join semilattice for presheaves

_∨ˢ_ : Sheaf → Sheaf → Sheaf
R ∨ˢ S = α (U R ∨ᵖ U S)

inj₁ˢ : R ≤ˢ (R ∨ˢ S)
inj₁ˢ = ≤ˢ-trans counit⁻¹ (α-mono inj₁ᵖ)

inj₂ˢ : S ≤ˢ (R ∨ˢ S)
inj₂ˢ = ≤ˢ-trans counit⁻¹ (α-mono inj₂ᵖ)

[_,_]ˢ : R ≤ˢ T → S ≤ˢ T → (R ∨ˢ S) ≤ˢ T
[_,_]ˢ {R} {T} {S} R≤T S≤T .*≤ˢ* x (t , x≤t) =
  T .≤-closed (≤-trans x≤t (map-join _ t))
    (T .closed (map-Tree (λ x → [ R≤T .*≤ˢ* x , S≤T .*≤ˢ* x ]) t))

∨ˢ-isJoinSemilattice : IsJoinSemilattice _≈ˢ_ _≤ˢ_ _∨ˢ_
∨ˢ-isJoinSemilattice = record
  { isPartialOrder = ≤ˢ-isPartialOrder
  ; supremum       = λ R S → (inj₁ˢ , inj₂ˢ , λ T → [_,_]ˢ)
  }

------------------------------------------------------------------------------
-- The topology is subcanonical if _&_ is sub-idempotent.
module LiftSubidempotent
    (&-idem : Subidempotent _≤_ _&_)
  where

  joinʲ : ∀ x → (t : Tree (∃[ y ] Lift c (y ≤ x))) → join t ≤ x
  joinʲ x (leaf (y , lift y≤x)) = y≤x
  joinʲ x (node l r) = ≤-trans (&-mono (joinʲ x l) (joinʲ x r)) (&-idem _)

  ηˢ : Carrier → Sheaf
  ηˢ x .SCarrier y = Lift c (y ≤ x)
  ηˢ x .≤-closed z≤y (lift y≤x) = lift (≤-trans z≤y y≤x)
  ηˢ x .closed t .lower = joinʲ _ t

------------------------------------------------------------------------------
-- Monoids 1 : if we have a 'medial'-type monoid, then the
-- presheaf monoid definition is already a sheaf. I.e., U (α (F ∙ G)) ≃ U (α F) ∙ U (α G)

module LiftIsPomonoid 
    {_∙_} {ε} 
    (isPomonoid : IsPomonoid _≈_ _≤_ _∙_ ε)
    (&-exchange : Exchange _≤_ _&_ _∙_) 
    (&-idem : Subidempotent _≤_ _&_)
  where
  

--     split : ∀ {F G : A → Set (a ⊔ ℓ₂)} →
--             (t : Tree (Σ[ x ∈ A ] Σ[ y ∈ A ] Σ[ z ∈ A ] (x ≤ (y ∙ z)) × F y × G z)) →
--             Σ[ t₁ ∈ Tree (Σ[ x ∈ A ] F x) ]
--             Σ[ t₂ ∈ Tree (Σ[ x ∈ A ] G x) ]
--               (join t ≤ (join t₁ ∙ join t₂))
--     split (lf (x , y , z , x≤yz , Fy , Gz)) = lf (y , Fy) , lf (z , Gz) , x≤yz
--     split (br s t) =
--       let s₁ , s₂ , s≤s₁s₂ = split s
--           t₁ , t₂ , t≤t₁t₂ = split t
--       in
--       br s₁ t₁ , br s₂ t₂ , trans (&-mono s≤s₁s₂ t≤t₁t₂) medial

--     _▷_ : Sheaf → Sheaf → Sheaf
--     (F ▷ G) .SCarrier x =
--       Σ[ y ∈ A ] Σ[ z ∈ A ] (x ≤ (y ∙ z) × F .SCarrier y × G .SCarrier z)
--     (F ▷ G) .≤-closed x≤x' (y , z , x'≤yz , Fy , Gz) =
--       y , z , trans x≤x' x'≤yz , Fy , Gz
--     (F ▷ G) .closed t =
--       let ft , gt , t≤fg = split t in
--       join ft , join gt , t≤fg , F .closed ft , G .closed gt

--     -- FIXME: this is the same as 'tidyup' in 'bv.agda', and is a
--     -- special case of joinJ above.
--     collapse : (t : Tree (Σ[ x ∈ A ] Lift a (x ≤ ε))) → join t ≤ ε
--     collapse (lf (x , lift x≤ε)) = x≤ε
--     collapse (br s t) = trans (&-mono (collapse s) (collapse t)) tidy

--     I : Sheaf
--     I .SCarrier x = Lift a (x ≤ ε)
--     I .≤-closed x≤y (lift y≤ε) = lift (trans x≤y y≤ε)
--     I .closed t = lift (collapse t)

--     -- Associativity etc. are now the same as before, because the
--     -- carrier is the same
--     open Monoid ∙-isMonoid renaming (I to J)

--     ▷-mono : ∀ {F₁ G₁ F₂ G₂} → F₁ ≤ˢ F₂ → G₁ ≤ˢ G₂ → (F₁ ▷ G₁) ≤ˢ (F₂ ▷ G₂)
--     ▷-mono {F₁}{G₁}{F₂}{G₂} m₁ m₂ .*≤ˢ* =
--       ∙-mono {U F₁}{U G₁}{U F₂}{U G₂}
--         (record { *≤ᵖ* = m₁ .*≤ˢ* }) (record { *≤ᵖ* = m₂ .*≤ˢ* }) .*≤ᵖ*

--     ▷-assoc : ∀ {F G H} → ((F ▷ G) ▷ H) ≈ˢ (F ▷ (G ▷ H))
--     ▷-assoc {F}{G}{H} .proj₁ .*≤ˢ* = ∙-assoc {U F}{U G}{U H} .proj₁ .*≤ᵖ*
--     ▷-assoc {F}{G}{H} .proj₂ .*≤ˢ* = ∙-assoc {U F}{U G}{U H} .proj₂ .*≤ᵖ*

--     ▷-lunit : ∀ {F} → (I ▷ F) ≈ˢ F
--     ▷-lunit {F} .proj₁ .*≤ˢ* = ∙-lunit {U F} .proj₁ .*≤ᵖ*
--     ▷-lunit {F} .proj₂ .*≤ˢ* = ∙-lunit {U F} .proj₂ .*≤ᵖ*

--     ▷-runit : ∀ {F} → (F ▷ I) ≈ˢ F
--     ▷-runit {F} .proj₁ .*≤ˢ* = ∙-runit {U F} .proj₁ .*≤ᵖ*
--     ▷-runit {F} .proj₂ .*≤ˢ* = ∙-runit {U F} .proj₂ .*≤ᵖ*

--     ▷-isMonoid : IsMonoid ≤ˢ-isPreorder _▷_ I
--     ▷-isMonoid .IsMonoid.mono m₁ m₂ .*≤ˢ* = ∙-mono (U-mono m₁) (U-mono m₂) .*≤ᵖ*
--     ▷-isMonoid .IsMonoid.assoc = ▷-assoc
--     ▷-isMonoid .IsMonoid.lunit = ▷-lunit
--     ▷-isMonoid .IsMonoid.runit = ▷-runit

--     U-monoidal : ∀ {F G} → U (F ▷ G) ≈ᵖ (U F ∙ U G)
--     U-monoidal .proj₁ .*≤ᵖ* x ϕ = ϕ
--     U-monoidal .proj₂ .*≤ᵖ* x ϕ = ϕ

--   -- A commutative monoid that distributes over the 'join' also
--   -- gives a monoid on sheaves.
--   module SMonoid2 {_∙_ : A → A → A} {ε : A}
--                   (∙-isMonoid : IsMonoid ≤-isPreorder _∙_ ε)
--                   (∙-sym : ∀ {x y} → (x ∙ y) ≤ (y ∙ x))
--                   (∙-&-distrib : ∀ {x y z} → ((x & y) ∙ z) ≤ ((x ∙ z) & (y ∙ z)))
--                  where

--     open IsMonoid ∙-isMonoid
--     open Monoid ∙-isMonoid renaming (I to J)

--     _⊗_ : Sheaf → Sheaf → Sheaf
--     F ⊗ G = α (U F ∙ U G)

--     I : Sheaf
--     I = α J

--     -- α is strong monoidal from PreSheaf to Sheaf
--     module _ {F G : PreSheaf} where
--        mul : Tree (Σ[ x ∈ A ] F .ICarrier x) →
--              Tree (Σ[ x ∈ A ] G .ICarrier x) →
--              Tree (Σ[ x ∈ A ] (F ∙ G) .ICarrier x)
--        mul (lf (x , Fx)) (lf (y , Gy)) = lf (x ∙ y , x , y , refl , Fx , Gy)
--        mul (lf x)        (br t₁ t₂)    = br (mul (lf x) t₁) (mul (lf x) t₂)
--        mul (br s₁ s₂)    t             = br (mul s₁ t) (mul s₂ t)

--        mul-join : (t₁ : Tree (Σ[ x ∈ A ] F .ICarrier x)) →
--                   (t₂ : Tree (Σ[ x ∈ A ] G .ICarrier x)) →
--                   (join t₁ ∙ join t₂) ≤ join (mul t₁ t₂)
--        mul-join (lf x) (lf x₁) = refl
--        mul-join (lf x) (br t₂ t₃) =
--          trans ∙-sym
--          (trans ∙-&-distrib
--          (&-mono (trans ∙-sym (mul-join (lf x) t₂))
--                  (trans ∙-sym (mul-join (lf x) t₃))))
--        mul-join (br s₁ s₂) t =
--          trans ∙-&-distrib (&-mono (mul-join s₁ t) (mul-join s₂ t))

--        -- The 2nd and 3rd arguments are unpacked to satisfy the termination checker
--        -- FIXME: this is essentially a map-and-join operation that preserves the first components
--        lemma : ∀ x
--                (t : Tree (Σ[ y ∈ A ] (U (α F) ∙ U (α G)) .ICarrier y)) →
--                x ≤ join t →
--                Σ[ t ∈ Tree (Σ[ x ∈ A ] ((F ∙ G) .ICarrier x)) ] (x ≤ join t)
--        lemma x (lf (y , (y₁ , y₂ , y≤y₁y₂ , (t₁ , y₁≤t₁) , (t₂ , y₂≤t₂)))) x≤y =
--          (mul t₁ t₂) , trans x≤y (trans y≤y₁y₂ (trans (mono y₁≤t₁ y₂≤t₂) (mul-join t₁ t₂)))
--        lemma x (br s t) x≤s&t =
--          let (t₁ , ϕ₁) = lemma (join s) s refl
--              (t₂ , ϕ₂) = lemma (join t) t refl
--          in br t₁ t₂ , trans x≤s&t (&-mono ϕ₁ ϕ₂)

--        α-monoidal : (α F ⊗ α G) ≈ˢ α (F ∙ G)
--        α-monoidal .proj₁ .*≤ˢ* x (t , x≤t) = lemma x t x≤t
--        α-monoidal .proj₂ = α-mono (∙-mono (unit F) (unit G))

--     module _ where
--       open IsMonoid ∙-isMonoid renaming (cong to ∙-cong)
--       open Setoid (IsPreorder.≃-setoid ≤ᵖ-isPreorder) renaming (refl to P-refl)

--       ⊗-mono : ∀ {F₁ G₁ F₂ G₂} → F₁ ≤ˢ F₂ → G₁ ≤ˢ G₂ → (F₁ ⊗ G₁) ≤ˢ (F₂ ⊗ G₂)
--       ⊗-mono m₁ m₂ = α-mono (∙-mono (U-mono m₁) (U-mono m₂))

--       ⊗-assoc : ∀ {F G H} → ((F ⊗ G) ⊗ H) ≈ˢ (F ⊗ (G ⊗ H))
--       ⊗-assoc {F}{G}{H} = begin
--           ((F ⊗ G) ⊗ H)
--         ≡⟨⟩
--           α (U (α (U F ∙ U G)) ∙ U H)
--         ≈⟨ α-cong (∙-cong P-refl (U-cong counit-≃)) ⟩
--           α (U (α (U F ∙ U G)) ∙ U (α (U H)))
--         ≈⟨ α-monoidal ⟩
--           α ((U F ∙ U G) ∙ U H)
--         ≈⟨ α-cong ∙-assoc ⟩
--           α (U F ∙ (U G ∙ U H))
--         ≈˘⟨ α-monoidal ⟩
--           α (U (α (U F)) ∙ U (α (U G ∙ U H)))
--         ≈˘⟨ α-cong (∙-cong (U-cong counit-≃) P-refl) ⟩
--           (F ⊗ (G ⊗ H))
--         ∎
--         where open IsPreorder.≃-SetoidReasoning ≤ˢ-isPreorder

--       ⊗-lunit : ∀ {F} → (I ⊗ F) ≈ˢ F
--       ⊗-lunit {F} = begin
--             I ⊗ F
--           ≡⟨⟩
--             α (U (α J) ∙ U F)
--           ≈⟨ α-cong (∙-cong P-refl (U-cong counit-≃)) ⟩
--             α (U (α J) ∙ U (α (U F)))
--           ≈⟨ α-monoidal ⟩
--             α (J ∙ U F)
--           ≈⟨ α-cong ∙-lunit ⟩
--             α (U F)
--           ≈˘⟨ counit-≃ ⟩
--             F
--           ∎
--           where open IsPreorder.≃-SetoidReasoning ≤ˢ-isPreorder

--       ⊗-runit : ∀ {F} → (F ⊗ I) ≈ˢ F
--       ⊗-runit {F} = begin
--             F ⊗ I
--           ≡⟨⟩
--             α (U F ∙ U (α J))
--           ≈⟨ α-cong (∙-cong (U-cong counit-≃) P-refl) ⟩
--             α (U (α (U F)) ∙ U (α J))
--           ≈⟨ α-monoidal ⟩
--             α (U F ∙ J)
--           ≈⟨ α-cong ∙-runit ⟩
--             α (U F)
--           ≈˘⟨ counit-≃ ⟩
--             F
--           ∎
--           where open IsPreorder.≃-SetoidReasoning ≤ˢ-isPreorder

--     ⊗-isMonoid : IsMonoid ≤ˢ-isPreorder _⊗_ I
--     ⊗-isMonoid .IsMonoid.mono = ⊗-mono
--     ⊗-isMonoid .IsMonoid.assoc = ⊗-assoc
--     ⊗-isMonoid .IsMonoid.lunit = ⊗-lunit
--     ⊗-isMonoid .IsMonoid.runit = ⊗-runit

--     ⊗-sym : ∀ {F G} → (F ⊗ G) ≤ˢ (G ⊗ F)
--     ⊗-sym {F}{G} = α-mono (∙-sym ∙-sym {U F} {U G})

--     -- Residuals are automatically closed, relying on distributivity.
--     -- Is this deducible from strong monoidality of α?
--     ⊸-lemma : ∀ F G →
--               (t : Tree (Σ[ x ∈ A ] (∀ y → F .SCarrier y → G .SCarrier (x ∙ y)))) →
--               (y : A) → F .SCarrier y →
--               Σ[ t' ∈ Tree (Σ[ x ∈ A ] (G .SCarrier x)) ] (join t ∙ y) ≤ join t'
--     ⊸-lemma F G (lf (x , f)) y Fy = (lf (x ∙ y , f y Fy)) , refl
--     ⊸-lemma F G (br s t)     y Fy =
--       let (s' , sy≤s') = ⊸-lemma F G s y Fy
--           (t' , ty≤t') = ⊸-lemma F G t y Fy
--       in br s' t' , trans ∙-&-distrib (&-mono sy≤s' ty≤t')

--     _⊸_ : Sheaf → Sheaf → Sheaf
--     (F ⊸ G) .SCarrier x = ∀ y → F .SCarrier y → G .SCarrier (x ∙ y)
--     (F ⊸ G) .≤-closed x≤x' f y Fy = G .≤-closed (mono x≤x' refl) (f y Fy)
--     (F ⊸ G) .closed t y Fy =
--       let t' , ty≤y' = ⊸-lemma F G t y Fy in
--       G .≤-closed ty≤y' (G .closed t')

--     U⊸ : ∀ {F G} → U (F ⊸ G) ≤ᵖ (U F -∙ U G)
--     U⊸ .*≤ᵖ* x f = f

--     ⊸-isClosure : IsClosure ≤ˢ-isPreorder ⊗-isMonoid _⊸_
--     ⊸-isClosure .IsClosure.lambda {F}{G}{H} m .*≤ˢ* x Fx y Gy =
--       -- FIXME: find a more abstract way of doing this
--       m .*≤ˢ* (x ∙ y) ((lf (x ∙ y , x , y , refl , Fx , Gy)) , refl)
--     ⊸-isClosure .IsClosure.eval =
--        ≤ˢ-trans (α-mono (∙-mono U⊸ (≤ᵖ-isPreorder .IsPreorder.refl)))
--        (≤ˢ-trans (α-mono (-∙-isClosure .IsClosure.eval)) counit)

--   module SDuoidal {_∙_ : A → A → A} {_⍮_ : A → A → A} {ε : A}
--                   (∙-isMonoid : IsMonoid ≤-isPreorder _∙_ ε)
--                   (∙-sym : ∀ {x y} → (x ∙ y) ≤ (y ∙ x))
--                   (∙-&-distrib : ∀ {x y z} → ((x & y) ∙ z) ≤ ((x ∙ z) & (y ∙ z)))
--                   (⍮-isMonoid : IsMonoid ≤-isPreorder _⍮_ ε)
--                   (medial : ∀ {w x y z} → ((w ⍮ x) & (y ⍮ z)) ≤ ((w & y) ⍮ (x & z)))
--                   (tidy   : (ε & ε) ≤ ε)
--                   (∙-⍮-isDuoidal : IsDuoidal ≤-isPreorder ∙-isMonoid ⍮-isMonoid)
--               where

--     open Monoid ∙-isMonoid renaming (_∙_ to _⊛_; ∙-mono to ⊛-mono)
--     open Monoid ⍮-isMonoid renaming (_∙_ to _,-_; ∙-mono to ,--mono)
--     open SMonoid1 ⍮-isMonoid medial tidy renaming (I to J)
--     open SMonoid2 ∙-isMonoid ∙-sym ∙-&-distrib renaming (I to I⊗)

--     open Duoidal ∙-isMonoid ⍮-isMonoid ∙-⍮-isDuoidal

--     units-iso : I⊗ ≈ˢ J
--     units-iso .proj₁ .*≤ˢ* x (t , x≤t) = J .≤-closed x≤t (J .closed t)
--     units-iso .proj₂ .*≤ˢ* x x≤I = lf (x , x≤I) , refl

--     _>>_ = ≤ˢ-trans

--     ⊗-▷-isDuoidal : IsDuoidal ≤ˢ-isPreorder ⊗-isMonoid ▷-isMonoid
--     ⊗-▷-isDuoidal .IsDuoidal.exchange =
--       α-mono (⊛-mono (U-monoidal .proj₁) (U-monoidal .proj₁)) >>
--       (α-mono ∙-⍮-exchange >>
--       (α-mono (,--mono (unit _) (unit _)) >>
--       (α-mono (U-monoidal .proj₂)
--       >> counit)))
--       --   (w ▷ x) ⊗ (y ▷ z)
--       -- ≡ α (U (w ▷ x) ∙ U(y ▷ z))
--       -- ≃ α ((U w ⍮ U x) ∙ (U y ⍮ U z))
--       -- ≤ α ((U w ∙ U y) ⍮ (U x ∙ U z))
--       -- ≤ α (U (α (U w ∙ U y)) ⍮ U (α (U x ∙ U z)))
--       -- ≃ α (U ((w ⊗ y) ▷ (x ⊗ z))
--       -- ≡ (w ⊗ y) ▷ (x ⊗ z)
--     ⊗-▷-isDuoidal .IsDuoidal.mu = ⊗-mono (units-iso .proj₂) ≤ˢ-refl >> ⊗-lunit .proj₁
    