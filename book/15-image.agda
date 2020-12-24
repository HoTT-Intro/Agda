{-# OPTIONS --without-K --exact-split #-}

module book.15-image where

open import book.14-propositional-truncation-solutions public

--------------------------------------------------------------------------------

-- Section 14.4 The image of a map

--------------------------------------------------------------------------------

-- The universal property of the image

-- Definition 14.4.1

-- We introduce the image inclusion of a map.

comp-hom-slice :
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (h : C → X) →
  hom-slice g h → hom-slice f g → hom-slice f h
comp-hom-slice f g h j i =
  pair ( ( map-hom-slice g h j) ∘
         ( map-hom-slice f g i))
       ( ( triangle-hom-slice f g i) ∙h
         ( (triangle-hom-slice g h j) ·r (map-hom-slice f g i)))

id-hom-slice :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) → hom-slice f f
id-hom-slice f = pair id refl-htpy

is-equiv-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → hom-slice f g → UU (l2 ⊔ l3)
is-equiv-hom-slice f g h = is-equiv (map-hom-slice f g h)

-- Definition 14.4.2

precomp-emb :
  { l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} ( i : B ↪ X) (q : hom-slice f (map-emb i)) →
  {C : UU l4} ( j : C ↪ X) (r : hom-slice (map-emb i) (map-emb j)) →
  hom-slice f (map-emb j)
precomp-emb f i q j r =
  pair
    ( ( map-hom-slice (map-emb i) (map-emb j) r) ∘
      ( map-hom-slice f (map-emb i) q))
    ( ( triangle-hom-slice f (map-emb i) q) ∙h
      ( ( triangle-hom-slice (map-emb i) (map-emb j) r) ·r
        ( map-hom-slice f (map-emb i) q)))

universal-property-image :
  ( l : Level) {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  { B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  UU (lsuc l ⊔ l1 ⊔ l2 ⊔ l3)
universal-property-image l {X = X} f i q =
  ( C : UU l) (j : C ↪ X) → is-equiv (precomp-emb f i q j)

-- Lemma 14.4.3

is-prop-hom-slice :
  { l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  { B : UU l3} (i : B ↪ X) → is-prop (hom-slice f (map-emb i))
is-prop-hom-slice {X = X} f i =
  is-prop-is-equiv
    ( (x : X) → fib f x → fib (map-emb i) x)
    ( fiberwise-hom-hom-slice f (map-emb i))
    ( is-equiv-fiberwise-hom-hom-slice f (map-emb i))
    ( is-prop-Π
      ( λ x → is-prop-Π
        ( λ p → is-prop-map-is-emb (is-emb-map-emb i) x)))

-- Proposition 14.4.4

-- Proposition 14.4.4 condition (ii)

universal-property-image' :
  ( l : Level) {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  { B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  UU (lsuc l ⊔ l1 ⊔ l2 ⊔ l3)
universal-property-image' l {X = X} f i q =
  ( C : UU l) (j : C ↪ X) →
    hom-slice f (map-emb j) → hom-slice (map-emb i) (map-emb j)

{- We show that condition (ii) implies the universal property of the image
   inclusion. The other direction of the equivalence is trivial and never 
   needed. -}

universal-property-image-universal-property-image' :
  ( l : Level) {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  { B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  universal-property-image' l f i q → universal-property-image l f i q
universal-property-image-universal-property-image' l f i q up' C j =
  is-equiv-is-prop
    ( is-prop-hom-slice (map-emb i) j)
    ( is-prop-hom-slice f j)
    ( up' C j)

-- Example 14.4.5

universal-property-image-has-section :
  (l : Level) {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  sec f → universal-property-image l f emb-id (pair f refl-htpy)
universal-property-image-has-section l f (pair g H) =
  universal-property-image-universal-property-image'
    l f emb-id (pair f refl-htpy)
    ( λ B m h → pair ((pr1 h) ∘ g) ( λ x → (inv (H x)) ∙ (pr2 h (g x))))

universal-property-image-is-emb :
  (l : Level) {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  (H : is-emb f) → universal-property-image l f (pair f H) (pair id refl-htpy)
universal-property-image-is-emb l f H =
  universal-property-image-universal-property-image'
    l f (pair f H) (pair id refl-htpy)
    ( λ B m h → h)

-- Example 14.4.6

{- We show that a map A → P into a proposition P is a propositional truncation
   if and only if P is the image of A in 1. -}

--------------------------------------------------------------------------------

-- The existence of the image

-- Definition 14.4.7

im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) → UU (l1 ⊔ l2)
im {X = X} {A} f = Σ X (λ x → type-trunc-Prop (fib f x))

inclusion-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) → im f → X
inclusion-im f = pr1

map-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) → A → im f
map-im f a = pair (f a) (unit-trunc-Prop (pair a refl))

triangle-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  f ~ (inclusion-im f ∘ map-im f)
triangle-im f a = refl

hom-slice-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  hom-slice f (inclusion-im f)
hom-slice-im f = pair (map-im f) (triangle-im f)

-- Proposition 14.4.8

is-emb-inclusion-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  is-emb (inclusion-im f)
is-emb-inclusion-im f =
  is-emb-pr1-is-subtype (λ x → is-prop-type-trunc-Prop)

emb-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) → im f ↪ X
emb-im f = pair (inclusion-im f) (is-emb-inclusion-im f)

-- Theorem 14.4.9

fiberwise-map-universal-property-im :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} (f : A → X) →
  (m : B ↪ X) (h : hom-slice f (map-emb m)) →
  (x : X) → type-trunc-Prop (fib f x) → fib (map-emb m) x
fiberwise-map-universal-property-im f m h x =
  map-universal-property-trunc-Prop
    { A = (fib f x)}
    ( fib-emb-Prop m x)
    ( λ t →
      pair ( map-hom-slice f (map-emb m) h (pr1 t))
           ( ( inv (triangle-hom-slice f (map-emb m) h (pr1 t))) ∙
             ( pr2 t)))

map-universal-property-im :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} (f : A → X) →
  (m : B ↪ X) (h : hom-slice f (map-emb m)) → im f → B
map-universal-property-im f m h (pair x t) =
  pr1 (fiberwise-map-universal-property-im f m h x t)

triangle-universal-property-im :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} (f : A → X) →
  (m : B ↪ X) (h : hom-slice f (map-emb m)) →
  inclusion-im f ~ ((map-emb m) ∘ (map-universal-property-im f m h))
triangle-universal-property-im f m h (pair x t) =
  inv (pr2 (fiberwise-map-universal-property-im f m h x t))

universal-property-im :
  (l : Level) {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  universal-property-image l f (emb-im f) (hom-slice-im f)
universal-property-im l f =
  universal-property-image-universal-property-image'
    l f (emb-im f) (hom-slice-im f)
    ( λ B m h →
      pair ( map-universal-property-im f m h)
           ( triangle-universal-property-im f m h))

{- We show some truncatedness results, so that we can use images as sets, and
   so on. -}

is-trunc-im :
  {l1 l2 : Level} (k : 𝕋) {X : UU l1} {A : UU l2} (f : A → X) →
  is-trunc (succ-𝕋 k) X → is-trunc (succ-𝕋 k) (im f)
is-trunc-im k f = is-trunc-emb k (emb-im f) 

is-prop-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  is-prop X → is-prop (im f)
is-prop-im = is-trunc-im neg-two-𝕋

is-set-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  is-set X → is-set (im f)
is-set-im = is-trunc-im neg-one-𝕋

is-1-type-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  is-1-type X → is-1-type (im f)
is-1-type-im = is-trunc-im zero-𝕋

im-Set' :
  {l1 l2 : Level} (A : UU l2) (X : UU-Set l1) (f : A → type-Set X) →
  UU-Set (l1 ⊔ l2)
im-Set' A X f = pair (im f) (is-set-im f (is-set-type-Set X))

im-Set :
  {l1 l2 : Level} (A : UU-Set l2) (X : UU-Set l1) (f : type-hom-Set A X) →
  UU-Set (l1 ⊔ l2)
im-Set A = im-Set' (type-Set A)

im-1-Type' :
  {l1 l2 : Level} (A : UU l2) (X : UU-1-Type l1)
  (f : A → type-1-Type X) → UU-1-Type (l1 ⊔ l2)
im-1-Type' A X f = pair (im f) (is-1-type-im f (is-1-type-type-1-Type X))

im-1-Type :
  {l1 l2 : Level} (A : UU-1-Type l2) (X : UU-1-Type l1)
  (f : type-hom-1-Type A X) → UU-1-Type (l1 ⊔ l2)
im-1-Type A = im-1-Type' (type-1-Type A)

--------------------------------------------------------------------------------

-- The uniqueness of the image

-- Proposition 14.4.10

is-equiv-hom-slice-emb :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A ↪ X) (g : B ↪ X) (h : hom-slice (map-emb f) (map-emb g)) →
  hom-slice (map-emb g) (map-emb f) →
  is-equiv-hom-slice (map-emb f) (map-emb g) h
is-equiv-hom-slice-emb f g h i =
  is-equiv-has-inverse
    ( map-hom-slice (map-emb g) (map-emb f) i)
    ( λ y →
      is-injective-emb g
      ( inv
        ( ( triangle-hom-slice
            ( map-emb g)
            ( map-emb f)
            ( i)
            ( y)) ∙
          ( triangle-hom-slice
            ( map-emb f)
            ( map-emb g)
            ( h)
            ( map-hom-slice (map-emb g) (map-emb f) i y)))))
    ( λ x →
      is-injective-emb f
      ( inv
        ( ( triangle-hom-slice (map-emb f) (map-emb g) h x) ∙
          ( triangle-hom-slice (map-emb g) (map-emb f) i
            ( map-hom-slice
              ( map-emb f)
              ( map-emb g)
              ( h)
              ( x))))))

is-equiv-up-image-up-image :
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  {B' : UU l4} (i' : B' ↪ X) (q' : hom-slice f (map-emb i'))
  (h : hom-slice (map-emb i) (map-emb i'))
  (p : Id (comp-hom-slice f (map-emb i) (map-emb i') h q) q') →
  ({l : Level} → universal-property-image l f i q) →
  ({l : Level} → universal-property-image l f i' q') →
  is-equiv (map-hom-slice (map-emb i) (map-emb i') h)
is-equiv-up-image-up-image f i q i' q' h p up-i up-i' =
  is-equiv-hom-slice-emb i i' h (map-inv-is-equiv (up-i' _ i) q)

up-image-up-image-is-equiv :
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  {B' : UU l4} (i' : B' ↪ X) (q' : hom-slice f (map-emb i'))
  (h : hom-slice (map-emb i) (map-emb i'))
  (p : Id (comp-hom-slice f (map-emb i) (map-emb i') h q) q') →
  is-equiv (map-hom-slice (map-emb i) (map-emb i') h) →
  ({l : Level} → universal-property-image l f i q) →
  ({l : Level} → universal-property-image l f i' q')
up-image-up-image-is-equiv f i q i' q' h p is-equiv-h up-i {l} =
  universal-property-image-universal-property-image' l f i' q'
    ( λ C j r →
      comp-hom-slice
        ( map-emb i')
        ( map-emb i)
        ( map-emb j)
        ( map-inv-is-equiv (up-i C j) r)
        ( pair
          ( map-inv-is-equiv is-equiv-h)
          ( triangle-section
            ( map-emb i)
            ( map-emb i')
            ( map-hom-slice (map-emb i) (map-emb i') h)
            ( triangle-hom-slice (map-emb i) (map-emb i') h)
            ( pair ( map-inv-is-equiv is-equiv-h)
                   ( issec-map-inv-is-equiv is-equiv-h)))))

up-image-is-equiv-up-image :
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  {B' : UU l4} (i' : B' ↪ X) (q' : hom-slice f (map-emb i'))
  (h : hom-slice (map-emb i) (map-emb i'))
  (p : Id (comp-hom-slice f (map-emb i) (map-emb i') h q) q') →
  ({l : Level} → universal-property-image l f i' q') →
  is-equiv (map-hom-slice (map-emb i) (map-emb i') h) →
  ({l : Level} → universal-property-image l f i q)
up-image-is-equiv-up-image f i q i' q' h p up-i' is-equiv-h {l} =
  universal-property-image-universal-property-image' l f i q
    ( λ C j r →
      comp-hom-slice
        ( map-emb i)
        ( map-emb i')
        ( map-emb j)
        ( map-inv-is-equiv (up-i' C j) r)
        ( h))

--------------------------------------------------------------------------------

-- Section 14.5 Surjective maps

-- Definition 14.5.1

is-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-surjective {B = B} f = (y : B) → type-trunc-Prop (fib f y)

-- Example 14.5.2

-- Proposition 14.5.3

dependent-universal-property-surj :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  UU ((lsuc l) ⊔ l1 ⊔ l2)
dependent-universal-property-surj l {B = B} f =
  (P : B → UU-Prop l) →
    is-equiv (λ (h : (b : B) → type-Prop (P b)) x → h (f x))

is-surjective-dependent-universal-property-surj :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  ({l : Level} → dependent-universal-property-surj l f) →
  is-surjective f
is-surjective-dependent-universal-property-surj f dup-surj-f =
  map-inv-is-equiv
    ( dup-surj-f (λ b → trunc-Prop (fib f b)))
    ( λ x → unit-trunc-Prop (pair x refl))

square-dependent-universal-property-surj :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (P : B → UU-Prop l3) →
  ( λ (h : (y : B) → type-Prop (P y)) x → h (f x)) ~
  ( ( λ h x → h (f x) (pair x refl)) ∘
    ( ( λ h y → (h y) ∘ unit-trunc-Prop) ∘
      ( λ h y → const (type-trunc-Prop (fib f y)) (type-Prop (P y)) (h y))))
square-dependent-universal-property-surj f P = refl-htpy

dependent-universal-property-surj-is-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-surjective f →
  ({l : Level} → dependent-universal-property-surj l f)
dependent-universal-property-surj-is-surjective f is-surj-f P =
  is-equiv-comp'
    ( λ h x → h (f x) (pair x refl))
    ( ( λ h y → (h y) ∘ unit-trunc-Prop) ∘
      ( λ h y → const (type-trunc-Prop (fib f y)) (type-Prop (P y)) (h y)))
    ( is-equiv-comp'
      ( λ h y → (h y) ∘ unit-trunc-Prop)
      ( λ h y → const (type-trunc-Prop (fib f y)) (type-Prop (P y)) (h y))
      ( is-equiv-postcomp-Π
        ( λ y p z → p)
        ( λ y →
          is-equiv-diagonal-is-contr
            ( is-surj-f y)
            ( is-proof-irrelevant-is-prop
              ( is-prop-type-trunc-Prop)
              ( is-surj-f y))
            ( type-Prop (P y))))
      ( is-equiv-postcomp-Π
        ( λ b g → g ∘ unit-trunc-Prop)
        ( λ b → is-propositional-truncation-trunc-Prop (fib f b) (P b))))
    ( is-equiv-map-reduce-Π-fib f ( λ y z → type-Prop (P y)))

-- Corollary 14.5.4

is-surjective-is-propositional-truncation :
  {l1 l2 : Level} {A : UU l1} {P : UU-Prop l2} (f : A → type-Prop P) →
    ({l : Level} → dependent-universal-property-propositional-truncation l P f) → is-surjective f
is-surjective-is-propositional-truncation f duppt-f =
  is-surjective-dependent-universal-property-surj f duppt-f

is-propsitional-truncation-is-surjective :
  {l1 l2 : Level} {A : UU l1} {P : UU-Prop l2} (f : A → type-Prop P) →
    is-surjective f → {l : Level} → dependent-universal-property-propositional-truncation l P f
is-propsitional-truncation-is-surjective f is-surj-f =
  dependent-universal-property-surj-is-surjective f is-surj-f

-- Theorem 14.5.5

{-
is-surjective-universal-property-image :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  ({l : Level} → universal-property-image l f i q) →
  is-surjective (map-hom-slice f (map-emb i) q)
is-surjective-universal-property-image f i q up-i b = {!!}
-}

--------------------------------------------------------------------------------

-- Section 14.6 Cantor's diagonal argument

-- Definition 14.6.1

-- Theorem 14.6.2

map-cantor :
  {l1 l2 : Level} (X : UU l1) (f : X → (X → UU-Prop l2)) → (X → UU-Prop l2)
map-cantor X f x = neg-Prop (f x x)

iff-eq :
  {l1 : Level} {P Q : UU-Prop l1} → Id P Q → P ⇔ Q
iff-eq refl = pair id id

no-fixed-points-neg-Prop :
  {l1 : Level} (P : UU-Prop l1) → ¬ (P ⇔ neg-Prop P)
no-fixed-points-neg-Prop P = no-fixed-points-neg (type-Prop P)

not-in-image-map-cantor :
  {l1 l2 : Level} (X : UU l1) (f : X → (X → UU-Prop l2)) →
  ( t : fib f (map-cantor X f)) → empty
not-in-image-map-cantor X f (pair x α) =
  no-fixed-points-neg-Prop (f x x) (iff-eq (htpy-eq α x))

cantor : {l1 l2 : Level} (X : UU l1) (f : X → (X → UU-Prop l2)) →
  ¬ (is-surjective f)
cantor X f H =
  ( apply-universal-property-trunc-Prop
    ( H (map-cantor X f))
    ( empty-Prop)
    ( not-in-image-map-cantor X f))
