
{-# OPTIONS --without-K --exact-split --safe #-}

module book.09-equivalences where

import book.08-decidability-in-number-theory
open book.08-decidability-in-number-theory public

--------------------------------------------------------------------------------

-- Section 9.1 Homotopies

-- Definition 9.1.2

_~_ :
  {i j : Level} {A : UU i} {B : A → UU j} (f g : (x : A) → B x) → UU (i ⊔ j)
f ~ g = (x : _) → Id (f x) (g x)

-- Example 9.1.3

neg-neg-𝟚 : (neg-𝟚 ∘ neg-𝟚) ~ id
neg-neg-𝟚 true = refl
neg-neg-𝟚 false = refl

-- Remark 9.1.4

square :
  {i : Level} {A : UU i} {x y1 y2 z : A}
  (p1 : Id x y1) (q1 : Id y1 z) (p2 : Id x y2) (q2 : Id y2 z) → UU i
square p q p' q' = Id (p ∙ q) (p' ∙ q')

-- Definition 9.1.5

refl-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f : (x : A) → B x} → f ~ f
refl-htpy x = refl

{- Most of the time we get by with refl-htpy. However, sometimes Agda wants us
   to specify the implicit argument. The it is easier to call refl-htpy' than
   to use Agda's {f = ?} notation. -}
   
refl-htpy' :
  {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) → f ~ f
refl-htpy' f = refl-htpy

inv-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (f ~ g) → (g ~ f)
inv-htpy H x = inv (H x)

_∙h_ :
  {i j : Level} {A : UU i} {B : A → UU j} {f g h : (x : A) → B x} →
  (f ~ g) → (g ~ h) → (f ~ h)
_∙h_ H K x = (H x) ∙ (K x)

concat-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (f ~ g) → (h : (x : A) → B x) → (g ~ h) → (f ~ h)
concat-htpy H h K x = concat (H x) (h x) (K x)

concat-htpy' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x} →
  (g ~ h) → (f ~ g) → (f ~ h)
concat-htpy' f K H = H ∙h K

-- Proposition 9.1.6

-- Proposition 9.1.6 (i)

assoc-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g h k : (x : A) → B x} →
  (H : f ~ g) → (K : g ~ h) → (L : h ~ k) →
  ((H ∙h K) ∙h L) ~ (H ∙h (K ∙h L))
assoc-htpy H K L x = assoc (H x) (K x) (L x)

-- Proposition 9.1.6 (ii)

left-unit-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  {H : f ~ g} → (refl-htpy ∙h H) ~ H
left-unit-htpy x = left-unit

right-unit-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  {H : f ~ g} → (H ∙h refl-htpy) ~ H
right-unit-htpy x = right-unit

-- Proposition 9.1.6 (iii)

left-inv-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  (H : f ~ g) → ((inv-htpy H) ∙h H) ~ refl-htpy
left-inv-htpy H x = left-inv (H x)

right-inv-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  (H : f ~ g) → (H ∙h (inv-htpy H)) ~ refl-htpy
right-inv-htpy H x = right-inv (H x)

-- Definition 9.1.7

-- Definition 9.1.7 (i)

htpy-left-whisk :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k}
  (h : B → C) {f g : A → B} → (f ~ g) → ((h ∘ f) ~ (h ∘ g))
htpy-left-whisk h H x = ap h (H x)

_·l_ = htpy-left-whisk

-- Definition 9.1.7 (ii)

htpy-right-whisk :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k}
  {g h : B → C} (H : g ~ h) (f : A → B) → ((g ∘ f) ~ (h ∘ f))
htpy-right-whisk H f x = H (f x)

_·r_ = htpy-right-whisk

sq-left-whisk :
  {i : Level} {A : UU i} {x y1 y2 z : A} {p1 p1' : Id x y1}
  (s : Id p1 p1') {q1 : Id y1 z} {p2 : Id x y2} {q2 : Id y2 z} →
  square p1 q1 p2 q2 → square p1' q1 p2 q2
sq-left-whisk refl sq = sq

sq-top-whisk :
  {i : Level} {A : UU i} {x y1 y2 z : A}
  (p1 : Id x y1) (q1 : Id y1 z)
  (p2 : Id x y2) {p2' : Id x y2} (s : Id p2 p2') (q2 : Id y2 z) →
  square p1 q1 p2 q2 → square p1 q1 p2' q2
sq-top-whisk p1 q1 p2 refl q2 sq = sq

--------------------------------------------------------------------------------

-- Section 9.2 Bi-invertible maps

-- Definition 9.2.1

-- Definition 9.2.1 (i)

sec :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
sec {i} {j} {A} {B} f = Σ (B → A) (λ g → (f ∘ g) ~ id)

-- Definition 9.2.1 (ii)

retr :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
retr {i} {j} {A} {B} f = Σ (B → A) (λ g → (g ∘ f) ~ id)

_retract-of_ :
  {i j : Level} → UU i → UU j → UU (i ⊔ j)
A retract-of B = Σ (A → B) retr

section-retract-of :
  {i j : Level} {A : UU i} {B : UU j} → A retract-of B → A → B
section-retract-of = pr1

retr-section-retract-of :
  {i j : Level} {A : UU i} {B : UU j} (R : A retract-of B) →
  retr (section-retract-of R)
retr-section-retract-of = pr2

retraction-retract-of :
  {i j : Level} {A : UU i} {B : UU j} → (A retract-of B) → B → A
retraction-retract-of R = pr1 (retr-section-retract-of R)

is-retr-retraction-retract-of :
  {i j : Level} {A : UU i} {B : UU j} (R : A retract-of B) →
  ((retraction-retract-of R) ∘ (section-retract-of R)) ~ id
is-retr-retraction-retract-of R = pr2 (retr-section-retract-of R)

-- Definition 9.2.1 (ii)

is-equiv :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
is-equiv f = sec f × retr f

_≃_ :
  {i j : Level} (A : UU i) (B : UU j) → UU (i ⊔ j)
A ≃ B = Σ (A → B) (λ f → is-equiv f)

map-equiv :
  {i j : Level} {A : UU i} {B : UU j} → (A ≃ B) → (A → B)
map-equiv e = pr1 e

is-equiv-map-equiv :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) → is-equiv (map-equiv e)
is-equiv-map-equiv e = pr2 e

-- Example 9.2.3

is-equiv-id :
  {i : Level} {A : UU i} → is-equiv (id {i} {A})
is-equiv-id = pair (pair id refl-htpy) (pair id refl-htpy)

equiv-id :
  {i : Level} {A : UU i} → A ≃ A
equiv-id = pair id is-equiv-id

-- Example 9.2.4

abstract
  is-equiv-neg-𝟚 : is-equiv neg-𝟚
  is-equiv-neg-𝟚 =
    pair (pair neg-𝟚 neg-neg-𝟚) (pair neg-𝟚 neg-neg-𝟚)

equiv-neg-𝟚 : bool ≃ bool
equiv-neg-𝟚 = pair neg-𝟚 is-equiv-neg-𝟚

-- Example 9.2.5

-- We show that succ-ℤ is an equivalence

abstract
  is-equiv-succ-ℤ : is-equiv succ-ℤ
  is-equiv-succ-ℤ =
    pair (pair pred-ℤ right-inverse-pred-ℤ) (pair pred-ℤ left-inverse-pred-ℤ)

equiv-succ-ℤ : ℤ ≃ ℤ
equiv-succ-ℤ = pair succ-ℤ is-equiv-succ-ℤ

-- We show that pred-ℤ is an equivalence

abstract
  is-equiv-pred-ℤ : is-equiv pred-ℤ
  is-equiv-pred-ℤ =
    pair (pair succ-ℤ left-inverse-pred-ℤ) (pair succ-ℤ right-inverse-pred-ℤ)

equiv-pred-ℤ : ℤ ≃ ℤ
equiv-pred-ℤ = pair pred-ℤ is-equiv-pred-ℤ

-- We show that add-ℤ x is an equivalence

abstract
  is-equiv-add-ℤ : (x : ℤ) → is-equiv (add-ℤ x)
  is-equiv-add-ℤ x =
    pair
      ( pair
        ( add-ℤ (neg-ℤ x))
        ( λ y →
          ( inv (associative-add-ℤ x (neg-ℤ x) y)) ∙
          ( ( ap (add-ℤ' y) (right-inverse-law-add-ℤ x)) ∙
            ( left-unit-law-add-ℤ y))))
      ( pair
        ( add-ℤ (neg-ℤ x))
        ( λ y →
          ( inv (associative-add-ℤ (neg-ℤ x) x y)) ∙
          ( ( ap (add-ℤ' y) (left-inverse-law-add-ℤ x)) ∙
            ( left-unit-law-add-ℤ y))))

equiv-add-ℤ : ℤ → (ℤ ≃ ℤ)
equiv-add-ℤ x = pair (add-ℤ x) (is-equiv-add-ℤ x)

-- We show that add-ℤ' y is an equivalence

abstract
  is-equiv-add-ℤ' : (y : ℤ) → is-equiv (add-ℤ' y)
  is-equiv-add-ℤ' y =
    pair
      ( pair
        ( add-ℤ' (neg-ℤ y))
        ( λ x →
          ( associative-add-ℤ x (neg-ℤ y) y) ∙
          ( ( ap (add-ℤ x) (left-inverse-law-add-ℤ y)) ∙
            ( right-unit-law-add-ℤ x))))
      ( pair
        ( add-ℤ' (neg-ℤ y))
        ( λ x →
          ( associative-add-ℤ x y (neg-ℤ y)) ∙
          ( ( ap (add-ℤ x) (right-inverse-law-add-ℤ y)) ∙
            ( right-unit-law-add-ℤ x))))

equiv-add-ℤ' : ℤ → (ℤ ≃ ℤ)
equiv-add-ℤ' y = pair (add-ℤ' y) (is-equiv-add-ℤ' y)

-- We show that neg-ℤ is an equivalence

abstract
  is-equiv-neg-ℤ : is-equiv neg-ℤ
  is-equiv-neg-ℤ = pair (pair neg-ℤ neg-neg-ℤ) (pair neg-ℤ neg-neg-ℤ)

equiv-neg-ℤ : ℤ ≃ ℤ
equiv-neg-ℤ = pair neg-ℤ is-equiv-neg-ℤ

-- We show that succ-Fin k is an equivalence

-- We show that pred-Fin k is an equivalence

-- We show that add-Fin k x is an equivalence

-- We show that add-Fin' k y is an equivalence

-- We show that neg-Fin k is an equivalence

-- Remark 9.2.6

has-inverse :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
has-inverse {i} {j} {A} {B} f =
  Σ (B → A) (λ g → ((f ∘ g) ~ id) × ((g ∘ f) ~ id))

-- Proposition 9.2.7

is-equiv-has-inverse' :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  has-inverse f → is-equiv f
is-equiv-has-inverse' (pair g (pair H K)) = pair (pair g H) (pair g K)

is-equiv-has-inverse :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (g : B → A) (H : (f ∘ g) ~ id) (K : (g ∘ f) ~ id) → is-equiv f
is-equiv-has-inverse g H K =
  is-equiv-has-inverse' (pair g (pair H K))

-- Corollary 9.2.8

htpy-section-retraction :
  { i j : Level} {A : UU i} {B : UU j} {f : A → B}
  ( is-equiv-f : is-equiv f) →
  ( (pr1 (pr1 is-equiv-f))) ~ (pr1 (pr2 is-equiv-f))
htpy-section-retraction {i} {j} {A} {B} {f} (pair (pair g G) (pair h H)) =
    (inv-htpy (H ·r g)) ∙h (h ·l G)

has-inverse-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-equiv f → has-inverse f
has-inverse-is-equiv {i} {j} {A} {B} {f} (pair (pair g G) (pair h H)) =
  let is-equiv-f = pair (pair g G) (pair h H) in
  pair g (pair G (((htpy-section-retraction is-equiv-f) ·r f) ∙h H))

map-inv-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} → is-equiv f → B → A
map-inv-is-equiv is-equiv-f = pr1 (has-inverse-is-equiv is-equiv-f)

issec-map-inv-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (is-equiv-f : is-equiv f) → (f ∘ (map-inv-is-equiv is-equiv-f)) ~ id
issec-map-inv-is-equiv is-equiv-f = pr1 (pr2 (has-inverse-is-equiv is-equiv-f))

isretr-map-inv-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (is-equiv-f : is-equiv f) → ((map-inv-is-equiv is-equiv-f) ∘ f) ~ id
isretr-map-inv-is-equiv is-equiv-f = pr2 (pr2 (has-inverse-is-equiv is-equiv-f))

is-equiv-map-inv-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (is-equiv-f : is-equiv f) → is-equiv (map-inv-is-equiv is-equiv-f)
is-equiv-map-inv-is-equiv {i} {j} {A} {B} {f} is-equiv-f =
  is-equiv-has-inverse f
    ( isretr-map-inv-is-equiv is-equiv-f)
    ( issec-map-inv-is-equiv is-equiv-f)

map-inv-equiv :
  {i j : Level} {A : UU i} {B : UU j} → (A ≃ B) → (B → A)
map-inv-equiv e = map-inv-is-equiv (is-equiv-map-equiv e)

issec-map-inv-equiv :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) →
  ((map-equiv e) ∘ (map-inv-equiv e)) ~ id
issec-map-inv-equiv e = issec-map-inv-is-equiv (is-equiv-map-equiv e)

isretr-map-inv-equiv :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) →
  ((map-inv-equiv e) ∘ (map-equiv e)) ~ id
isretr-map-inv-equiv e = isretr-map-inv-is-equiv (is-equiv-map-equiv e)

is-equiv-map-inv-equiv :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) → is-equiv (map-inv-equiv e)
is-equiv-map-inv-equiv e =
  is-equiv-map-inv-is-equiv (is-equiv-map-equiv e)

inv-equiv :
  {i j : Level} {A : UU i} {B : UU j} → (A ≃ B) → (B ≃ A)
inv-equiv e = pair (map-inv-equiv e) (is-equiv-map-inv-equiv e)

-- Equivalences are injective

is-injective-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-equiv f → is-injective f
is-injective-is-equiv {l1} {l2} {A} {B} {f} H {x} {y} p =
  ( inv (isretr-map-inv-is-equiv H x)) ∙
  ( ( ap (map-inv-is-equiv H) p) ∙
    ( isretr-map-inv-is-equiv H y))

is-injective-map-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (e : A ≃ B) → is-injective (map-equiv e)
is-injective-map-equiv (pair f H) = is-injective-is-equiv H

is-equiv-is-injective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  sec f → is-injective f → is-equiv f
is-equiv-is-injective {f = f} (pair g G) H =
  is-equiv-has-inverse g G (λ x → H (G (f x)))

-- Remarks

-- Left unit law of coproducts

map-inv-left-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-empty A → B → coprod A B
map-inv-left-unit-law-coprod-is-empty A B H = inr

issec-map-inv-left-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty A) →
  ( map-left-unit-law-coprod-is-empty A B H ∘ map-inv-left-unit-law-coprod-is-empty A B H) ~ id
issec-map-inv-left-unit-law-coprod-is-empty A B H a = refl

isretr-map-inv-left-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty A) →
  ( map-inv-left-unit-law-coprod-is-empty A B H ∘ map-left-unit-law-coprod-is-empty A B H) ~ id
isretr-map-inv-left-unit-law-coprod-is-empty A B H (inl a) = ex-falso (H a)
isretr-map-inv-left-unit-law-coprod-is-empty A B H (inr b) = refl

is-equiv-map-left-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty A) →
  is-equiv (map-left-unit-law-coprod-is-empty A B H)
is-equiv-map-left-unit-law-coprod-is-empty A B H =
  is-equiv-has-inverse
    ( map-inv-left-unit-law-coprod-is-empty A B H)
    ( issec-map-inv-left-unit-law-coprod-is-empty A B H)
    ( isretr-map-inv-left-unit-law-coprod-is-empty A B H)

left-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty A) →
  coprod A B ≃ B
left-unit-law-coprod-is-empty A B H =
  pair (map-left-unit-law-coprod-is-empty A B H) (is-equiv-map-left-unit-law-coprod-is-empty A B H)

inv-left-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty A) →
  B ≃ coprod A B
inv-left-unit-law-coprod-is-empty A B H =
  pair ( map-inv-left-unit-law-coprod-is-empty A B H)
       ( is-equiv-has-inverse
         ( map-left-unit-law-coprod-is-empty A B H)
         ( isretr-map-inv-left-unit-law-coprod-is-empty A B H)
         ( issec-map-inv-left-unit-law-coprod-is-empty A B H))

map-left-unit-law-coprod :
  {l : Level} (B : UU l) → coprod empty B → B
map-left-unit-law-coprod B =
  map-left-unit-law-coprod-is-empty empty B id

map-inv-left-unit-law-coprod :
  {l : Level} (B : UU l) → B → coprod empty B
map-inv-left-unit-law-coprod B = inr

issec-map-inv-left-unit-law-coprod :
  {l : Level} (B : UU l) →
  ( map-left-unit-law-coprod B ∘ map-inv-left-unit-law-coprod B) ~ id
issec-map-inv-left-unit-law-coprod B =
  issec-map-inv-left-unit-law-coprod-is-empty empty B id

isretr-map-inv-left-unit-law-coprod :
  {l : Level} (B : UU l) →
  ( map-inv-left-unit-law-coprod B ∘ map-left-unit-law-coprod B) ~ id
isretr-map-inv-left-unit-law-coprod B =
  isretr-map-inv-left-unit-law-coprod-is-empty empty B id

is-equiv-map-left-unit-law-coprod :
  {l : Level} (B : UU l) → is-equiv (map-left-unit-law-coprod B)
is-equiv-map-left-unit-law-coprod B =
  is-equiv-map-left-unit-law-coprod-is-empty empty B id

left-unit-law-coprod :
  {l : Level} (B : UU l) → coprod empty B ≃ B
left-unit-law-coprod B =
  left-unit-law-coprod-is-empty empty B id

inv-left-unit-law-coprod :
  {l : Level} (B : UU l) → B ≃ (coprod empty B)
inv-left-unit-law-coprod B =
  inv-left-unit-law-coprod-is-empty empty B id

-- The right unit law for coproducts

map-inv-right-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-empty B → A → coprod A B
map-inv-right-unit-law-coprod-is-empty A B is-empty-B = inl

issec-map-inv-right-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty B) →
  ( map-right-unit-law-coprod-is-empty A B H ∘ map-inv-right-unit-law-coprod-is-empty A B H) ~ id
issec-map-inv-right-unit-law-coprod-is-empty A B H a = refl

isretr-map-inv-right-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty B) →
  ( map-inv-right-unit-law-coprod-is-empty A B H ∘ map-right-unit-law-coprod-is-empty A B H) ~ id
isretr-map-inv-right-unit-law-coprod-is-empty A B H (inl a) = refl
isretr-map-inv-right-unit-law-coprod-is-empty A B H (inr b) = ex-falso (H b)

is-equiv-map-right-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty B) →
  is-equiv (map-right-unit-law-coprod-is-empty A B H)
is-equiv-map-right-unit-law-coprod-is-empty A B H =
  is-equiv-has-inverse
    ( map-inv-right-unit-law-coprod-is-empty A B H)
    ( issec-map-inv-right-unit-law-coprod-is-empty A B H)
    ( isretr-map-inv-right-unit-law-coprod-is-empty A B H)

is-equiv-inl-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  is-empty B → is-equiv (inl {l1} {l2} {A} {B})
is-equiv-inl-is-empty A B H =
  is-equiv-has-inverse
    ( map-right-unit-law-coprod-is-empty A B H)
    ( isretr-map-inv-right-unit-law-coprod-is-empty A B H)
    ( issec-map-inv-right-unit-law-coprod-is-empty A B H)

right-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-empty B →
  (coprod A B) ≃ A
right-unit-law-coprod-is-empty A B H =
  pair ( map-right-unit-law-coprod-is-empty A B H)
       ( is-equiv-map-right-unit-law-coprod-is-empty A B H)

inv-right-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-empty B →
  A ≃ (coprod A B)
inv-right-unit-law-coprod-is-empty A B H =
  pair ( inl)
       ( is-equiv-has-inverse
         ( map-right-unit-law-coprod-is-empty A B H)
         ( isretr-map-inv-right-unit-law-coprod-is-empty A B H)
         ( issec-map-inv-right-unit-law-coprod-is-empty A B H))

map-right-unit-law-coprod :
  {l1 : Level} (A : UU l1) → coprod A empty → A
map-right-unit-law-coprod A = map-right-unit-law-coprod-is-empty A empty id

map-inv-right-unit-law-coprod :
  {l1 : Level} (A : UU l1) → A → coprod A empty
map-inv-right-unit-law-coprod A = inl

issec-map-inv-right-unit-law-coprod :
  {l1 : Level} (A : UU l1) →
  ( map-right-unit-law-coprod A ∘ map-inv-right-unit-law-coprod A) ~ id
issec-map-inv-right-unit-law-coprod A =
  issec-map-inv-right-unit-law-coprod-is-empty A empty id

isretr-map-inv-right-unit-law-coprod :
  {l1 : Level} (A : UU l1) →
  ( map-inv-right-unit-law-coprod A ∘ map-right-unit-law-coprod A) ~ id
isretr-map-inv-right-unit-law-coprod A =
  isretr-map-inv-right-unit-law-coprod-is-empty A empty id

is-equiv-map-right-unit-law-coprod :
  {l1 : Level} (A : UU l1) → is-equiv (map-right-unit-law-coprod A)
is-equiv-map-right-unit-law-coprod A =
  is-equiv-map-right-unit-law-coprod-is-empty A empty id

right-unit-law-coprod :
  {l1 : Level} (A : UU l1) → coprod A empty ≃ A
right-unit-law-coprod A =
  right-unit-law-coprod-is-empty A empty id

inv-right-unit-law-coprod :
  {l1 : Level} (A : UU l1) → A ≃ coprod A empty
inv-right-unit-law-coprod A =
  inv-right-unit-law-coprod-is-empty A empty id

-- Commutativity of coproducts

map-commutative-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → coprod A B → coprod B A
map-commutative-coprod A B (inl a) = inr a
map-commutative-coprod A B (inr b) = inl b

map-inv-commutative-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → coprod B A → coprod A B
map-inv-commutative-coprod A B = map-commutative-coprod B A

issec-map-inv-commutative-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  ( map-commutative-coprod A B ∘ map-commutative-coprod B A) ~ id
issec-map-inv-commutative-coprod A B (inl b) = refl
issec-map-inv-commutative-coprod A B (inr a) = refl

isretr-map-inv-commutative-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  ( map-commutative-coprod B A ∘ map-commutative-coprod A B) ~ id
isretr-map-inv-commutative-coprod A B = issec-map-inv-commutative-coprod B A

is-equiv-map-commutative-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  is-equiv (map-commutative-coprod A B)
is-equiv-map-commutative-coprod A B =
  is-equiv-has-inverse
    ( map-inv-commutative-coprod A B)
    ( issec-map-inv-commutative-coprod A B)
    ( isretr-map-inv-commutative-coprod A B)

-- Associativity of coproducts

map-assoc-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  coprod (coprod A B) C → coprod A (coprod B C)
map-assoc-coprod (inl (inl x)) = inl x
map-assoc-coprod (inl (inr x)) = inr (inl x)
map-assoc-coprod (inr x) = inr (inr x)

map-inv-assoc-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  coprod A (coprod B C) → coprod (coprod A B) C
map-inv-assoc-coprod (inl x) = inl (inl x)
map-inv-assoc-coprod (inr (inl x)) = inl (inr x)
map-inv-assoc-coprod (inr (inr x)) = inr x

issec-map-inv-assoc-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  ( map-assoc-coprod {A = A} {B} {C} ∘ map-inv-assoc-coprod) ~ id
issec-map-inv-assoc-coprod (inl x) = refl
issec-map-inv-assoc-coprod (inr (inl x)) = refl
issec-map-inv-assoc-coprod (inr (inr x)) = refl

isretr-map-inv-assoc-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  ( map-inv-assoc-coprod ∘ map-assoc-coprod {A = A} {B} {C}) ~ id
isretr-map-inv-assoc-coprod (inl (inl x)) = refl
isretr-map-inv-assoc-coprod (inl (inr x)) = refl
isretr-map-inv-assoc-coprod (inr x) = refl

is-equiv-map-assoc-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  is-equiv (map-assoc-coprod {A = A} {B} {C})
is-equiv-map-assoc-coprod =
  is-equiv-has-inverse
    map-inv-assoc-coprod
    issec-map-inv-assoc-coprod
    isretr-map-inv-assoc-coprod

is-equiv-map-inv-assoc-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  is-equiv (map-inv-assoc-coprod {A = A} {B} {C})
is-equiv-map-inv-assoc-coprod =
  is-equiv-has-inverse
    map-assoc-coprod
    isretr-map-inv-assoc-coprod
    issec-map-inv-assoc-coprod

assoc-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  coprod (coprod A B) C ≃ coprod A (coprod B C)
assoc-coprod = pair map-assoc-coprod is-equiv-map-assoc-coprod

inv-assoc-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  coprod A (coprod B C) ≃ coprod (coprod A B) C
inv-assoc-coprod = pair map-inv-assoc-coprod is-equiv-map-inv-assoc-coprod

{- We prove a left zero law for cartesian products. -}

inv-pr1-prod-empty :
  {l : Level} (X : UU l) → empty → empty × X
inv-pr1-prod-empty X ()

issec-inv-pr1-prod-empty :
  {l : Level} (X : UU l) → (pr1 ∘ (inv-pr1-prod-empty X)) ~ id
issec-inv-pr1-prod-empty X ()

isretr-inv-pr1-prod-empty :
  {l : Level} (X : UU l) → ((inv-pr1-prod-empty X) ∘ pr1) ~ id
isretr-inv-pr1-prod-empty X (pair () x)

is-equiv-pr1-prod-empty :
  {l : Level} (X : UU l) → is-equiv (pr1 {A = empty} {B = λ t → X})
is-equiv-pr1-prod-empty X =
  is-equiv-has-inverse
    ( inv-pr1-prod-empty X)
    ( issec-inv-pr1-prod-empty X)
    ( isretr-inv-pr1-prod-empty X)

left-zero-law-prod :
  {l : Level} (X : UU l) → (empty × X) ≃ empty
left-zero-law-prod X =
  pair pr1 (is-equiv-pr1-prod-empty X)

{- We prove the right zero law for cartesian products. -}

inv-pr2-prod-empty :
  {l : Level} (X : UU l) → empty → (X × empty)
inv-pr2-prod-empty X ()

issec-inv-pr2-prod-empty :
  {l : Level} (X : UU l) → (pr2 ∘ (inv-pr2-prod-empty X)) ~ id
issec-inv-pr2-prod-empty X ()

isretr-inv-pr2-prod-empty :
  {l : Level} (X : UU l) → ((inv-pr2-prod-empty X) ∘ pr2) ~ id
isretr-inv-pr2-prod-empty X (pair x ())

is-equiv-pr2-prod-empty :
  {l : Level} (X : UU l) → is-equiv (pr2 {A = X} {B = λ x → empty})
is-equiv-pr2-prod-empty X =
  is-equiv-has-inverse
    ( inv-pr2-prod-empty X)
    ( issec-inv-pr2-prod-empty X)
    ( isretr-inv-pr2-prod-empty X)

right-zero-law-prod :
  {l : Level} (X : UU l) → (X × empty) ≃ empty
right-zero-law-prod X =
  pair pr2 (is-equiv-pr2-prod-empty X)

-- Right absorption law for Σ-types and cartesian products

abstract
  is-equiv-is-empty :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-empty B → is-equiv f
  is-equiv-is-empty f H =
    is-equiv-has-inverse
      ( ex-falso ∘ H)
      ( λ y → ex-falso (H y))
      ( λ x → ex-falso (H (f x)))

abstract
  is-equiv-is-empty' :
    {l : Level} {A : UU l} (f : is-empty A) → is-equiv f
  is-equiv-is-empty' f = is-equiv-is-empty f id

map-right-absorption-Σ :
  {l : Level} (A : UU l) → Σ A (λ x → empty) → empty
map-right-absorption-Σ A (pair x ())

map-right-absorption-prod = map-right-absorption-Σ

abstract
  is-equiv-map-right-absorption-Σ :
    {l : Level} (A : UU l) → is-equiv (map-right-absorption-Σ A)
  is-equiv-map-right-absorption-Σ A =
    is-equiv-is-empty' (map-right-absorption-Σ A)

  is-equiv-map-right-absorption-prod = is-equiv-map-right-absorption-Σ

right-absorption-Σ :
  {l : Level} (A : UU l) → Σ A (λ x → empty) ≃ empty
right-absorption-Σ A =
  pair (map-right-absorption-Σ A) (is-equiv-map-right-absorption-Σ A)

right-absorption-prod :
  {l : Level} (A : UU l) → (A × empty) ≃ empty
right-absorption-prod = right-absorption-Σ

-- Left absorption law for Σ and cartesian products

map-left-absorption-Σ :
  {l : Level} (A : empty → UU l) → Σ empty A → empty
map-left-absorption-Σ A = pr1

map-left-absorption-prod :
  {l : Level} (A : UU l) → empty × A → empty
map-left-absorption-prod A = map-left-absorption-Σ (λ x → A)

is-equiv-map-left-absorption-Σ :
  {l : Level} (A : empty → UU l) → is-equiv (map-left-absorption-Σ A)
is-equiv-map-left-absorption-Σ A =
  is-equiv-is-empty' (map-left-absorption-Σ A)

is-equiv-map-left-absorption-prod :
  {l : Level} (A : UU l) → is-equiv (map-left-absorption-prod A)
is-equiv-map-left-absorption-prod A =
  is-equiv-map-left-absorption-Σ (λ x → A)

left-absorption-Σ :
  {l : Level} (A : empty → UU l) → Σ empty A ≃ empty
left-absorption-Σ A =
  pair (map-left-absorption-Σ A) (is-equiv-map-left-absorption-Σ A)

left-absorption-prod :
  {l : Level} (A : UU l) → (empty × A) ≃ empty
left-absorption-prod A = left-absorption-Σ (λ x → A)

-- Unit laws for Σ-types and cartesian products

map-left-unit-law-Σ :
  {l : Level} (A : unit → UU l) → Σ unit A → A star
map-left-unit-law-Σ A (pair star a) = a

map-inv-left-unit-law-Σ :
  {l : Level} (A : unit → UU l) → A star → Σ unit A
map-inv-left-unit-law-Σ A a = (pair star a)

issec-map-inv-left-unit-law-Σ :
  {l : Level} (A : unit → UU l) →
  ( map-left-unit-law-Σ A ∘ map-inv-left-unit-law-Σ A) ~ id
issec-map-inv-left-unit-law-Σ A a = refl

isretr-map-inv-left-unit-law-Σ :
  {l : Level} (A : unit → UU l) →
  ( map-inv-left-unit-law-Σ A ∘ map-left-unit-law-Σ A) ~ id
isretr-map-inv-left-unit-law-Σ A (pair star a) = refl

is-equiv-map-left-unit-law-Σ :
  {l : Level} (A : unit → UU l) → is-equiv (map-left-unit-law-Σ A)
is-equiv-map-left-unit-law-Σ A =
  is-equiv-has-inverse
    ( map-inv-left-unit-law-Σ A)
    ( issec-map-inv-left-unit-law-Σ A)
    ( isretr-map-inv-left-unit-law-Σ A)

left-unit-law-Σ :
  {l : Level} (A : unit → UU l) → Σ unit A ≃ A star
left-unit-law-Σ A =
  pair (map-left-unit-law-Σ A) (is-equiv-map-left-unit-law-Σ A)

map-left-unit-law-prod :
  {l : Level} (A : UU l) → unit × A → A
map-left-unit-law-prod A = pr2

map-inv-left-unit-law-prod :
  {l : Level} (A : UU l) → A → unit × A
map-inv-left-unit-law-prod A = map-inv-left-unit-law-Σ (λ x → A)

issec-map-inv-left-unit-law-prod :
  {l : Level} (A : UU l) →
  ( map-left-unit-law-prod A ∘ map-inv-left-unit-law-prod A) ~ id
issec-map-inv-left-unit-law-prod A =
  issec-map-inv-left-unit-law-Σ (λ x → A)

isretr-map-inv-left-unit-law-prod :
  {l : Level} (A : UU l) →
  ( map-inv-left-unit-law-prod A ∘ map-left-unit-law-prod A) ~ id
isretr-map-inv-left-unit-law-prod A (pair star a) = refl

is-equiv-map-left-unit-law-prod :
  {l : Level} (A : UU l) → is-equiv (map-left-unit-law-prod A)
is-equiv-map-left-unit-law-prod A =
  is-equiv-has-inverse
    ( map-inv-left-unit-law-prod A)
    ( issec-map-inv-left-unit-law-prod A)
    ( isretr-map-inv-left-unit-law-prod A)

left-unit-law-prod :
  {l : Level} (A : UU l) → (unit × A) ≃ A
left-unit-law-prod A =
  pair
    ( map-left-unit-law-prod A)
    ( is-equiv-map-left-unit-law-prod A)

inv-left-unit-law-prod :
  {l : Level} (A : UU l) → A ≃ (unit × A)
inv-left-unit-law-prod A =
  pair
    ( map-inv-left-unit-law-prod A)
    ( is-equiv-has-inverse
      ( map-left-unit-law-prod A)
      ( isretr-map-inv-left-unit-law-prod A)
      ( issec-map-inv-left-unit-law-prod A))

map-right-unit-law-prod :
  {l1 : Level} {A : UU l1} → A × unit → A
map-right-unit-law-prod = pr1

map-inv-right-unit-law-prod :
  {l1 : Level} {A : UU l1} → A → A × unit
map-inv-right-unit-law-prod a = pair a star

issec-map-inv-right-unit-law-prod :
  {l1 : Level} {A : UU l1} →
  (map-right-unit-law-prod {A = A} ∘ map-inv-right-unit-law-prod {A = A}) ~ id
issec-map-inv-right-unit-law-prod a = refl

isretr-map-inv-right-unit-law-prod :
  {l1 : Level} {A : UU l1} →
  (map-inv-right-unit-law-prod {A = A} ∘ map-right-unit-law-prod {A = A}) ~ id
isretr-map-inv-right-unit-law-prod (pair a star) = refl

is-equiv-map-right-unit-law-prod :
  {l1 : Level} {A : UU l1} → is-equiv (map-right-unit-law-prod {A = A})
is-equiv-map-right-unit-law-prod =
  is-equiv-has-inverse
    map-inv-right-unit-law-prod
    issec-map-inv-right-unit-law-prod
    isretr-map-inv-right-unit-law-prod

right-unit-law-prod : {l1 : Level} {A : UU l1} → (A × unit) ≃ A
right-unit-law-prod =
  pair map-right-unit-law-prod is-equiv-map-right-unit-law-prod

-- Associativity of Σ-types

triple :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  (a : A) (b : B a) → C a b → Σ A (λ x → Σ (B x) (C x))
triple a b c = pair a (pair b c)

triple' :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  (a : A) (b : B a) → C (pair a b) → Σ (Σ A B) C
triple' a b c = pair (pair a b) c

map-assoc-Σ :
  {i j k : Level} (A : UU i) (B : A → UU j) (C : (Σ A B) → UU k) →
  Σ (Σ A B) C → Σ A (λ x → Σ (B x) (λ y → C (pair x y)))
map-assoc-Σ A B C (pair (pair x y) z) = triple x y z

map-inv-assoc-Σ :
  {i j k : Level} (A : UU i) (B : A → UU j) (C : (Σ A B) → UU k) →
  Σ A (λ x → Σ (B x) (λ y → C (pair x y))) → Σ (Σ A B) C
map-inv-assoc-Σ A B C t = triple' (pr1 t) (pr1 (pr2 t)) (pr2 (pr2 t))

isretr-map-inv-assoc-Σ :
  {i j k : Level} (A : UU i) (B : A → UU j)
  (C : (Σ A B) → UU k) → ((map-inv-assoc-Σ  A B C) ∘ (map-assoc-Σ A B C)) ~ id
isretr-map-inv-assoc-Σ A B C (pair (pair x y) z) = refl

issec-map-inv-assoc-Σ :
  {i j k : Level} (A : UU i) (B : A → UU j)
  (C : (Σ A B) → UU k) → ((map-assoc-Σ A B C) ∘ (map-inv-assoc-Σ A B C)) ~ id
issec-map-inv-assoc-Σ A B C (pair x (pair y z)) = refl

abstract
  is-equiv-map-assoc-Σ :
    {i j k : Level} (A : UU i) (B : A → UU j)
    (C : (Σ A B) → UU k) → is-equiv (map-assoc-Σ A B C)
  is-equiv-map-assoc-Σ A B C =
    is-equiv-has-inverse
      ( map-inv-assoc-Σ A B C)
      ( issec-map-inv-assoc-Σ A B C)
      ( isretr-map-inv-assoc-Σ A B C)

assoc-Σ :
  {i j k : Level} (A : UU i) (B : A → UU j) (C : (Σ A B) → UU k) →
  Σ (Σ A B) C ≃ Σ A (λ x → Σ (B x) (λ y → C (pair x y)))
assoc-Σ A B C =
  pair (map-assoc-Σ A B C) (is-equiv-map-assoc-Σ A B C)

inv-assoc-Σ :
  {i j k : Level} (A : UU i) (B : A → UU j) (C : (Σ A B) → UU k) →
  Σ A (λ x → Σ (B x) (λ y → C (pair x y))) ≃ Σ (Σ A B) C
inv-assoc-Σ A B C =
  pair
    ( map-inv-assoc-Σ A B C)
    ( is-equiv-has-inverse
      ( map-assoc-Σ A B C)
      ( isretr-map-inv-assoc-Σ A B C)
      ( issec-map-inv-assoc-Σ A B C))

-- Another way to phrase associativity of Σ-types.

map-assoc-Σ' :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : (x : A) → B x → UU l3) →
  Σ (Σ A B) (λ w → C (pr1 w) (pr2 w)) → Σ A (λ x → Σ (B x) (C x))
map-assoc-Σ' A B C (pair (pair x y) z) = triple x y z

map-inv-assoc-Σ' :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : (x : A) → B x → UU l3) →
  Σ A (λ x → Σ (B x) (C x)) → Σ (Σ A B) (λ w → C (pr1 w) (pr2 w))
map-inv-assoc-Σ' A B C (pair x (pair y z)) = triple' x y z

issec-map-inv-assoc-Σ' :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : (x : A) → B x → UU l3) →
  ( map-assoc-Σ' A B C ∘ map-inv-assoc-Σ' A B C) ~ id
issec-map-inv-assoc-Σ' A B C (pair x (pair y z)) = refl

isretr-map-inv-assoc-Σ' :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : (x : A) → B x → UU l3) →
  ( map-inv-assoc-Σ' A B C ∘ map-assoc-Σ' A B C) ~ id
isretr-map-inv-assoc-Σ' A B C (pair (pair x y) z) = refl

is-equiv-map-assoc-Σ' :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : (x : A) → B x → UU l3) →
  is-equiv (map-assoc-Σ' A B C)
is-equiv-map-assoc-Σ' A B C =
  is-equiv-has-inverse
    ( map-inv-assoc-Σ' A B C)
    ( issec-map-inv-assoc-Σ' A B C)
    ( isretr-map-inv-assoc-Σ' A B C)

assoc-Σ' :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : (x : A) → B x → UU l3) →
  Σ (Σ A B) (λ w → C (pr1 w) (pr2 w)) ≃ Σ A (λ x → Σ (B x) (C x))
assoc-Σ' A B C = pair (map-assoc-Σ' A B C) (is-equiv-map-assoc-Σ' A B C)

inv-assoc-Σ' :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : (x : A) → B x → UU l3) →
  Σ A (λ x → Σ (B x) (C x)) ≃ Σ (Σ A B) (λ w → C (pr1 w) (pr2 w))
inv-assoc-Σ' A B C =
  pair
    ( map-inv-assoc-Σ' A B C)
    ( is-equiv-has-inverse
      ( map-assoc-Σ' A B C)
      ( isretr-map-inv-assoc-Σ' A B C)
      ( issec-map-inv-assoc-Σ' A B C))

-- Commutativity of cartesian products

map-commutative-prod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → A × B → B × A
map-commutative-prod A B (pair a b) = pair b a

map-inv-commutative-prod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → B × A → A × B
map-inv-commutative-prod A B = map-commutative-prod B A

issec-map-inv-commutative-prod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  (map-commutative-prod A B ∘ map-inv-commutative-prod A B) ~ id
issec-map-inv-commutative-prod A B (pair b a) = refl

isretr-map-inv-commutative-prod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  (map-inv-commutative-prod A B ∘ map-commutative-prod A B) ~ id
isretr-map-inv-commutative-prod A B (pair a b) = refl

is-equiv-map-commutative-prod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-equiv (map-commutative-prod A B)
is-equiv-map-commutative-prod A B =
  is-equiv-has-inverse
    ( map-inv-commutative-prod A B)
    ( issec-map-inv-commutative-prod A B)
    ( isretr-map-inv-commutative-prod A B)

commutative-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A × B) ≃ (B × A)
commutative-prod {l1} {l2} {A} {B} =
  pair (map-commutative-prod A B) (is-equiv-map-commutative-prod A B)

-- Associativity of cartesian products

map-assoc-prod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  (A × B) × C → A × (B × C)
map-assoc-prod A B C = map-assoc-Σ A (λ x → B) (λ w → C)

map-inv-assoc-prod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  A × (B × C) → (A × B) × C
map-inv-assoc-prod A B C = map-inv-assoc-Σ A (λ x → B) (λ w → C)

issec-map-inv-assoc-prod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  ( map-assoc-prod A B C ∘ map-inv-assoc-prod A B C) ~ id
issec-map-inv-assoc-prod A B C = issec-map-inv-assoc-Σ A (λ x → B) (λ w → C)

isretr-map-inv-assoc-prod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  ( map-inv-assoc-prod A B C ∘ map-assoc-prod A B C) ~ id
isretr-map-inv-assoc-prod A B C = isretr-map-inv-assoc-Σ A (λ x → B) (λ w → C)

is-equiv-map-assoc-prod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  is-equiv (map-assoc-prod A B C)
is-equiv-map-assoc-prod A B C = is-equiv-map-assoc-Σ A (λ x → B) (λ w → C)

assoc-prod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  ((A × B) × C) ≃ (A × (B × C))
assoc-prod A B C = assoc-Σ A (λ x → B) (λ w → C)

-- Right distributivity of Σ over coproducts

map-right-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2)
  (C : coprod A B → UU l3) → Σ (coprod A B) C →
  coprod (Σ A (λ x → C (inl x))) (Σ B (λ y → C (inr y)))
map-right-distributive-Σ-coprod A B C (pair (inl x) z) = inl (pair x z)
map-right-distributive-Σ-coprod A B C (pair (inr y) z) = inr (pair y z)

map-inv-right-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2)
  (C : coprod A B → UU l3) →
  coprod (Σ A (λ x → C (inl x))) (Σ B (λ y → C (inr y))) → Σ (coprod A B) C
map-inv-right-distributive-Σ-coprod A B C (inl (pair x z)) = pair (inl x) z
map-inv-right-distributive-Σ-coprod A B C (inr (pair y z)) = pair (inr y) z

issec-map-inv-right-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : coprod A B → UU l3) →
  ( (map-right-distributive-Σ-coprod A B C) ∘
    (map-inv-right-distributive-Σ-coprod A B C)) ~ id
issec-map-inv-right-distributive-Σ-coprod A B C (inl (pair x z)) = refl
issec-map-inv-right-distributive-Σ-coprod A B C (inr (pair y z)) = refl

isretr-map-inv-right-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : coprod A B → UU l3) →
  ( (map-inv-right-distributive-Σ-coprod A B C) ∘
    (map-right-distributive-Σ-coprod A B C)) ~ id
isretr-map-inv-right-distributive-Σ-coprod A B C (pair (inl x) z) = refl
isretr-map-inv-right-distributive-Σ-coprod A B C (pair (inr y) z) = refl

abstract
  is-equiv-map-right-distributive-Σ-coprod :
    {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : coprod A B → UU l3) →
    is-equiv (map-right-distributive-Σ-coprod A B C)
  is-equiv-map-right-distributive-Σ-coprod A B C =
    is-equiv-has-inverse
      ( map-inv-right-distributive-Σ-coprod A B C)
      ( issec-map-inv-right-distributive-Σ-coprod A B C)
      ( isretr-map-inv-right-distributive-Σ-coprod A B C)

right-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : coprod A B → UU l3) →
  Σ (coprod A B) C ≃ coprod (Σ A (λ x → C (inl x))) (Σ B (λ y → C (inr y)))
right-distributive-Σ-coprod A B C =
  pair ( map-right-distributive-Σ-coprod A B C)
       ( is-equiv-map-right-distributive-Σ-coprod A B C)

-- Left distributivity of Σ over coproducts

map-left-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : A → UU l3) →
  Σ A (λ x → coprod (B x) (C x)) → coprod (Σ A B) (Σ A C)
map-left-distributive-Σ-coprod A B C (pair x (inl y)) = inl (pair x y)
map-left-distributive-Σ-coprod A B C (pair x (inr z)) = inr (pair x z)

map-inv-left-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : A → UU l3) →
  coprod (Σ A B) (Σ A C) → Σ A (λ x → coprod (B x) (C x))
map-inv-left-distributive-Σ-coprod A B C (inl (pair x y)) = pair x (inl y)
map-inv-left-distributive-Σ-coprod A B C (inr (pair x z)) = pair x (inr z)

issec-map-inv-left-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : A → UU l3) →
  ( ( map-left-distributive-Σ-coprod A B C) ∘
    ( map-inv-left-distributive-Σ-coprod A B C)) ~ id
issec-map-inv-left-distributive-Σ-coprod A B C (inl (pair x y)) = refl
issec-map-inv-left-distributive-Σ-coprod A B C (inr (pair x z)) = refl

isretr-map-inv-left-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : A → UU l3) →
  ( ( map-inv-left-distributive-Σ-coprod A B C) ∘
    ( map-left-distributive-Σ-coprod A B C)) ~ id
isretr-map-inv-left-distributive-Σ-coprod A B C (pair x (inl y)) = refl
isretr-map-inv-left-distributive-Σ-coprod A B C (pair x (inr z)) = refl

is-equiv-map-left-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : A → UU l3) →
  is-equiv (map-left-distributive-Σ-coprod A B C)
is-equiv-map-left-distributive-Σ-coprod A B C =
  is-equiv-has-inverse
    ( map-inv-left-distributive-Σ-coprod A B C)
    ( issec-map-inv-left-distributive-Σ-coprod A B C)
    ( isretr-map-inv-left-distributive-Σ-coprod A B C)

left-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : A → UU l3) →
  Σ A (λ x → coprod (B x) (C x)) ≃ coprod (Σ A B) (Σ A C)
left-distributive-Σ-coprod A B C =
  pair ( map-left-distributive-Σ-coprod A B C)
       ( is-equiv-map-left-distributive-Σ-coprod A B C)

-- Right distributivity of products over coproducts

map-right-distributive-prod-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  (coprod A B) × C → coprod (A × C) (B × C)
map-right-distributive-prod-coprod A B C =
  map-right-distributive-Σ-coprod A B (λ x → C)

map-inv-right-distributive-prod-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  coprod (A × C) (B × C) → (coprod A B) × C
map-inv-right-distributive-prod-coprod A B C =
  map-inv-right-distributive-Σ-coprod A B (λ x → C)

issec-map-inv-right-distributive-prod-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  ( (map-right-distributive-prod-coprod A B C) ∘
    (map-inv-right-distributive-prod-coprod A B C)) ~ id
issec-map-inv-right-distributive-prod-coprod A B C =
  issec-map-inv-right-distributive-Σ-coprod A B (λ x → C)

isretr-map-inv-right-distributive-prod-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  ( (map-inv-right-distributive-prod-coprod A B C) ∘
    (map-right-distributive-prod-coprod A B C)) ~ id
isretr-map-inv-right-distributive-prod-coprod A B C =
  isretr-map-inv-right-distributive-Σ-coprod A B (λ x → C)

abstract
  is-equiv-map-right-distributive-prod-coprod :
    {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
    is-equiv (map-right-distributive-prod-coprod A B C)
  is-equiv-map-right-distributive-prod-coprod A B C =
    is-equiv-map-right-distributive-Σ-coprod A B (λ x → C)

right-distributive-prod-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  ((coprod A B) × C) ≃ coprod (A × C) (B × C)
right-distributive-prod-coprod A B C =
  right-distributive-Σ-coprod A B (λ x → C)

-- Left distributivity of products over coproducts

map-left-distributive-prod-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  A × (coprod B C) → coprod (A × B) (A × C)
map-left-distributive-prod-coprod A B C =
  map-left-distributive-Σ-coprod A (λ x → B) (λ x → C)

map-inv-left-distributive-prod-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  coprod (A × B) (A × C) → A × (coprod B C)
map-inv-left-distributive-prod-coprod A B C =
  map-inv-left-distributive-Σ-coprod A (λ x → B) (λ x → C)

issec-map-inv-left-distributive-prod-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  ( ( map-left-distributive-prod-coprod A B C) ∘
    ( map-inv-left-distributive-prod-coprod A B C)) ~ id
issec-map-inv-left-distributive-prod-coprod A B C =
  issec-map-inv-left-distributive-Σ-coprod A (λ x → B) (λ x → C)

isretr-map-inv-left-distributive-prod-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  ( ( map-inv-left-distributive-prod-coprod A B C) ∘
    ( map-left-distributive-prod-coprod A B C)) ~ id
isretr-map-inv-left-distributive-prod-coprod A B C =
  isretr-map-inv-left-distributive-Σ-coprod A (λ x → B) (λ x → C)

is-equiv-map-left-distributive-prod-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  is-equiv (map-left-distributive-prod-coprod A B C)
is-equiv-map-left-distributive-prod-coprod A B C =
  is-equiv-map-left-distributive-Σ-coprod A (λ x → B) (λ x → C)

left-distributive-prod-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  (A × (coprod B C)) ≃ coprod (A × B) (A × C)
left-distributive-prod-coprod A B C =
  left-distributive-Σ-coprod A (λ x → B) (λ x → C)

-- Exercise 7.10

Σ-swap :
  {i j k : Level} (A : UU i) (B : UU j) (C : A → B → UU k) →
  Σ A (λ x → Σ B (C x)) → Σ B (λ y → Σ A (λ x → C x y))
Σ-swap A B C t = pair (pr1 (pr2 t)) (pair (pr1 t) (pr2 (pr2 t)))

Σ-swap' :
  {i j k : Level} (A : UU i) (B : UU j) (C : A → B → UU k) →
  Σ B (λ y → Σ A (λ x → C x y)) → Σ A (λ x → Σ B (C x))
Σ-swap' A B C = Σ-swap B A (λ y x → C x y)

Σ-swap-swap :
  {i j k : Level} (A : UU i) (B : UU j) (C : A → B → UU k) →
  ((Σ-swap' A B C) ∘ (Σ-swap A B C)) ~ id
Σ-swap-swap A B C (pair x (pair y z)) = refl

abstract
  is-equiv-Σ-swap :
    {i j k : Level} (A : UU i) (B : UU j) (C : A → B → UU k) →
    is-equiv (Σ-swap A B C)
  is-equiv-Σ-swap A B C =
    is-equiv-has-inverse
      ( Σ-swap' A B C)
      ( Σ-swap-swap B A (λ y x → C x y))
      ( Σ-swap-swap A B C)

--------------------------------------------------------------------------------

-- Section 9.3 The identity type of a Σ-type

-- Definition 9.3.1

Eq-Σ :
  {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) → UU (i ⊔ j)
Eq-Σ {B = B} s t = Σ (Id (pr1 s) (pr1 t)) (λ α → Id (tr B α (pr2 s)) (pr2 t))

-- Lemma 9.3.2

reflexive-Eq-Σ :
  {i j : Level} {A : UU i} {B : A → UU j} (s : Σ A B) → Eq-Σ s s
reflexive-Eq-Σ (pair a b) = pair refl refl

-- Definition 9.3.3

pair-eq :
  {i j : Level} {A : UU i} {B : A → UU j} {s t : Σ A B} →
  (Id s t) → Eq-Σ s t
pair-eq {s = s} refl = reflexive-Eq-Σ s

-- Theorem 9.3.4

eq-pair :
  {i j : Level} {A : UU i} {B : A → UU j} {s t : Σ A B} →
  (α : Id (pr1 s) (pr1 t)) → Id (tr B α (pr2 s)) (pr2 t) → Id s t
eq-pair {B = B} {pair x y} {pair .x .y} refl refl = refl

eq-pair' :
  {i j : Level} {A : UU i} {B : A → UU j} {s t : Σ A B} →
  Eq-Σ s t → Id s t
eq-pair' (pair α β) = eq-pair α β

isretr-pair-eq :
  {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) →
  ((pair-eq {s = s} {t}) ∘ (eq-pair' {s = s} {t})) ~ id {A = Eq-Σ s t}
isretr-pair-eq (pair x y) (pair .x .y) (pair refl refl) = refl

issec-pair-eq :
  {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) →
  ((eq-pair' {s = s} {t}) ∘ (pair-eq {s = s} {t})) ~ id
issec-pair-eq (pair x y) .(pair x y) refl = refl

abstract
  is-equiv-eq-pair :
    {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) →
    is-equiv (eq-pair' {s = s} {t})
  is-equiv-eq-pair s t =
    is-equiv-has-inverse
      ( pair-eq)
      ( issec-pair-eq s t)
      ( isretr-pair-eq s t)

abstract
  is-equiv-pair-eq :
    {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) →
    is-equiv (pair-eq {s = s} {t})
  is-equiv-pair-eq s t =
    is-equiv-has-inverse
      ( eq-pair')
      ( isretr-pair-eq s t)
      ( issec-pair-eq s t)

η-pair :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (t : Σ A B) →
  Id (pair (pr1 t) (pr2 t)) t
η-pair t = eq-pair refl refl

{- For our convenience, we repeat the above argument for cartesian products. -}

Eq-prod :
  {i j : Level} {A : UU i} {B : UU j} (s t : A × B) → UU (i ⊔ j)
Eq-prod s t = (Id (pr1 s) (pr1 t)) × (Id (pr2 s) (pr2 t))

{- We also define a function eq-pair-triv, which is like eq-pair but simplified 
   for the case where B is just a type. -}

eq-pair-triv' :
  {i j : Level} {A : UU i} {B : UU j} (s t : prod A B) →
  Eq-prod s t → Id s t
eq-pair-triv' (pair x y) (pair .x .y) (pair refl refl) = refl

eq-pair-triv :
  {i j : Level} {A : UU i} {B : UU j} {s t : prod A B} →
  Eq-prod s t → Id s t
eq-pair-triv {s = s} {t} = eq-pair-triv' s t

{- Ideally, we would use the 3-for-2 property of equivalences to show that 
   eq-pair-triv is an equivalence, using that eq-pair is an equivalence. 
   Indeed, there is an equivalence 
   
     (Id x x') × (Id y y') → Σ (Id x x') (λ p → Id (tr (λ x → B) p y) y'). 

   However, to show that this map is an equivalence we either give a direct 
   proof (in which case we might as well have given a direct proof that 
   eq-pair-triv is an equivalence), or we use the fact that it is the induced 
   map on total spaces of a fiberwise equivalence (the topic of Lecture 8). 
   Thus it seems that a direct proof showing that eq-pair-triv is an 
   equivalence is quickest for now. -}

pair-eq-triv' :
  {i j : Level} {A : UU i} {B : UU j} (s t : prod A B) →
  Id s t → Eq-prod s t
pair-eq-triv' s t α = pair (ap pr1 α) (ap pr2 α)

isretr-pair-eq-triv' :
  {i j : Level} {A : UU i} {B : UU j} (s t : prod A B) →
  ((pair-eq-triv' s t) ∘ (eq-pair-triv' s t)) ~ id
isretr-pair-eq-triv' (pair x y) (pair .x .y) (pair refl refl) = refl

issec-pair-eq-triv' :
  {i j : Level} {A : UU i} {B : UU j} (s t : prod A B) →
  ((eq-pair-triv' s t) ∘ (pair-eq-triv' s t)) ~ id
issec-pair-eq-triv' (pair x y) (pair .x .y) refl = refl

abstract
  is-equiv-eq-pair-triv' :
    {i j : Level} {A : UU i} {B : UU j} (s t : prod A B) →
    is-equiv (eq-pair-triv' s t)
  is-equiv-eq-pair-triv' s t =
    is-equiv-has-inverse
      ( pair-eq-triv' s t)
      ( issec-pair-eq-triv' s t)
      ( isretr-pair-eq-triv' s t)
      
--------------------------------------------------------------------------------

-- The Maybe modality
Maybe : {l : Level} → UU l → UU l
Maybe X = coprod X unit

unit-Maybe : {l : Level} {X : UU l} → X → Maybe X
unit-Maybe = inl

is-injective-inl :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → is-injective (inl {A = X} {B = Y})
is-injective-inl {l1} {l2} {X} {Y} {x} {y} p =
  map-inv-raise (Eq-coprod-eq X Y (inl x) (inl y) p)

is-injective-inr :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → is-injective (inr {A = X} {B = Y})
is-injective-inr {l1} {l2} {X} {Y} {x} {y} p =
  map-inv-raise (Eq-coprod-eq X Y (inr x) (inr y) p)

is-injective-unit-Maybe :
  {l : Level} {X : UU l} → is-injective (unit-Maybe {X = X})
is-injective-unit-Maybe = is-injective-inl

-- The exception
exception-Maybe : {l : Level} {X : UU l} → Maybe X
exception-Maybe {l} {X} = inr star

-- The is-exception predicate
is-exception-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-exception-Maybe {l} {X} x = Id x exception-Maybe

-- The is-exception predicate is decidable
is-decidable-is-exception-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-decidable (is-exception-Maybe x)
is-decidable-is-exception-Maybe {l} {X} (inl x) =
  inr
    (λ p → ex-falso (map-inv-raise (Eq-coprod-eq X unit (inl x) (inr star) p)))
is-decidable-is-exception-Maybe (inr star) = inl refl

-- The is-not-exception predicate
is-not-exception-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-not-exception-Maybe x = ¬ (is-exception-Maybe x)

is-not-exception-unit-Maybe :
  {l : Level} {X : UU l} (x : X) → is-not-exception-Maybe (unit-Maybe x)
is-not-exception-unit-Maybe {l} {X} x = neq-inl-inr x star

-- The is-not-exception predicate is decidable
is-decidable-is-not-exception-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-decidable (is-not-exception-Maybe x)
is-decidable-is-not-exception-Maybe x =
  is-decidable-neg (is-decidable-is-exception-Maybe x)

-- The is-value predicate
is-value-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-value-Maybe {l} {X} x = Σ X (λ y → Id (inl y) x)

value-is-value-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-value-Maybe x → X
value-is-value-Maybe x = pr1

eq-is-value-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) (H : is-value-Maybe x) →
  Id (inl (value-is-value-Maybe x H)) x
eq-is-value-Maybe x H = pr2 H

-- The decision procedure whether something is a value or an exception
decide-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) →
  coprod (is-value-Maybe x) (is-exception-Maybe x)
decide-Maybe (inl x) = inl (pair x refl)
decide-Maybe (inr star) = inr refl

-- If a point is not an exception, then it is a value
is-value-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) →
  is-not-exception-Maybe x → is-value-Maybe x
is-value-is-not-exception-Maybe x H =
  map-right-unit-law-coprod-is-empty (is-value-Maybe x) (is-exception-Maybe x) H (decide-Maybe x)

value-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) → is-not-exception-Maybe x → X
value-is-not-exception-Maybe x H =
  value-is-value-Maybe x (is-value-is-not-exception-Maybe x H)

eq-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) (H : is-not-exception-Maybe x) →
  Id (inl (value-is-not-exception-Maybe x H)) x
eq-is-not-exception-Maybe x H =
  eq-is-value-Maybe x (is-value-is-not-exception-Maybe x H)

-- If a point is a value, then it is not an exception
is-not-exception-is-value-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) →
  is-value-Maybe x → is-not-exception-Maybe x
is-not-exception-is-value-Maybe {l1} {X} .(inl x) (pair x refl) =
  is-not-exception-unit-Maybe x

-- If e is an equivalence and e (inl x) is an exception, then e exception is
-- not an exception. In the proof we see that we only need a section-retraction
-- pair, not a full equivalence.
is-not-exception-map-equiv-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-exception-Maybe (map-equiv e (inl x)) →
  is-not-exception-Maybe (map-equiv e exception-Maybe)
is-not-exception-map-equiv-exception-Maybe {l1} {l2} {X} {Y} e x p q =
  is-not-exception-unit-Maybe x (is-injective-map-equiv e (p ∙ inv q))

-- If e (inl x) is an exception, then e exception is a value
is-value-map-equiv-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-exception-Maybe (map-equiv e (inl x)) →
  is-value-Maybe (map-equiv e exception-Maybe)
is-value-map-equiv-exception-Maybe e x H =
  is-value-is-not-exception-Maybe
    ( map-equiv e exception-Maybe)
    ( is-not-exception-map-equiv-exception-Maybe e x H)

value-map-equiv-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-exception-Maybe (map-equiv e (inl x)) → Y
value-map-equiv-exception-Maybe e x H =
  value-is-value-Maybe
    ( map-equiv e exception-Maybe)
    ( is-value-map-equiv-exception-Maybe e x H)

comp-map-equiv-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  (H : is-exception-Maybe (map-equiv e (inl x))) →
  Id ( inl (value-map-equiv-exception-Maybe e x H))
     ( map-equiv e exception-Maybe)
comp-map-equiv-exception-Maybe e x H =
  eq-is-value-Maybe
    ( map-equiv e exception-Maybe)
    ( is-value-map-equiv-exception-Maybe e x H)

-- An equivalence e : Maybe X ≃ Maybe Y induces a map X → Y. We don't use
-- with-abstraction to keep full control over the definitional equalities, so
-- we give the definition in two steps. After the definition is complete, we
-- also prove two computation rules. Since we will prove computation rules, we
-- make the definition abstract.

map-equiv-equiv-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y)
  (x : X) (u : Maybe Y) (p : Id (map-equiv e (inl x)) u) → Y
map-equiv-equiv-Maybe' e x (inl y) p = y
map-equiv-equiv-Maybe' e x (inr star) p =
  value-map-equiv-exception-Maybe e x p

map-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) → X → Y
map-equiv-equiv-Maybe e x =
  map-equiv-equiv-Maybe' e x (map-equiv e (inl x)) refl

comp-map-equiv-equiv-is-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  (u : Maybe Y) (p : Id (map-equiv e (inl x)) u) →
  is-exception-Maybe (map-equiv e (inl x)) →
  Id (inl (map-equiv-equiv-Maybe' e x u p)) (map-equiv e exception-Maybe)
comp-map-equiv-equiv-is-exception-Maybe' e x (inl y) p q =
  ex-falso (is-not-exception-unit-Maybe y (inv p ∙ q))
comp-map-equiv-equiv-is-exception-Maybe' e x (inr star) p q =
  comp-map-equiv-exception-Maybe e x p

comp-map-equiv-equiv-is-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-exception-Maybe (map-equiv e (inl x)) →
  Id (inl (map-equiv-equiv-Maybe e x)) (map-equiv e exception-Maybe)
comp-map-equiv-equiv-is-exception-Maybe e x =
  comp-map-equiv-equiv-is-exception-Maybe' e x (map-equiv e (inl x)) refl

comp-map-equiv-equiv-is-not-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  (u : Maybe Y) (p : Id (map-equiv e (inl x)) u) →
  is-not-exception-Maybe (map-equiv e (inl x)) →
  Id (inl (map-equiv-equiv-Maybe' e x u p)) (map-equiv e (inl x))
comp-map-equiv-equiv-is-not-exception-Maybe' e x (inl y) p H =
  inv p
comp-map-equiv-equiv-is-not-exception-Maybe' e x (inr star) p H =
  ex-falso (H p)

comp-map-equiv-equiv-is-not-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-not-exception-Maybe (map-equiv e (inl x)) →
  Id (inl (map-equiv-equiv-Maybe e x)) (map-equiv e (inl x))
comp-map-equiv-equiv-is-not-exception-Maybe e x =
  comp-map-equiv-equiv-is-not-exception-Maybe' e x (map-equiv e (inl x)) refl

-- An equivalence e : Maybe X ≃ Maybe Y induces a map Y → X
map-inv-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) → Y → X
map-inv-equiv-equiv-Maybe e =
  map-equiv-equiv-Maybe (inv-equiv e)

comp-map-inv-equiv-equiv-is-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (y : Y) →
  is-exception-Maybe (map-inv-equiv e (inl y)) →
  Id (inl (map-inv-equiv-equiv-Maybe e y)) (map-inv-equiv e exception-Maybe)
comp-map-inv-equiv-equiv-is-exception-Maybe e =
  comp-map-equiv-equiv-is-exception-Maybe (inv-equiv e)

comp-map-inv-equiv-equiv-is-not-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (y : Y) →
  ( f : is-not-exception-Maybe (map-inv-equiv e (inl y))) →
  Id (inl (map-inv-equiv-equiv-Maybe e y)) (map-inv-equiv e (inl y))
comp-map-inv-equiv-equiv-is-not-exception-Maybe e =
  comp-map-equiv-equiv-is-not-exception-Maybe (inv-equiv e)
    
-- map-inv-equiv-equiv-Maybe e is a section of map-equiv-equiv-Maybe e.
issec-map-inv-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) →
  (map-equiv-equiv-Maybe e ∘ map-inv-equiv-equiv-Maybe e) ~ id
issec-map-inv-equiv-equiv-Maybe e y with
  is-decidable-is-exception-Maybe (map-inv-equiv e (inl y))
... | inl p =
  is-injective-unit-Maybe
    ( ( comp-map-equiv-equiv-is-exception-Maybe e
        ( map-inv-equiv-equiv-Maybe e y)
        ( ( ap
            ( map-equiv e)
            ( comp-map-inv-equiv-equiv-is-exception-Maybe e y p)) ∙
          ( issec-map-inv-equiv e exception-Maybe))) ∙
      ( ( ap (map-equiv e) (inv p)) ∙
        ( issec-map-inv-equiv e (inl y))))
... | inr f =
  is-injective-unit-Maybe
    ( ( comp-map-equiv-equiv-is-not-exception-Maybe e
        ( map-inv-equiv-equiv-Maybe e y)
        ( is-not-exception-is-value-Maybe
          ( map-equiv e (inl (map-inv-equiv-equiv-Maybe e y)))
          ( pair y
            ( inv
              ( ( ap
                  ( map-equiv e)
                  ( comp-map-inv-equiv-equiv-is-not-exception-Maybe e y f)) ∙
                ( issec-map-inv-equiv e (inl y))))))) ∙
      ( ( ap
          ( map-equiv e)
          ( comp-map-inv-equiv-equiv-is-not-exception-Maybe e y f)) ∙
        ( issec-map-inv-equiv e (inl y))))

{-
-- Alternatively, we can proceed in the spirit of the definition, but that leads
-- to cases where we have to reason by contradiction, that are avoided otherwise
issec-map-inv-equiv-equiv-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (y : Y) →
  (u : Maybe X) (p : Id (map-inv-equiv e (inl y)) u) (v : Maybe Y)
  (q : Id (map-equiv e (inl (map-equiv-equiv-Maybe' (inv-equiv e) y u p))) v) →
  Id ( map-equiv-equiv-Maybe' e
       ( map-equiv-equiv-Maybe' (inv-equiv e) y u p) v q)
     ( y)
issec-map-inv-equiv-equiv-Maybe' e y (inl x) p (inl y') q =
  is-injective-unit-Maybe (inv (map-inv-eq-transpose-equiv' e p ∙ q))
issec-map-inv-equiv-equiv-Maybe' e y (inl x) p (inr star) q =
  ex-falso (is-not-exception-unit-Maybe y (map-inv-eq-transpose-equiv' e p ∙ q))
issec-map-inv-equiv-equiv-Maybe' e y (inr star) p (inl y') q =
  ex-falso
    ( is-not-exception-unit-Maybe y'
      ( ( ( inv q) ∙
          ( ap
            ( map-equiv e)
            ( comp-map-equiv-exception-Maybe (inv-equiv e) y p))) ∙
        ( issec-map-inv-equiv e exception-Maybe))) 
issec-map-inv-equiv-equiv-Maybe' e y (inr star) p (inr star) q =
  is-injective-unit-Maybe
    ( ( comp-map-equiv-exception-Maybe e
        ( map-equiv-equiv-Maybe' (inv-equiv e) y (inr star) p)
        ( q)) ∙
      ( ( ap (map-equiv e) (inv p)) ∙
        ( issec-map-inv-equiv e (inl y))))

issec-map-inv-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) →
  (map-equiv-equiv-Maybe e ∘ map-inv-equiv-equiv-Maybe e) ~ id
issec-map-inv-equiv-equiv-Maybe e y =
  issec-map-inv-equiv-equiv-Maybe' e y
    ( map-inv-equiv e (inl y)) refl
    ( map-equiv e (inl (map-inv-equiv-equiv-Maybe e y))) refl
-}

-- The map map-inv-equiv-equiv e is a retraction of the map map-equiv-equiv
isretr-map-inv-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) →
  (map-inv-equiv-equiv-Maybe e ∘ map-equiv-equiv-Maybe e) ~ id
isretr-map-inv-equiv-equiv-Maybe e x with
  is-decidable-is-exception-Maybe (map-equiv e (inl x))
... | inl p =
  is-injective-unit-Maybe
    ( ( comp-map-inv-equiv-equiv-is-exception-Maybe e
        ( map-equiv-equiv-Maybe e x)
        ( ( ap ( map-inv-equiv e)
               ( comp-map-equiv-equiv-is-exception-Maybe e x p)) ∙
          ( isretr-map-inv-equiv e exception-Maybe))) ∙
      ( ( ap (map-inv-equiv e) (inv p)) ∙
        ( isretr-map-inv-equiv e (inl x))))
... | inr f =
  is-injective-unit-Maybe
    ( ( comp-map-inv-equiv-equiv-is-not-exception-Maybe e
        ( map-equiv-equiv-Maybe e x)
        ( is-not-exception-is-value-Maybe
          ( map-inv-equiv e (inl (map-equiv-equiv-Maybe e x)))
          ( pair x
            ( inv
              ( ( ap (map-inv-equiv e)
                     ( comp-map-equiv-equiv-is-not-exception-Maybe e x f)) ∙
                ( isretr-map-inv-equiv e (inl x))))))) ∙
      ( ( ap ( map-inv-equiv e)
             ( comp-map-equiv-equiv-is-not-exception-Maybe e x f)) ∙
        ( isretr-map-inv-equiv e (inl x))))

-- The function map-equiv-equiv-Maybe is an equivalence

is-equiv-map-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) →
  is-equiv (map-equiv-equiv-Maybe e)
is-equiv-map-equiv-equiv-Maybe e =
  is-equiv-has-inverse
    ( map-inv-equiv-equiv-Maybe e)
    ( issec-map-inv-equiv-equiv-Maybe e)
    ( isretr-map-inv-equiv-equiv-Maybe e)

equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (Maybe X ≃ Maybe Y) → (X ≃ Y)
equiv-equiv-Maybe e =
  pair (map-equiv-equiv-Maybe e) (is-equiv-map-equiv-equiv-Maybe e)

is-injective-Fin : {k l : ℕ} → (Fin k ≃ Fin l) → Id k l
is-injective-Fin {zero-ℕ} {zero-ℕ} e = refl
is-injective-Fin {zero-ℕ} {succ-ℕ l} e = ex-falso (map-inv-equiv e zero-Fin)
is-injective-Fin {succ-ℕ k} {zero-ℕ} e = ex-falso (map-equiv e zero-Fin)
is-injective-Fin {succ-ℕ k} {succ-ℕ l} e =
  ap succ-ℕ (is-injective-Fin (equiv-equiv-Maybe e))

--------------------------------------------------------------------------------

-- Exercises

-- Exercise 9.1

{- We show that inv is an equivalence. -}

inv-inv :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) → Id (inv (inv p)) p
inv-inv refl = refl

abstract
  is-equiv-inv :
    {i : Level} {A : UU i} (x y : A) →
    is-equiv (λ (p : Id x y) → inv p)
  is-equiv-inv x y =
    is-equiv-has-inverse inv inv-inv inv-inv

equiv-inv :
  {i : Level} {A : UU i} (x y : A) → (Id x y) ≃ (Id y x)
equiv-inv x y = pair inv (is-equiv-inv x y)

{- We show that concat p is an equivalence, for any path p. -}

inv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
  (Id x z) → (Id y z)
inv-concat p = concat (inv p)

isretr-inv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
  ((inv-concat p z) ∘ (concat p z)) ~ id
isretr-inv-concat refl z q = refl

issec-inv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
  ((concat p z) ∘ (inv-concat p z)) ~ id
issec-inv-concat refl z refl = refl

abstract
  is-equiv-concat :
    {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
    is-equiv (concat p z)
  is-equiv-concat p z =
    is-equiv-has-inverse
      ( inv-concat p z)
      ( issec-inv-concat p z)
      ( isretr-inv-concat p z)

equiv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
  Id y z ≃ Id x z
equiv-concat p z = pair (concat p z) (is-equiv-concat p z)

{- We show that concat' q is an equivalence, for any path q. -}

concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} → Id y z → Id x y → Id x z
concat' x q p = p ∙ q

inv-concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} → Id y z →
  Id x z → Id x y
inv-concat' x q = concat' x (inv q)

isretr-inv-concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} (q : Id y z) →
  ((inv-concat' x q) ∘ (concat' x q)) ~ id
isretr-inv-concat' x refl refl = refl

issec-inv-concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} (q : Id y z) →
  ((concat' x q) ∘ (inv-concat' x q)) ~ id
issec-inv-concat' x refl refl = refl

abstract
  is-equiv-concat' :
    {i : Level} {A : UU i} (x : A) {y z : A} (q : Id y z) →
    is-equiv (concat' x q)
  is-equiv-concat' x q =
    is-equiv-has-inverse
      ( inv-concat' x q)
      ( issec-inv-concat' x q)
      ( isretr-inv-concat' x q)

equiv-concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} (q : Id y z) →
  Id x y ≃ Id x z
equiv-concat' x q = pair (concat' x q) (is-equiv-concat' x q)

{- We show that tr B p is an equivalence, for an path p and any type family B.
   -}
   
inv-tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A} →
  Id x y → B y → B x
inv-tr B p = tr B (inv p)

isretr-inv-tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A}
  (p : Id x y) → ((inv-tr B p ) ∘ (tr B p)) ~ id
isretr-inv-tr B refl b = refl

issec-inv-tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A}
  (p : Id x y) → ((tr B p) ∘ (inv-tr B p)) ~ id
issec-inv-tr B refl b = refl

abstract
  is-equiv-tr :
    {i j : Level} {A : UU i} (B : A → UU j) {x y : A}
    (p : Id x y) → is-equiv (tr B p)
  is-equiv-tr B p =
    is-equiv-has-inverse
      ( inv-tr B p)
      ( issec-inv-tr B p)
      ( isretr-inv-tr B p)

equiv-tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A}
  (p : Id x y) → (B x) ≃ (B y)
equiv-tr B p = pair (tr B p) (is-equiv-tr B p)

-- Exercise 9.2

abstract
  not-equiv-const :
    (b : bool) → ¬ (is-equiv (const bool bool b))
  not-equiv-const true (pair (pair s issec) (pair r isretr)) =
    neq-false-true-𝟚 (inv (issec false))
  not-equiv-const false (pair (pair s issec) (pair r isretr)) =
    neq-false-true-𝟚 (issec true)

-- Exercise 9.3

-- Exercise 9.3(a)

abstract
  is-equiv-htpy :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} (g : A → B) →
    f ~ g → is-equiv g → is-equiv f
  is-equiv-htpy g H (pair (pair gs issec) (pair gr isretr)) =
    pair
      ( pair gs ((H ·r gs) ∙h issec))
      ( pair gr ((gr ·l H) ∙h isretr))

abstract
  is-equiv-htpy' :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B) {g : A → B} →
    f ~ g → is-equiv f → is-equiv g
  is-equiv-htpy' f H = is-equiv-htpy f (inv-htpy H)

-- Exercise 9.3(b)

inv-htpy-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f f' : A → B} (H : f ~ f') →
  (is-equiv-f : is-equiv f) (is-equiv-f' : is-equiv f') →
  (map-inv-is-equiv is-equiv-f) ~ (map-inv-is-equiv is-equiv-f')
inv-htpy-is-equiv H is-equiv-f is-equiv-f' b =
  ( inv (isretr-map-inv-is-equiv is-equiv-f' (map-inv-is-equiv is-equiv-f b))) ∙
  ( ap (map-inv-is-equiv is-equiv-f')
    ( ( inv (H (map-inv-is-equiv is-equiv-f b))) ∙
      ( issec-map-inv-is-equiv is-equiv-f b)))

-- Exercise 9.4

-- Exercise 9.4(a)

{- Exercise 9.4 (a) asks to show that, given a commuting triangle f ~ g ∘ h and
   a section s of h, we get a new commuting triangle g ~ f ∘ s. Moreover, under
   the same assumptions it follows that f has a section if and only if g has a 
   section. -}

triangle-section :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) (S : sec h) →
  g ~ (f ∘ (pr1 S))
triangle-section f g h H (pair s issec) =
  inv-htpy (( H ·r s) ∙h (g ·l issec))

section-comp :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  sec h → sec f → sec g
section-comp f g h H sec-h sec-f =
  pair (h ∘ (pr1 sec-f)) ((inv-htpy (H ·r (pr1 sec-f))) ∙h (pr2 sec-f))

section-comp' :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  sec h → sec g → sec f
section-comp' f g h H sec-h sec-g =
  pair
    ( (pr1 sec-h) ∘ (pr1 sec-g))
    ( ( H ·r ((pr1 sec-h) ∘ (pr1 sec-g))) ∙h
      ( ( g ·l ((pr2 sec-h) ·r (pr1 sec-g))) ∙h ((pr2 sec-g))))

-- Exercise 9.4(b)

{- Exercise 9.4 (b) is dual to exercise 9.4 (a). It asks to show that, given a 
   commuting triangle f ~ g ∘ h and a retraction r of g, we get a new commuting
   triangle h ~ r ∘ f. Moreover, under these assumptions it also follows that f
   has a retraction if and only if h has a retraction. -}

triangle-retraction :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) (R : retr g) →
  h ~ ((pr1 R) ∘ f)
triangle-retraction f g h H (pair r isretr) =
  inv-htpy (( r ·l H) ∙h (isretr ·r h))

retraction-comp :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  retr g → retr f → retr h
retraction-comp f g h H retr-g retr-f =
  pair
    ( (pr1 retr-f) ∘ g)
    ( (inv-htpy ((pr1 retr-f) ·l H)) ∙h (pr2 retr-f))

retraction-comp' :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  retr g → retr h → retr f
retraction-comp' f g h H retr-g retr-h =
  pair
    ( (pr1 retr-h) ∘ (pr1 retr-g))
    ( ( ((pr1 retr-h) ∘ (pr1 retr-g)) ·l H) ∙h
      ( ((pr1 retr-h) ·l ((pr2 retr-g) ·r h)) ∙h (pr2 retr-h)))

-- Exercise 9.4(c)

{- In Exercise 9.4 (c) we use the constructions of parts (a) and (b) to derive 
   the 3-for-2 property of equivalences. -}

abstract
  is-equiv-comp :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-equiv h → is-equiv g → is-equiv f
  is-equiv-comp f g h H (pair sec-h retr-h) (pair sec-g retr-g) =
    pair
      ( section-comp' f g h H sec-h sec-g)
      ( retraction-comp' f g h H retr-g retr-h)

abstract
  is-equiv-comp' :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k} (g : B → X) (h : A → B) →
    is-equiv h → is-equiv g → is-equiv (g ∘ h)
  is-equiv-comp' g h = is-equiv-comp (g ∘ h) g h refl-htpy

equiv-comp :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k} →
  (B ≃ X) → (A ≃ B) → (A ≃ X)
equiv-comp g h =
  pair ((pr1 g) ∘ (pr1 h)) (is-equiv-comp' (pr1 g) (pr1 h) (pr2 h) (pr2 g))

_∘e_ :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k} →
  (B ≃ X) → (A ≃ B) → (A ≃ X)
_∘e_ = equiv-comp

abstract
  is-equiv-left-factor :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-equiv f → is-equiv h → is-equiv g
  is-equiv-left-factor f g h H
    ( pair sec-f retr-f)
    ( pair (pair sh sh-issec) retr-h) =
    pair
      ( section-comp f g h H (pair sh sh-issec) sec-f)
      ( retraction-comp' g f sh
        ( triangle-section f g h H (pair sh sh-issec))
        ( retr-f)
        ( pair h sh-issec))

abstract
  is-equiv-left-factor' :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k} (g : B → X) (h : A → B) →
    is-equiv (g ∘ h) → is-equiv h → is-equiv g
  is-equiv-left-factor' g h =
    is-equiv-left-factor (g ∘ h) g h refl-htpy

abstract
  is-equiv-right-factor :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-equiv g → is-equiv f → is-equiv h
  is-equiv-right-factor f g h H
    ( pair sec-g (pair rg rg-isretr))
    ( pair sec-f retr-f) =
    pair
      ( section-comp' h rg f
        ( triangle-retraction f g h H (pair rg rg-isretr))
        ( sec-f)
        ( pair g rg-isretr))
      ( retraction-comp f g h H (pair rg rg-isretr) retr-f)

abstract
  is-equiv-right-factor' :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k} (g : B → X) (h : A → B) → 
    is-equiv g → is-equiv (g ∘ h) → is-equiv h
  is-equiv-right-factor' g h =
    is-equiv-right-factor (g ∘ h) g h refl-htpy

abstract
  is-equiv-is-section-is-equiv :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} {g : B → A} →
    is-equiv f → (f ∘ g) ~ id → is-equiv g
  is-equiv-is-section-is-equiv {B = B} {f = f} {g = g} is-equiv-f H =
    is-equiv-right-factor id f g (inv-htpy H) is-equiv-f is-equiv-id

abstract
  is-equiv-is-retraction-is-equiv :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} {g : B → A} →
    is-equiv f  → (g ∘ f) ~ id → is-equiv g
  is-equiv-is-retraction-is-equiv {A = A} {f = f} {g = g} is-equiv-f H =
    is-equiv-left-factor id g f (inv-htpy H) is-equiv-id is-equiv-f
    
-- Exercise 9.5

map-inv-is-cyclic-map :
  {l : Level} {X : UU l} (f : X → X) (H : is-cyclic-map f) → X → X
map-inv-is-cyclic-map f H x =
  iterate (length-path-is-cyclic-map H (f x) x) f x

issec-map-inv-is-cyclic-map :
  {l : Level} {X : UU l} (f : X → X) (H : is-cyclic-map f) →
  (f ∘ map-inv-is-cyclic-map f H) ~ id
issec-map-inv-is-cyclic-map f H x =
  ( iterate-succ-ℕ (length-path-is-cyclic-map H (f x) x) f x) ∙
  ( eq-is-cyclic-map H (f x) x)

isretr-map-inv-is-cyclic-map :
  {l : Level} {X : UU l} (f : X → X) (H : is-cyclic-map f) →
  (map-inv-is-cyclic-map f H ∘ f) ~ id
isretr-map-inv-is-cyclic-map f H x =
  ( ap ( iterate (length-path-is-cyclic-map H (f (f x)) (f x)) f ∘ f)
       ( inv (eq-is-cyclic-map H (f x) x))) ∙
  ( ( ap ( iterate (length-path-is-cyclic-map H (f (f x)) (f x)) f)
         ( iterate-succ-ℕ (length-path-is-cyclic-map H (f x) x) f (f x))) ∙
    ( ( iterate-iterate
        ( length-path-is-cyclic-map H (f (f x)) (f x))
        ( length-path-is-cyclic-map H (f x) x) f (f (f x))) ∙
      ( ( ap ( iterate (length-path-is-cyclic-map H (f x) x) f)
           ( eq-is-cyclic-map H (f (f x)) (f x))) ∙
        ( eq-is-cyclic-map H (f x) x))))

is-equiv-is-cyclic-map :
  {l : Level} {X : UU l} (f : X → X) → is-cyclic-map f → is-equiv f
is-equiv-is-cyclic-map f H =
  is-equiv-has-inverse
    ( map-inv-is-cyclic-map f H)
    ( issec-map-inv-is-cyclic-map f H)
    ( isretr-map-inv-is-cyclic-map f H)

-- Exercise 9.6

{- In this exercise we construct an equivalence from A + B to B + A, showing 
   that the coproduct is commutative. -}

swap-coprod :
  {i j : Level} (A : UU i) (B : UU j) → coprod A B → coprod B A
swap-coprod A B (inl x) = inr x
swap-coprod A B (inr x) = inl x

swap-swap-coprod :
  {i j : Level} (A : UU i) (B : UU j) →
  ((swap-coprod B A) ∘ (swap-coprod A B)) ~ id
swap-swap-coprod A B (inl x) = refl
swap-swap-coprod A B (inr x) = refl

abstract
  is-equiv-swap-coprod :
    {i j : Level} (A : UU i) (B : UU j) → is-equiv (swap-coprod A B)
  is-equiv-swap-coprod A B =
    is-equiv-has-inverse
      ( swap-coprod B A)
      ( swap-swap-coprod B A)
      ( swap-swap-coprod A B)

equiv-swap-coprod :
  {i j : Level} (A : UU i) (B : UU j) → coprod A B ≃ coprod B A
equiv-swap-coprod A B = pair (swap-coprod A B) (is-equiv-swap-coprod A B)

swap-prod :
  {i j : Level} (A : UU i) (B : UU j) → prod A B → prod B A
swap-prod A B t = pair (pr2 t) (pr1 t)

swap-swap-prod :
  {i j : Level} (A : UU i) (B : UU j) →
  ((swap-prod B A) ∘ (swap-prod A B)) ~ id
swap-swap-prod A B (pair x y) = refl

abstract
  is-equiv-swap-prod :
    {i j : Level} (A : UU i) (B : UU j) →
    is-equiv (swap-prod A B)
  is-equiv-swap-prod A B =
    is-equiv-has-inverse
      ( swap-prod B A)
      ( swap-swap-prod B A)
      ( swap-swap-prod A B)

equiv-swap-prod :
  {i j : Level} (A : UU i) (B : UU j) → (A × B) ≃ (B × A)
equiv-swap-prod A B = pair (swap-prod A B) (is-equiv-swap-prod A B)

-- Exercise 9.8

{- In this exercise we show that if A is a retract of B, then so are its 
   identity types. -}

ap-retraction :
  {i j : Level} {A : UU i} {B : UU j}
  (i : A → B) (r : B → A) (H : (r ∘ i) ~ id)
  (x y : A) → Id (i x) (i y) → Id x y
ap-retraction i r H x y p =
    ( inv (H x)) ∙ ((ap r p) ∙ (H y))

isretr-ap-retraction :
  {i j : Level} {A : UU i} {B : UU j}
  (i : A → B) (r : B → A) (H : (r ∘ i) ~ id)
  (x y : A) → ((ap-retraction i r H x y) ∘ (ap i {x} {y})) ~ id
isretr-ap-retraction i r H x .x refl = left-inv (H x)

retr-ap :
  {i j : Level} {A : UU i} {B : UU j} (i : A → B) →
  retr i → (x y : A) → retr (ap i {x} {y})
retr-ap i (pair r H) x y =
  pair (ap-retraction i r H x y) (isretr-ap-retraction i r H x y)

Id-retract-of-Id :
  {i j : Level} {A : UU i} {B : UU j} (R : A retract-of B) →
  (x y : A) → (Id x y) retract-of (Id (pr1 R x) (pr1 R y))
Id-retract-of-Id (pair i (pair r H)) x y =
  pair
    ( ap i {x} {y})
    ( retr-ap i (pair r H) x y)

-- Exercise 9.9

-- Exercise 9.11

abstract
  is-equiv-add-ℤ-right :
    (x : ℤ) → is-equiv (add-ℤ x)
  is-equiv-add-ℤ-right x =
    is-equiv-has-inverse
      ( add-ℤ (neg-ℤ x))
      ( λ y →
        ( inv (associative-add-ℤ x (neg-ℤ x) y)) ∙
        ( ap (λ t → add-ℤ t y) (right-inverse-law-add-ℤ x)))
      ( λ y →
        ( inv (associative-add-ℤ (neg-ℤ x) x y)) ∙
        ( ap (λ t → add-ℤ t y) (left-inverse-law-add-ℤ x)))

abstract
  is-equiv-add-ℤ-left :
    (y : ℤ) → is-equiv (λ x → add-ℤ x y)
  is-equiv-add-ℤ-left y =
    is-equiv-htpy (add-ℤ y)
      ( λ x → commutative-add-ℤ x y)
      ( is-equiv-add-ℤ-right y)

-- Exercise 9.12

-- Exercise 9.13

{- We construct the functoriality of coproducts. -}

htpy-map-coprod :
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  {f f' : A → A'} (H : f ~ f') {g g' : B → B'} (K : g ~ g') →
  (map-coprod f g) ~ (map-coprod f' g')
htpy-map-coprod H K (inl x) = ap inl (H x)
htpy-map-coprod H K (inr y) = ap inr (K y)

id-map-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  (map-coprod (id {A = A}) (id {A = B})) ~ id
id-map-coprod A B (inl x) = refl
id-map-coprod A B (inr x) = refl

compose-map-coprod :
  {l1 l2 l1' l2' l1'' l2'' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  {A'' : UU l1''} {B'' : UU l2''}
  (f : A → A') (f' : A' → A'') (g : B → B') (g' : B' → B'') →
  (map-coprod (f' ∘ f) (g' ∘ g)) ~
  ((map-coprod f' g') ∘ (map-coprod f g))
compose-map-coprod f f' g g' (inl x) = refl
compose-map-coprod f f' g g' (inr y) = refl

abstract
  is-equiv-map-coprod :
    {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
    {f : A → A'} {g : B → B'} →
    is-equiv f → is-equiv g → is-equiv (map-coprod f g)
  is-equiv-map-coprod {A = A} {B = B} {A' = A'} {B' = B'} {f = f} {g = g}
    (pair (pair sf issec-sf) (pair rf isretr-rf))
    (pair (pair sg issec-sg) (pair rg isretr-rg)) =
    pair
      ( pair
        ( map-coprod sf sg)
        ( ( ( inv-htpy (compose-map-coprod sf f sg g)) ∙h
            ( htpy-map-coprod issec-sf issec-sg)) ∙h
          ( id-map-coprod A' B')))
      ( pair
        ( map-coprod rf rg)
        ( ( ( inv-htpy (compose-map-coprod f rf g rg)) ∙h
            ( htpy-map-coprod isretr-rf isretr-rg)) ∙h
          ( id-map-coprod A B)))
  
equiv-coprod :
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'} →
  (A ≃ A') → (B ≃ B') → ((coprod A B) ≃ (coprod A' B'))
equiv-coprod (pair e is-equiv-e) (pair f is-equiv-f) =
  pair
    ( map-coprod e f)
    ( is-equiv-map-coprod is-equiv-e is-equiv-f)

--------------------------------------------------------------------------------

-- Extra material

abstract
  is-equiv-inv-con :
    {i : Level} {A : UU i} {x y z : A} (p : Id x y)
    (q : Id y z) (r : Id x z) → is-equiv (inv-con p q r)
  is-equiv-inv-con refl q r = is-equiv-id

equiv-inv-con :
  {i : Level} {A : UU i} {x y z : A} (p : Id x y) (q : Id y z) (r : Id x z) →
  Id (p ∙ q) r ≃ Id q ((inv p) ∙ r)
equiv-inv-con p q r = pair (inv-con p q r) (is-equiv-inv-con p q r)

abstract
  is-equiv-con-inv :
    {i : Level} {A : UU i} {x y z : A} (p : Id x y)
    (q : Id y z) (r : Id x z) → is-equiv (con-inv p q r)
  is-equiv-con-inv p refl r =
    is-equiv-comp'
      ( concat' p (inv right-unit))
      ( concat (inv right-unit) r)
      ( is-equiv-concat (inv right-unit) r)
      ( is-equiv-concat' p (inv right-unit))

equiv-con-inv :
  {i : Level} {A : UU i} {x y z : A} (p : Id x y) (q : Id y z) (r : Id x z) →
  Id (p ∙ q) r ≃ Id p (r ∙ (inv q))
equiv-con-inv p q r = pair (con-inv p q r) (is-equiv-con-inv p q r)

-- Extra constructions with homotopies

inv-htpy-con :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x} →
  (H : f ~ g) (K : g ~ h) (L : f ~ h) →
  (H ∙h K) ~ L → K ~ ((inv-htpy H) ∙h L)
inv-htpy-con H K L M x = inv-con (H x) (K x) (L x) (M x)

htpy-con-inv :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x} →
  (H : f ~ g) (K : g ~ h) (L : f ~ h) →
  (H ∙h K) ~ L → H ~ (L ∙h (inv-htpy K))
htpy-con-inv H K L M x = con-inv (H x) (K x) (L x) (M x)

htpy-ap-concat :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x} →
  (H : f ~ g) (K K' : g ~ h) →
  K ~ K' → (H ∙h K) ~ (H ∙h K')
htpy-ap-concat {g = g} {h} H K K' L x =
  ap (concat (H x) (h x)) (L x)

htpy-ap-concat' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x} →
  (H H' : f ~ g) (K : g ~ h) →
  H ~ H' → (H ∙h K) ~ (H' ∙h K)
htpy-ap-concat' H H' K L x =
  ap (concat' _ (K x)) (L x)

htpy-distributive-inv-concat :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x} →
  (H : f ~ g) (K : g ~ h) →
  (inv-htpy (H ∙h K)) ~ ((inv-htpy K) ∙h (inv-htpy H))
htpy-distributive-inv-concat H K x = distributive-inv-concat (H x) (K x)

htpy-ap-inv :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x} →
  {H H' : f ~ g} →
  H ~ H' → (inv-htpy H) ~ (inv-htpy H')
htpy-ap-inv K x = ap inv (K x)

htpy-left-whisk-inv-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {f f' : A → B} (g : B → C) (H : f ~ f') →
  (g ·l (inv-htpy H)) ~ inv-htpy (g ·l H)
htpy-left-whisk-inv-htpy g H x = ap-inv g (H x)

htpy-right-whisk-inv-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {g g' : B → C} (H : g ~ g') (f : A → B) →
  ((inv-htpy H) ·r f) ~ (inv-htpy (H ·r f))
htpy-right-whisk-inv-htpy H f = refl-htpy

--------------------------------------------------------------------------------

coprod-Fin :
  (k l : ℕ) → coprod (Fin k) (Fin l) ≃ Fin (add-ℕ k l)
coprod-Fin k zero-ℕ = right-unit-law-coprod (Fin k)
coprod-Fin k (succ-ℕ l) =
  (equiv-coprod (coprod-Fin k l) equiv-id) ∘e inv-assoc-coprod

{- We construct the functoriality of cartesian products. -}

map-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) → (A × B) → (C × D)
map-prod f g (pair a b) = pair (f a) (g b)

map-prod-pr1 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) → (pr1 ∘ (map-prod f g)) ~ (f ∘ pr1)
map-prod-pr1 f g (pair a b) = refl

map-prod-pr2 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) → (pr2 ∘ (map-prod f g)) ~ (g ∘ pr2)
map-prod-pr2 f g (pair a b) = refl

{- For our convenience we show that the functorial action of cartesian products
   preserves identity maps, compositions, homotopies, and equivalences. -}

map-prod-id :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (map-prod (id {A = A}) (id {A = B})) ~ id
map-prod-id (pair a b) = refl

map-prod-comp :
  {l1 l2 l3 l4 l5 l6 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {E : UU l5} {F : UU l6} (f : A → C) (g : B → D) (h : C → E) (k : D → F) →
  map-prod (h ∘ f) (k ∘ g) ~ ((map-prod h k) ∘ (map-prod f g))
map-prod-comp f g h k (pair a b) = refl

htpy-map-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f f' : A → C} (H : f ~ f') {g g' : B → D} (K : g ~ g') →
  map-prod f g ~ map-prod f' g'
htpy-map-prod {f = f} {f'} H {g} {g'} K (pair a b) =
  eq-pair-triv (pair (H a) (K b))

abstract
  is-equiv-map-prod :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
    (f : A → C) (g : B → D) →
    is-equiv f → is-equiv g → is-equiv (map-prod f g)
  is-equiv-map-prod f g
    ( pair (pair sf issec-sf) (pair rf isretr-rf))
    ( pair (pair sg issec-sg) (pair rg isretr-rg)) =
    pair
      ( pair
        ( map-prod sf sg)
        ( ( inv-htpy (map-prod-comp sf sg f g)) ∙h
          ( (htpy-map-prod issec-sf issec-sg) ∙h map-prod-id)))
      ( pair
        ( map-prod rf rg)
        ( ( inv-htpy (map-prod-comp f g rf rg)) ∙h
          ( (htpy-map-prod isretr-rf isretr-rg) ∙h map-prod-id)))

equiv-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A ≃ C) (g : B ≃ D) → (A × B) ≃ (C × D)
equiv-prod (pair f is-equiv-f) (pair g is-equiv-g) =
  pair (map-prod f g) (is-equiv-map-prod f g is-equiv-f is-equiv-g)

prod-Fin : (k l : ℕ) → ((Fin k) × (Fin l)) ≃ Fin (mul-ℕ k l)
prod-Fin zero-ℕ l = left-absorption-prod (Fin l)
prod-Fin (succ-ℕ k) l =
  ( ( coprod-Fin (mul-ℕ k l) l) ∘e
    ( equiv-coprod (prod-Fin k l) (left-unit-law-prod (Fin l)))) ∘e
  ( right-distributive-prod-coprod (Fin k) unit (Fin l))

--------------------------------------------------------------------------------
