{-# OPTIONS --without-K --exact-split --safe #-}

module book.10-contractible-types where

import book.09-equivalences
open book.09-equivalences public

--------------------------------------------------------------------------------

-- Section 10 Contractible types

--------------------------------------------------------------------------------

-- Section 10.1 Contractible types

{- Definition 10.1.1 -}

is-contr :
  {l : Level} → UU l → UU l
is-contr A = Σ A (λ a → (x : A) → Id a x)

abstract
  center :
    {l : Level} {A : UU l} → is-contr A → A
  center (pair c is-contr-A) = c
  
-- We make sure that the contraction is coherent in a straightforward way
eq-is-contr :
  {l : Level} {A : UU l} → is-contr A → (x y : A) → Id x y
eq-is-contr (pair c C) x y = (inv (C x)) ∙ (C y)

abstract
  contraction :
    {l : Level} {A : UU l} (is-contr-A : is-contr A) →
    (const A A (center is-contr-A) ~ id)
  contraction (pair c C) x = eq-is-contr (pair c C) c x
  
  coh-contraction :
    {l : Level} {A : UU l} (is-contr-A : is-contr A) →
    Id (contraction is-contr-A (center is-contr-A)) refl
  coh-contraction (pair c C) = left-inv (C c)

{- Remark 10.1.2 -}

{- Remark 10.1.3 -}

{- Theorem 10.1.4 -}

--------------------------------------------------------------------------------

-- Section 10.2 Singleton induction

-- We show that contractible types satisfy an induction principle akin to the induction principle of the unit type: singleton induction. This can be helpful to give short proofs of many facts.

{- Definition 10.2.1 -}

ev-pt :
  {l1 l2 : Level} {A : UU l1} (a : A) (B : A → UU l2) → ((x : A) → B x) → B a
ev-pt a B f = f a

is-singleton :
  (l : Level) {i : Level} (A : UU i) → A → UU (lsuc l ⊔ i)
is-singleton l A a = (B : A → UU l) → sec (ev-pt a B)

ind-is-singleton :
  {l1 l2 : Level} {A : UU l1} (a : A) →
  ({l : Level} → is-singleton l A a) → (B : A → UU l2) →
  B a → (x : A) → B x
ind-is-singleton a is-sing-A B = pr1 (is-sing-A B)

comp-is-singleton :
  {l1 l2 : Level} {A : UU l1} (a : A) (H : {l : Level} → is-singleton l A a) →
  (B : A → UU l2) → (ev-pt a B ∘ ind-is-singleton a H B) ~ id
comp-is-singleton a H B = pr2 (H B)

{- Theorem 10.2.3 -}

abstract
  ind-singleton-is-contr :
    {i j : Level} {A : UU i} (a : A) (is-contr-A : is-contr A) (B : A → UU j) →
    B a → (x : A) → B x
  ind-singleton-is-contr a is-contr-A B b x =
    tr B ((inv (contraction is-contr-A a)) ∙ (contraction is-contr-A x)) b
  
  comp-singleton-is-contr :
    {i j : Level} {A : UU i} (a : A) (is-contr-A : is-contr A) (B : A → UU j) →
    ((ev-pt a B) ∘ (ind-singleton-is-contr a is-contr-A B)) ~ id
  comp-singleton-is-contr a is-contr-A B b =
    ap (λ ω → tr B ω b) (left-inv (contraction is-contr-A a))

is-singleton-is-contr :
  {l1 l2 : Level} {A : UU l1} (a : A) → is-contr A → is-singleton l2 A a
is-singleton-is-contr a is-contr-A B =
  pair
    ( ind-singleton-is-contr a is-contr-A B)
    ( comp-singleton-is-contr a is-contr-A B)

abstract
  is-contr-ind-singleton :
    {i : Level} (A : UU i) (a : A) →
    ({l : Level} (P : A → UU l) → P a → (x : A) → P x) → is-contr A
  is-contr-ind-singleton A a S = pair a (S (λ x → Id a x) refl)

abstract
  is-contr-is-singleton :
    {i : Level} (A : UU i) (a : A) →
    ({l : Level} → is-singleton l A a) → is-contr A
  is-contr-is-singleton A a S = is-contr-ind-singleton A a (λ P → pr1 (S P))

abstract
  is-singleton-unit : {l : Level} → is-singleton l unit star
  is-singleton-unit B = pair ind-unit (λ b → refl)

is-contr-unit : is-contr unit
is-contr-unit = is-contr-is-singleton unit star (is-singleton-unit)

abstract
  is-singleton-total-path :
    {i l : Level} (A : UU i) (a : A) →
    is-singleton l (Σ A (λ x → Id a x)) (pair a refl)
  is-singleton-total-path A a B = pair (ind-Σ ∘ (ind-Id a _)) (λ b → refl)

abstract
  is-contr-total-path :
    {i : Level} {A : UU i} (a : A) → is-contr (Σ A (λ x → Id a x))
  is-contr-total-path {A = A} a =
    is-contr-is-singleton _ _ (is-singleton-total-path A a)

--------------------------------------------------------------------------------

-- Section 10.3 Contractible maps

{- Definition 10.3.1 -}

fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (b : B) → UU (i ⊔ j)
fib f b = Σ _ (λ x → Id (f x) b)

fib' :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (b : B) → UU (i ⊔ j)
fib' f b = Σ _ (λ x → Id b (f x))

{- Definition 10.3.2 -}

Eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  fib f y → fib f y → UU (i ⊔ j)
Eq-fib f y s t =
  Σ (Id (pr1 s) (pr1 t)) (λ α → Id ((ap f α) ∙ (pr2 t)) (pr2 s))

{- Proposition 10.3.3 -}

reflexive-Eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  (s : fib f y) → Eq-fib f y s s
reflexive-Eq-fib f y s = pair refl refl

Eq-fib-eq :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  {s t : fib f y} → (Id s t) → Eq-fib f y s t
Eq-fib-eq f y {s} refl = reflexive-Eq-fib f y s

eq-Eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  {s t : fib f y} → Eq-fib f y s t → Id s t
eq-Eq-fib f y {pair x p} {pair .x .p} (pair refl refl) = refl

issec-eq-Eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  {s t : fib f y} → ((Eq-fib-eq f y {s} {t}) ∘ (eq-Eq-fib f y {s} {t})) ~ id
issec-eq-Eq-fib f y {pair x p} {pair .x .p} (pair refl refl) = refl

isretr-eq-Eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  {s t : fib f y} → ((eq-Eq-fib f y {s} {t}) ∘ (Eq-fib-eq f y {s} {t})) ~ id
isretr-eq-Eq-fib f y {pair x p} {.(pair x p)} refl = refl

abstract
  is-equiv-Eq-fib-eq :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
    {s t : fib f y} → is-equiv (Eq-fib-eq f y {s} {t})
  is-equiv-Eq-fib-eq f y {s} {t} =
    is-equiv-has-inverse
      ( eq-Eq-fib f y)
      ( issec-eq-Eq-fib f y)
      ( isretr-eq-Eq-fib f y)

equiv-Eq-fib-eq :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  {s t : fib f y} → Id s t ≃ Eq-fib f y s t
equiv-Eq-fib-eq f y {s} {t} = pair (Eq-fib-eq f y) (is-equiv-Eq-fib-eq f y)

abstract
  is-equiv-eq-Eq-fib :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
    {s t : fib f y} → is-equiv (eq-Eq-fib f y {s} {t})
  is-equiv-eq-Eq-fib f y {s} {t} =
    is-equiv-has-inverse
      ( Eq-fib-eq f y)
      ( isretr-eq-Eq-fib f y)
      ( issec-eq-Eq-fib f y)

equiv-eq-Eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  {s t : fib f y} → Eq-fib f y s t ≃ Id s t
equiv-eq-Eq-fib f y {s} {t} = pair (eq-Eq-fib f y) (is-equiv-eq-Eq-fib f y)

{- Definition 10.3.4 -}

is-contr-map :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
is-contr-map f = (y : _) → is-contr (fib f y)

{- Theorem 10.3.5 -}

-- Our goal is to show that contractible maps are equivalences.
-- First we construct the inverse of a contractible map.
map-inv-is-contr-map :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-contr-map f → B → A
map-inv-is-contr-map is-contr-f y = pr1 (center (is-contr-f y))

-- Then we show that the inverse is a section.
issec-map-inv-is-contr-map :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B}
  (is-contr-f : is-contr-map f) → (f ∘ (map-inv-is-contr-map is-contr-f)) ~ id
issec-map-inv-is-contr-map is-contr-f y = pr2 (center (is-contr-f y))

-- Then we show that the inverse is also a retraction.
isretr-map-inv-is-contr-map :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B}
  (is-contr-f : is-contr-map f) → ((map-inv-is-contr-map is-contr-f) ∘ f) ~ id
isretr-map-inv-is-contr-map {_} {_} {A} {B} {f} is-contr-f x =
  ap ( pr1 {B = λ z → Id (f z) (f x)})
     ( ( inv
         ( contraction
           ( is-contr-f (f x))
           ( pair
             ( map-inv-is-contr-map is-contr-f (f x))
             ( issec-map-inv-is-contr-map is-contr-f (f x))))) ∙
       ( contraction (is-contr-f (f x)) (pair x refl)))

-- Finally we put it all together to show that contractible maps are equivalences.

abstract
  is-equiv-is-contr-map :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
    is-contr-map f → is-equiv f
  is-equiv-is-contr-map is-contr-f =
    is-equiv-has-inverse
      ( map-inv-is-contr-map is-contr-f)
      ( issec-map-inv-is-contr-map is-contr-f)
      ( isretr-map-inv-is-contr-map is-contr-f)

--------------------------------------------------------------------------------

-- Section 10.4 Equivalences are contractible maps

{- Definition 10.4.1 -}

coherence-is-coherently-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  (G : (f ∘ g) ~ id) (H : (g ∘ f) ~ id) → UU (l1 ⊔ l2)
coherence-is-coherently-invertible f g G H = (G ·r f) ~ (f ·l H)

is-coherently-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → UU (l1 ⊔ l2)
is-coherently-invertible {l1} {l2} {A} {B} f =
  Σ ( B → A)
    ( λ g → Σ ((f ∘ g) ~ id)
      ( λ G → Σ ((g ∘ f) ~ id)
        (λ H → ((G ·r f) ~ (f ·l H)))))

inv-is-coherently-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-coherently-invertible f → B → A
inv-is-coherently-invertible = pr1

issec-inv-is-coherently-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  (H : is-coherently-invertible f) → (f ∘ inv-is-coherently-invertible H) ~ id
issec-inv-is-coherently-invertible H = pr1 (pr2 H)

isretr-inv-is-coherently-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  (H : is-coherently-invertible f) → (inv-is-coherently-invertible H ∘ f) ~ id
isretr-inv-is-coherently-invertible H = pr1 (pr2 (pr2 H))

coh-inv-is-coherently-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  (H : is-coherently-invertible f) →
  coherence-is-coherently-invertible f
    ( inv-is-coherently-invertible H)
    ( issec-inv-is-coherently-invertible H)
    ( isretr-inv-is-coherently-invertible H)
coh-inv-is-coherently-invertible H = pr2 (pr2 (pr2 H))

{- Proposition 10.4.2 -}

abstract
  center-fib-is-coherently-invertible :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
    is-coherently-invertible f → (y : B) → fib f y
  center-fib-is-coherently-invertible {i} {j} {A} {B} {f} H y =
    pair
      ( inv-is-coherently-invertible H y)
      ( issec-inv-is-coherently-invertible H y)

  contraction-fib-is-coherently-invertible :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
    (H : is-coherently-invertible f) → (y : B) → (t : fib f y) →
    Id (center-fib-is-coherently-invertible H y) t
  contraction-fib-is-coherently-invertible {f = f} H y (pair x refl) =
    eq-Eq-fib f y
      ( pair 
        ( isretr-inv-is-coherently-invertible H x)
        ( ( right-unit) ∙
          ( inv ( coh-inv-is-coherently-invertible H x))))

is-contr-map-is-coherently-invertible : 
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-coherently-invertible f → is-contr-map f
is-contr-map-is-coherently-invertible H y =
  pair
    ( center-fib-is-coherently-invertible H y)
    ( contraction-fib-is-coherently-invertible H y)
      
{- Definition 10.4.3 -}

htpy-nat :
  {i j : Level} {A : UU i} {B : UU j} {f g : A → B} (H : f ~ g)
  {x y : A} (p : Id x y) →
  Id ((H x) ∙ (ap g p)) ((ap f p) ∙ (H y))
htpy-nat H refl = right-unit

{- Definition 10.4.4 -}

left-unwhisk :
  {i : Level} {A : UU i} {x y z : A} (p : Id x y) {q r : Id y z} →
  Id (p ∙ q) (p ∙ r) → Id q r
left-unwhisk refl s = (inv left-unit) ∙ (s ∙ left-unit)

right-unwhisk :
  {i : Level} {A : UU i} {x y z : A} {p q : Id x y}
  (r : Id y z) → Id (p ∙ r) (q ∙ r) → Id p q
right-unwhisk refl s = (inv right-unit) ∙ (s ∙ right-unit)

htpy-red :
  {i : Level} {A : UU i} {f : A → A} (H : f ~ id) →
  (x : A) → Id (H (f x)) (ap f (H x))
htpy-red {_} {A} {f} H x =
  right-unwhisk (H x)
    ( ( ap (concat (H (f x)) x) (inv (ap-id (H x)))) ∙
      ( htpy-nat H (H x)))

{- Lemma 10.4.5 -}

inv-has-inverse :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  has-inverse f → B → A
inv-has-inverse inv-f = pr1 inv-f

issec-inv-has-inverse :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (inv-f : has-inverse f) → (f ∘ (inv-has-inverse inv-f)) ~ id
issec-inv-has-inverse {f = f} (pair g (pair G H)) y =
  (inv (G (f (g y)))) ∙ (ap f (H (g y)) ∙ (G y))

isretr-inv-has-inverse :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (inv-f : has-inverse f) → ((inv-has-inverse inv-f) ∘ f) ~ id
isretr-inv-has-inverse inv-f = pr2 (pr2 inv-f)

coherence-inv-has-inverse :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (inv-f : has-inverse f) →
  ((issec-inv-has-inverse inv-f) ·r f) ~ (f ·l (isretr-inv-has-inverse inv-f))
coherence-inv-has-inverse {f = f} (pair g (pair G H)) x =
  inv
    ( inv-con
      ( G (f (g (f x))))
      ( ap f (H x))
      ( (ap f (H (g (f x)))) ∙ (G (f x)))
      ( sq-top-whisk
        ( G (f (g (f x))))
        ( ap f (H x))
        ( (ap (f ∘ (g ∘ f)) (H x)))
        ( (ap-comp f (g ∘ f) (H x)) ∙ (inv (ap (ap f) (htpy-red H x))))
        ( G (f x))
        ( htpy-nat (htpy-right-whisk G f) (H x))))

is-coherently-invertible-has-inverse :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  has-inverse f → is-coherently-invertible f
is-coherently-invertible-has-inverse H =
  pair
    ( inv-has-inverse H)
    ( pair
      ( issec-inv-has-inverse H)
      ( pair
        ( isretr-inv-has-inverse H)
        ( coherence-inv-has-inverse H)))

{- Theorem 10.4.6 -}

abstract
  is-contr-map-is-equiv :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
    is-equiv f → is-contr-map f
  is-contr-map-is-equiv =
    is-contr-map-is-coherently-invertible ∘
      ( is-coherently-invertible-has-inverse ∘
        has-inverse-is-equiv)

{- Corollary 10.4.7 -}

abstract
  is-contr-total-path' :
    {i : Level} {A : UU i} (a : A) → is-contr (Σ A (λ x → Id x a))
  is-contr-total-path' a = is-contr-map-is-equiv is-equiv-id a

--------------------------------------------------------------------------------

-- Exercises

-- Exercise 10.1

-- In this exercise we are asked to show that the identity types of a contractible type are again contractible. In the terminology of Lecture 8: we are showing that contractible types are propositions.

contraction-is-prop-is-contr :
  {i : Level} {A : UU i} (H : is-contr A) {x y : A} →
  (p : Id x y) → Id (eq-is-contr H x y) p
contraction-is-prop-is-contr (pair c C) {x} refl = left-inv (C x)

abstract
  is-prop-is-contr : {i : Level} {A : UU i} → is-contr A →
    (x y : A) → is-contr (Id x y)
  is-prop-is-contr {i} {A} is-contr-A x y =
    pair
      ( eq-is-contr is-contr-A x y)
      ( contraction-is-prop-is-contr is-contr-A)

-- Exercise 10.2

-- In this exercise we are showing that contractible types are closed under retracts.

abstract
  is-contr-retract-of : {i j : Level} {A : UU i} (B : UU j) →
    A retract-of B → is-contr B → is-contr A
  is-contr-retract-of B (pair i (pair r isretr)) is-contr-B =
    pair
      ( r (center is-contr-B))
      ( λ x → (ap r (contraction is-contr-B (i x))) ∙ (isretr x))

-- Exercise 10.3

-- In this exercise we are showing that a type is contractible if and only if the constant map to the unit type is an equivalence. This can be used to derive a '3-for-2 property' for contractible types, which may come in handy sometimes.

abstract
  is-equiv-const-is-contr :
    {i : Level} {A : UU i} → is-contr A → is-equiv (const A unit star)
  is-equiv-const-is-contr {i} {A} is-contr-A =
    pair
      ( pair (ind-unit (center is-contr-A)) (ind-unit refl))
      ( pair (const unit A (center is-contr-A)) (contraction is-contr-A))

abstract
  is-contr-is-equiv-const :
    {i : Level} {A : UU i} → is-equiv (const A unit star) → is-contr A
  is-contr-is-equiv-const (pair (pair g issec) (pair h isretr)) =
    pair (h star) isretr

abstract
  is-contr-is-equiv :
    {i j : Level} {A : UU i} (B : UU j) (f : A → B) →
    is-equiv f → is-contr B → is-contr A
  is-contr-is-equiv B f is-equiv-f is-contr-B =
    is-contr-is-equiv-const
      ( is-equiv-comp'
        ( const B unit star)
        ( f)
        ( is-equiv-f)
        ( is-equiv-const-is-contr is-contr-B))

abstract
  is-contr-equiv :
    {i j : Level} {A : UU i} (B : UU j) (e : A ≃ B) → is-contr B → is-contr A
  is-contr-equiv B (pair e is-equiv-e) is-contr-B =
    is-contr-is-equiv B e is-equiv-e is-contr-B

abstract
  is-contr-is-equiv' :
    {i j : Level} (A : UU i) {B : UU j} (f : A → B) →
    is-equiv f → is-contr A → is-contr B
  is-contr-is-equiv' A f is-equiv-f is-contr-A =
    is-contr-is-equiv A
      ( map-inv-is-equiv is-equiv-f)
      ( is-equiv-map-inv-is-equiv is-equiv-f)
      ( is-contr-A)

abstract
  is-contr-equiv' :
    {i j : Level} (A : UU i) {B : UU j} (e : A ≃ B) → is-contr A → is-contr B
  is-contr-equiv' A (pair e is-equiv-e) is-contr-A =
    is-contr-is-equiv' A e is-equiv-e is-contr-A

abstract
  is-equiv-is-contr :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
    is-contr A → is-contr B → is-equiv f
  is-equiv-is-contr {i} {j} {A} {B} f is-contr-A is-contr-B =
    is-equiv-has-inverse
      ( const B A (center is-contr-A))
      ( ind-singleton-is-contr _ is-contr-B _
        ( inv (contraction is-contr-B (f (center is-contr-A)))))
      ( contraction is-contr-A)

equiv-is-contr :
  {i j : Level} {A : UU i} {B : UU j} →
  is-contr A → is-contr B → A ≃ B
equiv-is-contr is-contr-A is-contr-B =
  pair
    ( λ a → center is-contr-B)
    ( is-equiv-is-contr _ is-contr-A is-contr-B)

map-equiv-Fin-one-ℕ : Fin one-ℕ → unit
map-equiv-Fin-one-ℕ (inr star) = star

inv-map-equiv-Fin-one-ℕ : unit → Fin one-ℕ
inv-map-equiv-Fin-one-ℕ star = inr star

issec-inv-map-equiv-Fin-one-ℕ :
  ( map-equiv-Fin-one-ℕ ∘ inv-map-equiv-Fin-one-ℕ) ~ id
issec-inv-map-equiv-Fin-one-ℕ star = refl

isretr-inv-map-equiv-Fin-one-ℕ :
  ( inv-map-equiv-Fin-one-ℕ ∘ map-equiv-Fin-one-ℕ) ~ id
isretr-inv-map-equiv-Fin-one-ℕ (inr star) = refl

is-equiv-map-equiv-Fin-one-ℕ : is-equiv map-equiv-Fin-one-ℕ
is-equiv-map-equiv-Fin-one-ℕ =
  is-equiv-has-inverse
    inv-map-equiv-Fin-one-ℕ
    issec-inv-map-equiv-Fin-one-ℕ
    isretr-inv-map-equiv-Fin-one-ℕ

equiv-Fin-one-ℕ : Fin one-ℕ ≃ unit
equiv-Fin-one-ℕ = pair map-equiv-Fin-one-ℕ is-equiv-map-equiv-Fin-one-ℕ

is-contr-Fin-one-ℕ : is-contr (Fin one-ℕ)
is-contr-Fin-one-ℕ = is-contr-equiv unit equiv-Fin-one-ℕ is-contr-unit

-- Exercise 10.4

-- In this exercise we will show that if the base type in a Σ-type is contractible, then the Σ-type is equivalent to the fiber at the center of contraction. This can be seen as a left unit law for Σ-types. We will derive a right unit law for Σ-types in Lecture 7 (not because it is unduable here, but it is useful to have some knowledge of fiberwise equivalences).

map-left-unit-law-Σ-is-contr :
  {i j : Level} {C : UU i} (B : C → UU j)
  (is-contr-C : is-contr C) → B (center is-contr-C) → Σ C B
map-left-unit-law-Σ-is-contr B is-contr-C y = pair (center is-contr-C) y

inv-map-left-unit-law-Σ-is-contr :
  {i j : Level} {C : UU i} (B : C → UU j)
  (is-contr-C : is-contr C) → Σ C B → B (center is-contr-C)
inv-map-left-unit-law-Σ-is-contr B is-contr-C =
  ind-Σ
    ( ind-singleton-is-contr (center is-contr-C) is-contr-C
      ( λ x → B x → B (center is-contr-C))
      ( id))

isretr-inv-map-left-unit-law-Σ-is-contr :
  {i j : Level} {C : UU i} (B : C → UU j) (is-contr-C : is-contr C) →
  ( ( inv-map-left-unit-law-Σ-is-contr B is-contr-C) ∘
    ( map-left-unit-law-Σ-is-contr B is-contr-C)) ~ id
isretr-inv-map-left-unit-law-Σ-is-contr B is-contr-C y =
  ap
    ( λ (f : B (center is-contr-C) → B (center is-contr-C)) → f y)
    ( comp-singleton-is-contr (center is-contr-C) is-contr-C
      ( λ x → B x → B (center is-contr-C))
      ( id))

issec-inv-map-left-unit-law-Σ-is-contr :
  {i j : Level} {C : UU i} (B : C → UU j) (is-contr-C : is-contr C) →
  ( ( map-left-unit-law-Σ-is-contr B is-contr-C) ∘
    ( inv-map-left-unit-law-Σ-is-contr B is-contr-C)) ~ id
issec-inv-map-left-unit-law-Σ-is-contr B is-contr-C =
  ind-Σ
    ( ind-singleton-is-contr (center is-contr-C) is-contr-C
      ( λ x → (y : B x) →
        Id ( ( ( map-left-unit-law-Σ-is-contr B is-contr-C) ∘
               ( inv-map-left-unit-law-Σ-is-contr B is-contr-C))
             ( pair x y))
           ( id (pair x y)))
      ( λ y → ap
        ( map-left-unit-law-Σ-is-contr B is-contr-C)
        ( ap
          ( λ f → f y)
          ( comp-singleton-is-contr (center is-contr-C) is-contr-C
            ( λ x → B x → B (center is-contr-C)) id))))

abstract
  is-equiv-map-left-unit-law-Σ-is-contr :
    {i j : Level} {C : UU i} (B : C → UU j) (is-contr-C : is-contr C) →
    is-equiv (map-left-unit-law-Σ-is-contr B is-contr-C)
  is-equiv-map-left-unit-law-Σ-is-contr B is-contr-C =
    is-equiv-has-inverse
      ( inv-map-left-unit-law-Σ-is-contr B is-contr-C)
      ( issec-inv-map-left-unit-law-Σ-is-contr B is-contr-C)
      ( isretr-inv-map-left-unit-law-Σ-is-contr B is-contr-C)

abstract
  is-equiv-inv-map-left-unit-law-Σ-is-contr :
    {i j : Level} {C : UU i} (B : C → UU j) (is-contr-C : is-contr C) →
    is-equiv (inv-map-left-unit-law-Σ-is-contr B is-contr-C)
  is-equiv-inv-map-left-unit-law-Σ-is-contr B is-contr-C =
    is-equiv-has-inverse
      ( map-left-unit-law-Σ-is-contr B is-contr-C)
      ( isretr-inv-map-left-unit-law-Σ-is-contr B is-contr-C)
      ( issec-inv-map-left-unit-law-Σ-is-contr B is-contr-C)

left-unit-law-Σ-is-contr : {i j : Level} {C : UU i} (B : C → UU j)
  (is-contr-C : is-contr C) → B (center is-contr-C) ≃ Σ C B
left-unit-law-Σ-is-contr B is-contr-C =
  pair
    ( map-left-unit-law-Σ-is-contr B is-contr-C)
    ( is-equiv-map-left-unit-law-Σ-is-contr B is-contr-C)

map-left-unit-law-Σ-is-contr-gen :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
  is-contr A → (x : A) → B x → Σ A B
map-left-unit-law-Σ-is-contr-gen B is-contr-A x y = pair x y

abstract
  is-equiv-map-left-unit-law-Σ-is-contr-gen :
    {l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
    (is-contr-A : is-contr A) →
    (x : A) → is-equiv (map-left-unit-law-Σ-is-contr-gen B is-contr-A x)
  is-equiv-map-left-unit-law-Σ-is-contr-gen B is-contr-A x =
    is-equiv-comp
      ( map-left-unit-law-Σ-is-contr-gen B is-contr-A x)
      ( map-left-unit-law-Σ-is-contr B is-contr-A)
      ( tr B (inv (contraction is-contr-A x)))
      ( λ y → eq-pair (inv (contraction is-contr-A x)) refl)
      ( is-equiv-tr B (inv (contraction is-contr-A x)))
      ( is-equiv-map-left-unit-law-Σ-is-contr B is-contr-A)

left-unit-law-Σ-is-contr-gen :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
  (is-contr-A : is-contr A) →
  (x : A) → B x ≃ Σ A B
left-unit-law-Σ-is-contr-gen B is-contr-A x =
  pair
    ( map-left-unit-law-Σ-is-contr-gen B is-contr-A x)
    ( is-equiv-map-left-unit-law-Σ-is-contr-gen B is-contr-A x)

-- Exercise 10.6

-- In this exercise we show that the domain of a map is equivalent to the total space of its fibers.

Σ-fib-to-domain :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B ) → (Σ B (fib f)) → A
Σ-fib-to-domain f t = pr1 (pr2 t)

triangle-Σ-fib-to-domain :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B ) →
  pr1 ~ (f ∘ (Σ-fib-to-domain f))
triangle-Σ-fib-to-domain f t = inv (pr2 (pr2 t))

domain-to-Σ-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → A → Σ B (fib f)
domain-to-Σ-fib f x = pair (f x) (pair x refl)

left-inverse-domain-to-Σ-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B ) →
  ((domain-to-Σ-fib f) ∘ (Σ-fib-to-domain f)) ~ id
left-inverse-domain-to-Σ-fib f (pair .(f x) (pair x refl)) = refl

right-inverse-domain-to-Σ-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B ) →
  ((Σ-fib-to-domain f) ∘ (domain-to-Σ-fib f)) ~ id
right-inverse-domain-to-Σ-fib f x = refl

abstract
  is-equiv-Σ-fib-to-domain :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B ) →
    is-equiv (Σ-fib-to-domain f)
  is-equiv-Σ-fib-to-domain f =
    is-equiv-has-inverse
      ( domain-to-Σ-fib f)
      ( right-inverse-domain-to-Σ-fib f)
      ( left-inverse-domain-to-Σ-fib f)

equiv-Σ-fib-to-domain :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B ) → Σ B (fib f) ≃ A
equiv-Σ-fib-to-domain f =
  pair (Σ-fib-to-domain f) (is-equiv-Σ-fib-to-domain f)

-- Exercise 10.7

-- In this exercise we show that if a cartesian product is contractible, then so are its factors. We make use of the fact that contractible types are closed under retracts, just because that is a useful property to practice with. Other proofs are possible too.

abstract
  is-contr-left-factor-prod :
    {i j : Level} (A : UU i) (B : UU j) → is-contr (A × B) → is-contr A
  is-contr-left-factor-prod A B is-contr-AB =
    is-contr-retract-of
      ( A × B)
      ( pair
        ( λ x → pair x (pr2 (center is-contr-AB)))
        ( pair pr1 (λ x → refl)))
      ( is-contr-AB)

abstract
  is-contr-right-factor-prod :
    {i j : Level} (A : UU i) (B : UU j) → is-contr (A × B) → is-contr B
  is-contr-right-factor-prod A B is-contr-AB =
    is-contr-left-factor-prod B A
      ( is-contr-equiv
        ( A × B)
        ( equiv-swap-prod B A)
        ( is-contr-AB))

abstract
  is-contr-prod :
    {i j : Level} {A : UU i} {B : UU j} →
    is-contr A → is-contr B → is-contr (A × B)
  is-contr-prod {A = A} {B = B} is-contr-A is-contr-B =
    is-contr-equiv' B
      ( left-unit-law-Σ-is-contr (λ x → B) is-contr-A)
      ( is-contr-B)

-- Exercise 10.8

-- Given any family B over A, there is a map from the fiber of the projection map (pr1 : Σ A B → A) to the type (B a), i.e. the fiber of B at a. In this exercise we define this map, and show that it is an equivalence, for every a : A.

fib-fam-fib-pr1 :
  {i j : Level} {A : UU i} (B : A → UU j)
  (a : A) → fib (pr1 {B = B}) a → B a
fib-fam-fib-pr1 B a (pair (pair x y) p) = tr B p y

fib-pr1-fib-fam :
  {i j : Level} {A : UU i} (B : A → UU j)
  (a : A) → B a → fib (pr1 {B = B}) a
fib-pr1-fib-fam B a b = pair (pair a b) refl

left-inverse-fib-pr1-fib-fam :
  {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
  ((fib-pr1-fib-fam B a) ∘ (fib-fam-fib-pr1 B a)) ~ id
left-inverse-fib-pr1-fib-fam B a (pair (pair .a y) refl) = refl

right-inverse-fib-pr1-fib-fam :
  {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
  ((fib-fam-fib-pr1 B a) ∘ (fib-pr1-fib-fam B a)) ~ id
right-inverse-fib-pr1-fib-fam B a b = refl

abstract
  is-equiv-fib-fam-fib-pr1 :
    {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
    is-equiv (fib-fam-fib-pr1 B a)
  is-equiv-fib-fam-fib-pr1 B a =
    is-equiv-has-inverse
      ( fib-pr1-fib-fam B a)
      ( right-inverse-fib-pr1-fib-fam B a)
      ( left-inverse-fib-pr1-fib-fam B a)

equiv-fib-fam-fib-pr1 :
  {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
  fib (pr1 {B = B}) a ≃ B a
equiv-fib-fam-fib-pr1 B a =
  pair (fib-fam-fib-pr1 B a) (is-equiv-fib-fam-fib-pr1 B a)

abstract
  is-equiv-fib-pr1-fib-fam :
    {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
    is-equiv (fib-pr1-fib-fam B a)
  is-equiv-fib-pr1-fib-fam B a =
    is-equiv-has-inverse
      ( fib-fam-fib-pr1 B a)
      ( left-inverse-fib-pr1-fib-fam B a)
      ( right-inverse-fib-pr1-fib-fam B a)

equiv-fib-pr1-fib-fam :
  {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
  B a ≃ fib (pr1 {B = B}) a
equiv-fib-pr1-fib-fam B a =
  pair (fib-pr1-fib-fam B a) (is-equiv-fib-pr1-fib-fam B a)

abstract
  is-equiv-pr1-is-contr :
    {i j : Level} {A : UU i} (B : A → UU j) →
    ((a : A) → is-contr (B a)) → is-equiv (pr1 {B = B})
  is-equiv-pr1-is-contr B is-contr-B =
    is-equiv-is-contr-map
      ( λ x → is-contr-equiv
        ( B x)
        ( equiv-fib-fam-fib-pr1 B x)
        ( is-contr-B x))

equiv-pr1 :
  {i j : Level} {A : UU i} {B : A → UU j} →
  ((a : A) → is-contr (B a)) → (Σ A B) ≃ A
equiv-pr1 is-contr-B = pair pr1 (is-equiv-pr1-is-contr _ is-contr-B)

abstract
  is-contr-is-equiv-pr1 :
    {i j : Level} {A : UU i} (B : A → UU j) →
    (is-equiv (pr1 {B = B})) → ((a : A) → is-contr (B a))
  is-contr-is-equiv-pr1 B is-equiv-pr1-B a =
    is-contr-equiv'
      ( fib pr1 a)
      ( equiv-fib-fam-fib-pr1 B a)
      ( is-contr-map-is-equiv is-equiv-pr1-B a)

right-unit-law-Σ :
  {i j : Level} {A : UU i} (B : A → UU j) →
  ((a : A) → is-contr (B a)) → (Σ A B) ≃ A
right-unit-law-Σ B is-contr-B =
  pair pr1 (is-equiv-pr1-is-contr B is-contr-B)
