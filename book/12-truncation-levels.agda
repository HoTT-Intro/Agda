{-# OPTIONS --without-K --exact-split --safe #-}

module book.12-truncation-levels where

import book.11-fundamental-theorem
open book.11-fundamental-theorem public

-- Section 8.1 Propositions

is-prop :
  {i : Level} (A : UU i) → UU i
is-prop A = (x y : A) → is-contr (Id x y)

{- We introduce the universe of all propositions. -}
UU-Prop :
  (l : Level) → UU (lsuc l)
UU-Prop l = Σ (UU l) is-prop

type-Prop :
  {l : Level} → UU-Prop l → UU l
type-Prop P = pr1 P

is-prop-type-Prop :
  {l : Level} (P : UU-Prop l) → is-prop (type-Prop P)
is-prop-type-Prop P = pr2 P

{- The empty type is a proposition. -}

abstract
  is-prop-empty : is-prop empty
  is-prop-empty ()

empty-Prop : UU-Prop lzero
empty-Prop = pair empty is-prop-empty

abstract
  is-prop-unit : is-prop unit
  is-prop-unit = is-prop-is-contr is-contr-unit

unit-Prop : UU-Prop lzero
unit-Prop = pair unit is-prop-unit

is-prop' :
  {i : Level} (A : UU i) → UU i
is-prop' A = (x y : A) → Id x y

abstract
  is-prop-is-prop' :
    {i : Level} {A : UU i} → is-prop' A → is-prop A
  is-prop-is-prop' {i} {A} H x y =
    pair
      ( (inv (H x x)) ∙ (H x y))
      ( ind-Id x
        ( λ z p → Id ((inv (H x x)) ∙ (H x z)) p)
        ( left-inv (H x x)) y)

abstract
  eq-is-prop :
    {i : Level} {A : UU i} → is-prop A → is-prop' A
  eq-is-prop H x y = pr1 (H x y)

abstract
  is-contr-is-prop-inh :
    {i : Level} {A : UU i} → is-prop A → A → is-contr A
  is-contr-is-prop-inh H a = pair a (eq-is-prop H a)

abstract
  is-prop-is-contr-if-inh :
    {i : Level} {A : UU i} → (A → is-contr A) → is-prop A
  is-prop-is-contr-if-inh H x y = is-prop-is-contr (H x) x y

is-subtype :
  {i j : Level} {A : UU i} (B : A → UU j) → UU (i ⊔ j)
is-subtype B = (x : _) → is-prop (B x)

double-structure-swap :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : A → UU l3) →
  Σ (Σ A B) (λ t → C (pr1 t)) → Σ (Σ A C) (λ t → B (pr1 t))
double-structure-swap A B C (pair (pair a b) c) = (pair (pair a c) b)

htpy-double-structure-swap :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : A → UU l3) →
  ((double-structure-swap A C B) ∘ (double-structure-swap A B C)) ~ id
htpy-double-structure-swap A B C (pair (pair a b) c) =
  eq-pair (eq-pair refl refl) refl

is-equiv-double-structure-swap :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : A → UU l3) →
  is-equiv (double-structure-swap A B C)
is-equiv-double-structure-swap A B C =
  is-equiv-has-inverse
    ( double-structure-swap A C B)
    ( htpy-double-structure-swap A C B)
    ( htpy-double-structure-swap A B C)

{- The following is a general construction that will help us show that
   the identity type of a subtype agrees with the identity type of the 
   original type. We already know that the first projection of a family of
   propositions is an embedding, but the following lemma still has its uses. -}

abstract
  is-contr-total-Eq-substructure :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {P : A → UU l3} →
    is-contr (Σ A B) → (is-subtype P) → (a : A) (b : B a) (p : P a) →
    is-contr (Σ (Σ A P) (λ t → B (pr1 t)))
  is-contr-total-Eq-substructure {A = A} {B} {P}
    is-contr-AB is-subtype-P a b p =
    is-contr-is-equiv
      ( Σ (Σ A B) (λ t → P (pr1 t)))
      ( double-structure-swap A P B)
      ( is-equiv-double-structure-swap A P B)
      ( is-contr-is-equiv'
        ( P a)
        ( map-left-unit-law-Σ-is-contr-gen
          ( λ t → P (pr1 t))
          ( is-contr-AB)
          ( pair a b))
        ( is-equiv-map-left-unit-law-Σ-is-contr-gen _ is-contr-AB (pair a b))
        ( is-contr-is-prop-inh (is-subtype-P a) p))

Eq-total-subtype :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-subtype B →
  (Σ A B) → (Σ A B) → UU l1
Eq-total-subtype is-subtype-B p p' = Id (pr1 p) (pr1 p') 

reflexive-Eq-total-subtype :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (is-subtype-B : is-subtype B) →
  (p : Σ A B) → Eq-total-subtype is-subtype-B p p
reflexive-Eq-total-subtype is-subtype-B (pair x y) = refl

Eq-total-subtype-eq :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (is-subtype-B : is-subtype B) →
  (p p' : Σ A B) → Id p p' → Eq-total-subtype is-subtype-B p p'
Eq-total-subtype-eq is-subtype-B p .p refl =
  reflexive-Eq-total-subtype is-subtype-B p

is-contr-total-Eq-total-subtype :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (is-subtype-B : is-subtype B) →
  (p : Σ A B) → is-contr (Σ (Σ A B) (Eq-total-subtype is-subtype-B p))
is-contr-total-Eq-total-subtype is-subtype-B (pair x y) =
  is-contr-total-Eq-substructure
    ( is-contr-total-path x)
    ( is-subtype-B)
    x refl y

is-equiv-Eq-total-subtype-eq :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (is-subtype-B : is-subtype B) →
  (p p' : Σ A B) → is-equiv (Eq-total-subtype-eq is-subtype-B p p')
is-equiv-Eq-total-subtype-eq is-subtype-B p =
  fundamental-theorem-id p
    ( reflexive-Eq-total-subtype is-subtype-B p)
    ( is-contr-total-Eq-total-subtype is-subtype-B p)
    ( Eq-total-subtype-eq is-subtype-B p)

equiv-Eq-total-subtype-eq :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (is-subtype-B : is-subtype B) →
  (p p' : Σ A B) → (Id p p') ≃ (Eq-total-subtype is-subtype-B p p')
equiv-Eq-total-subtype-eq is-subtype-B p p' =
  pair
    ( Eq-total-subtype-eq is-subtype-B p p')
    ( is-equiv-Eq-total-subtype-eq is-subtype-B p p')

eq-subtype :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (is-subtype-B : is-subtype B) →
  {p p' : Σ A B} → Eq-total-subtype is-subtype-B p p' → Id p p'
eq-subtype is-subtype-B {p} {p'} =
  map-inv-is-equiv (is-equiv-Eq-total-subtype-eq is-subtype-B p p')

-- Section 8.2 Sets

is-set :
  {i : Level} → UU i → UU i
is-set A = (x y : A) → is-prop (Id x y)

UU-Set :
  (i : Level) → UU (lsuc i)
UU-Set i = Σ (UU i) is-set

type-Set :
  {l : Level} → UU-Set l → UU l
type-Set X = pr1 X

is-set-type-Set :
  {l : Level} (X : UU-Set l) → is-set (type-Set X)
is-set-type-Set X = pr2 X

Id-Prop :
  {l : Level} (X : UU-Set l) (x y : type-Set X) → UU-Prop l
Id-Prop X x y = pair (Id x y) (is-set-type-Set X x y)

axiom-K :
  {i : Level} → UU i → UU i
axiom-K A = (x : A) (p : Id x x) → Id refl p

abstract
  is-set-axiom-K :
    {i : Level} (A : UU i) → axiom-K A → is-set A
  is-set-axiom-K A H x y =
    is-prop-is-prop' (ind-Id x (λ z p → (q : Id x z) → Id p q) (H x) y)

abstract
  axiom-K-is-set :
    {i : Level} (A : UU i) → is-set A → axiom-K A
  axiom-K-is-set A H x p =
    ( inv (contraction (is-contr-is-prop-inh (H x x) refl) refl)) ∙ 
    ( contraction (is-contr-is-prop-inh (H x x) refl) p)

abstract
  is-equiv-prop-in-id :
    {i j : Level} {A : UU i}
    (R : A → A → UU j)
    (p : (x y : A) → is-prop (R x y))
    (ρ : (x : A) → R x x)
    (i : (x y : A) → R x y → Id x y) →
    (x y : A) → is-equiv (i x y)
  is-equiv-prop-in-id R p ρ i x =
    fundamental-theorem-id-retr x (i x)
      (λ y → pair
        (ind-Id x (λ z p → R x z) (ρ x) y)
        ((λ r → eq-is-prop (p x y) _ r)))

abstract
  is-prop-is-equiv :
    {i j : Level} {A : UU i} (B : UU j) (f : A → B) (E : is-equiv f) →
    is-prop B → is-prop A
  is-prop-is-equiv B f E H x y =
    is-contr-is-equiv _ (ap f {x} {y}) (is-emb-is-equiv f E x y) (H (f x) (f y))

is-prop-equiv :
  {i j : Level} {A : UU i} (B : UU j) (e : A ≃ B) → is-prop B → is-prop A
is-prop-equiv B (pair f is-equiv-f) = is-prop-is-equiv B f is-equiv-f

abstract
  is-prop-is-equiv' :
    {i j : Level} (A : UU i) {B : UU j} (f : A → B) (E : is-equiv f) →
    is-prop A → is-prop B
  is-prop-is-equiv' A f E H =
    is-prop-is-equiv _ (map-inv-is-equiv E) (is-equiv-map-inv-is-equiv E) H

is-prop-equiv' :
  {i j : Level} (A : UU i) {B : UU j} (e : A ≃ B) → is-prop A → is-prop B
is-prop-equiv' A (pair f is-equiv-f) = is-prop-is-equiv' A f is-equiv-f

abstract
  is-set-prop-in-id :
    {i j : Level} {A : UU i} (R : A → A → UU j)
    (p : (x y : A) → is-prop (R x y))
    (ρ : (x : A) → R x x)
    (i : (x y : A) → R x y → Id x y) →
    is-set A
  is-set-prop-in-id R p ρ i x y =
    is-prop-is-equiv'
      ( R x y)
      ( i x y)
      ( is-equiv-prop-in-id R p ρ i x y) (p x y)

abstract
  is-prop-Eq-ℕ :
    (n m : ℕ) → is-prop (Eq-ℕ n m)
  is-prop-Eq-ℕ zero-ℕ zero-ℕ = is-prop-unit
  is-prop-Eq-ℕ zero-ℕ (succ-ℕ m) = is-prop-empty
  is-prop-Eq-ℕ (succ-ℕ n) zero-ℕ = is-prop-empty
  is-prop-Eq-ℕ (succ-ℕ n) (succ-ℕ m) = is-prop-Eq-ℕ n m

abstract
  is-set-ℕ : is-set ℕ
  is-set-ℕ =
    is-set-prop-in-id
      Eq-ℕ
      is-prop-Eq-ℕ
      refl-Eq-ℕ
      eq-Eq-ℕ

ℕ-Set : UU-Set lzero
ℕ-Set = pair ℕ is-set-ℕ

{- Next, we show that types with decidable equality are sets. To see this, we 
   will construct a fiberwise equivalence with the binary relation R that is
   defined by R x y := unit if (x = y), and empty otherwise. In order to define
   this relation, we first define a type family over ((x = y) + ¬(x = y)) that 
   returns unit on the left and empty on the right. -}
   
Eq-has-decidable-equality' :
  {l : Level} {A : UU l} (x y : A) → is-decidable (Id x y) → UU lzero
Eq-has-decidable-equality' x y (inl p) = unit
Eq-has-decidable-equality' x y (inr f) = empty

Eq-has-decidable-equality :
  {l : Level} {A : UU l} (d : has-decidable-equality A) → A → A → UU lzero
Eq-has-decidable-equality d x y = Eq-has-decidable-equality' x y (d x y)

is-prop-Eq-has-decidable-equality' :
  {l : Level} {A : UU l} (x y : A) (t : is-decidable (Id x y)) →
  is-prop (Eq-has-decidable-equality' x y t)
is-prop-Eq-has-decidable-equality' x y (inl p) = is-prop-unit
is-prop-Eq-has-decidable-equality' x y (inr f) = is-prop-empty

is-prop-Eq-has-decidable-equality :
  {l : Level} {A : UU l} (d : has-decidable-equality A)
  {x y : A} → is-prop (Eq-has-decidable-equality d x y)
is-prop-Eq-has-decidable-equality d {x} {y} =
  is-prop-Eq-has-decidable-equality' x y (d x y)

reflexive-Eq-has-decidable-equality :
  {l : Level} {A : UU l} (d : has-decidable-equality A) (x : A) →
  Eq-has-decidable-equality d x x 
reflexive-Eq-has-decidable-equality d x with d x x
... | inl α = star
... | inr f = f refl

Eq-has-decidable-equality-eq :
  {l : Level} {A : UU l} (d : has-decidable-equality A) {x y : A} →
  Id x y → Eq-has-decidable-equality d x y
Eq-has-decidable-equality-eq {l} {A} d {x} {.x} refl =
  reflexive-Eq-has-decidable-equality d x

eq-Eq-has-decidable-equality' :
  {l : Level} {A : UU l} (x y : A) (t : is-decidable (Id x y)) →
  Eq-has-decidable-equality' x y t → Id x y
eq-Eq-has-decidable-equality' x y (inl p) t = p
eq-Eq-has-decidable-equality' x y (inr f) t = ex-falso t

eq-Eq-has-decidable-equality :
  {l : Level} {A : UU l} (d : has-decidable-equality A) {x y : A} →
  Eq-has-decidable-equality d x y → Id x y
eq-Eq-has-decidable-equality d {x} {y} =
  eq-Eq-has-decidable-equality' x y (d x y)

is-set-has-decidable-equality :
  {l : Level} {A : UU l} → has-decidable-equality A → is-set A
is-set-has-decidable-equality d =
  is-set-prop-in-id
    ( λ x y → Eq-has-decidable-equality d x y)
    ( λ x y → is-prop-Eq-has-decidable-equality d)
    ( λ x → reflexive-Eq-has-decidable-equality d x)
    ( λ x y → eq-Eq-has-decidable-equality d)

-- Section 8.3 General truncation levels

data 𝕋 : UU lzero where
  neg-two-𝕋 : 𝕋
  succ-𝕋 : 𝕋 → 𝕋

neg-one-𝕋 : 𝕋
neg-one-𝕋 = succ-𝕋 (neg-two-𝕋)

zero-𝕋 : 𝕋
zero-𝕋 = succ-𝕋 (neg-one-𝕋)

one-𝕋 : 𝕋
one-𝕋 = succ-𝕋 (zero-𝕋)

ℕ-in-𝕋 : ℕ → 𝕋
ℕ-in-𝕋 zero-ℕ = zero-𝕋
ℕ-in-𝕋 (succ-ℕ n) = succ-𝕋 (ℕ-in-𝕋 n)

-- Probably it is better to define this where we first need it.
add-𝕋 : 𝕋 → 𝕋 → 𝕋
add-𝕋 neg-two-𝕋 neg-two-𝕋 = neg-two-𝕋
add-𝕋 neg-two-𝕋 (succ-𝕋 neg-two-𝕋) = neg-two-𝕋
add-𝕋 neg-two-𝕋 (succ-𝕋 (succ-𝕋 y)) = y
add-𝕋 (succ-𝕋 neg-two-𝕋) neg-two-𝕋 = neg-two-𝕋
add-𝕋 (succ-𝕋 neg-two-𝕋) (succ-𝕋 y) = y
add-𝕋 (succ-𝕋 (succ-𝕋 neg-two-𝕋)) y = y
add-𝕋 (succ-𝕋 (succ-𝕋 (succ-𝕋 x))) y = succ-𝕋 (add-𝕋 (succ-𝕋 (succ-𝕋 x)) y)

is-trunc : {i : Level} (k : 𝕋) → UU i → UU i
is-trunc neg-two-𝕋 A = is-contr A
is-trunc (succ-𝕋 k) A = (x y : A) → is-trunc k (Id x y)

-- We introduce some notation for the special case of 1-types --

is-1-type : {l : Level} → UU l → UU l
is-1-type = is-trunc one-𝕋

UU-1-Type : (l : Level) → UU (lsuc l)
UU-1-Type l = Σ (UU l) is-1-type

type-1-Type :
  {l : Level} → UU-1-Type l → UU l
type-1-Type = pr1

is-1-type-type-1-Type :
  {l : Level} (A : UU-1-Type l) → is-1-type (type-1-Type A)
is-1-type-type-1-Type = pr2

-- We introduce some notation for the special case of 2-types --

is-2-type : {l : Level} → UU l → UU l
is-2-type = is-trunc (succ-𝕋 one-𝕋)

UU-2-Type : (l : Level) → UU (lsuc l)
UU-2-Type l = Σ (UU l) is-2-type

type-2-Type :
  {l : Level} → UU-2-Type l → UU l
type-2-Type = pr1

is-2-type-type-2-Type :
  {l : Level} (A : UU-2-Type l) → is-2-type (type-2-Type A)
is-2-type-type-2-Type = pr2

-- We introduce some notation for the universe of k-truncated types --

UU-Truncated-Type : 𝕋 → (l : Level) → UU (lsuc l)
UU-Truncated-Type k l = Σ (UU l) (is-trunc k)

type-Truncated-Type :
  (k : 𝕋) {l : Level} → UU-Truncated-Type k l → UU l
type-Truncated-Type k = pr1

is-trunc-type-Truncated-Type :
  (k : 𝕋) {l : Level} (A : UU-Truncated-Type k l) →
  is-trunc k (type-Truncated-Type k A)
is-trunc-type-Truncated-Type k = pr2

-- We show that if a type is k-truncated, then it is (k+1)-truncated. --

abstract
  is-trunc-succ-is-trunc :
    (k : 𝕋) {i : Level} {A : UU i} →
    is-trunc k A → is-trunc (succ-𝕋 k) A
  is-trunc-succ-is-trunc neg-two-𝕋 H =
    is-prop-is-contr H
  is-trunc-succ-is-trunc (succ-𝕋 k) H x y =
    is-trunc-succ-is-trunc k (H x y)

truncated-type-succ-Truncated-Type :
  (k : 𝕋) {l : Level} → UU-Truncated-Type k l → UU-Truncated-Type (succ-𝕋 k) l
truncated-type-succ-Truncated-Type k A =
  pair
    ( type-Truncated-Type k A)
    ( is-trunc-succ-is-trunc k (is-trunc-type-Truncated-Type k A))

set-Prop :
  {l : Level} → UU-Prop l → UU-Set l
set-Prop P = truncated-type-succ-Truncated-Type neg-one-𝕋 P

1-type-Set :
  {l : Level} → UU-Set l → UU-1-Type l
1-type-Set A = truncated-type-succ-Truncated-Type zero-𝕋 A

-- We show that k-truncated types are closed under equivalences --

abstract
  is-trunc-is-equiv :
    {i j : Level} (k : 𝕋) {A : UU i} (B : UU j) (f : A → B) → is-equiv f →
    is-trunc k B → is-trunc k A
  is-trunc-is-equiv neg-two-𝕋 B f is-equiv-f H =
    is-contr-is-equiv B f is-equiv-f H
  is-trunc-is-equiv (succ-𝕋 k) B f is-equiv-f H x y =
    is-trunc-is-equiv k (Id (f x) (f y)) (ap f {x} {y})
      (is-emb-is-equiv f is-equiv-f x y) (H (f x) (f y))

abstract
  is-set-is-equiv :
    {i j : Level} {A : UU i} (B : UU j) (f : A → B) → is-equiv f →
    is-set B → is-set A
  is-set-is-equiv = is-trunc-is-equiv zero-𝕋

abstract
  is-trunc-equiv :
    {i j : Level} (k : 𝕋) {A : UU i} (B : UU  j) (e : A ≃ B) →
    is-trunc k B → is-trunc k A
  is-trunc-equiv k B (pair f is-equiv-f) =
    is-trunc-is-equiv k B f is-equiv-f

abstract
  is-set-equiv :
    {i j : Level} {A : UU i} (B : UU j) (e : A ≃ B) →
    is-set B → is-set A
  is-set-equiv = is-trunc-equiv zero-𝕋

abstract
  is-trunc-is-equiv' :
    {i j : Level} (k : 𝕋) (A : UU i) {B : UU j} (f : A → B) →
    is-equiv f → is-trunc k A → is-trunc k B
  is-trunc-is-equiv' k A  f is-equiv-f is-trunc-A =
    is-trunc-is-equiv k A
      ( map-inv-is-equiv is-equiv-f)
      ( is-equiv-map-inv-is-equiv is-equiv-f)
      ( is-trunc-A)

abstract
  is-set-is-equiv' :
    {i j : Level} (A : UU i) {B : UU j} (f : A → B) → is-equiv f →
    is-set A → is-set B
  is-set-is-equiv' = is-trunc-is-equiv' zero-𝕋

abstract
  is-trunc-equiv' :
    {i j : Level} (k : 𝕋) (A : UU i) {B : UU j} (e : A ≃ B) →
    is-trunc k A → is-trunc k B
  is-trunc-equiv' k A (pair f is-equiv-f) =
    is-trunc-is-equiv' k A f is-equiv-f

abstract
  is-set-equiv' :
    {i j : Level} (A : UU i) {B : UU j} (e : A ≃ B) →
    is-set A → is-set B
  is-set-equiv' = is-trunc-equiv' zero-𝕋

-- We show that if A embeds into a (k+1)-type B, then A is a (k+1)-type. --

abstract
  is-trunc-is-emb : {i j : Level} (k : 𝕋) {A : UU i} {B : UU j}
    (f : A → B) → is-emb f → is-trunc (succ-𝕋 k) B → is-trunc (succ-𝕋 k) A
  is-trunc-is-emb k f Ef H x y =
    is-trunc-is-equiv k (Id (f x) (f y)) (ap f {x} {y}) (Ef x y) (H (f x) (f y))

abstract
  is-trunc-emb : {i j : Level} (k : 𝕋) {A : UU i} {B : UU j} →
    (f : A ↪ B) → is-trunc (succ-𝕋 k) B → is-trunc (succ-𝕋 k) A
  is-trunc-emb k f = is-trunc-is-emb k (map-emb f) (is-emb-map-emb f)

-- Truncated maps

is-trunc-map :
  {i j : Level} (k : 𝕋) {A : UU i} {B : UU j} → (A → B) → UU (i ⊔ j)
is-trunc-map k f = (y : _) → is-trunc k (fib f y)

trunc-map : {i j : Level} (k : 𝕋) (A : UU i) (B : UU j) → UU (i ⊔ j)
trunc-map k A B = Σ (A → B) (is-trunc-map k)

abstract
  is-trunc-pr1-is-trunc-fam :
    {i j : Level} (k : 𝕋) {A : UU i} (B : A → UU j) →
    ((x : A) → is-trunc k (B x)) → is-trunc-map k (pr1 {i} {j} {A} {B})
  is-trunc-pr1-is-trunc-fam k B H x =
    is-trunc-equiv k (B x) (equiv-fib-fam-fib-pr1 B x) (H x)

trunc-pr1 :
  {i j : Level} (k : 𝕋) {A : UU i} (B : A → UU-Truncated-Type k j) →
  trunc-map k (Σ A (λ x → pr1 (B x))) A
trunc-pr1 k B =
  pair pr1 (is-trunc-pr1-is-trunc-fam k (λ x → pr1 (B x)) (λ x → pr2 (B x)))

abstract
  is-trunc-fam-is-trunc-pr1 : {i j : Level} (k : 𝕋) {A : UU i} (B : A → UU j) →
    is-trunc-map k (pr1 {i} {j} {A} {B}) → ((x : A) → is-trunc k (B x))
  is-trunc-fam-is-trunc-pr1 k B is-trunc-pr1 x =
    is-trunc-equiv k (fib pr1 x) (equiv-fib-pr1-fib-fam B x) (is-trunc-pr1 x)

abstract
  is-trunc-map-is-trunc-ap : {i j : Level} (k : 𝕋) {A : UU i} {B : UU j}
    (f : A → B) → ((x y : A) → is-trunc-map k (ap f {x = x} {y = y})) →
    is-trunc-map (succ-𝕋 k) f
  is-trunc-map-is-trunc-ap k f is-trunc-ap-f b (pair x p) (pair x' p') =
    is-trunc-is-equiv k
      ( fib (ap f) (p ∙ (inv p')))
      ( fib-ap-eq-fib f (pair x p) (pair x' p'))
      ( is-equiv-fib-ap-eq-fib f (pair x p) (pair x' p'))
      ( is-trunc-ap-f x x' (p ∙ (inv p')))

abstract
  is-trunc-ap-is-trunc-map : {i j : Level} (k : 𝕋) {A : UU i} {B : UU j}
    (f : A → B) → is-trunc-map (succ-𝕋 k) f →
    (x y : A) → is-trunc-map k (ap f {x = x} {y = y})
  is-trunc-ap-is-trunc-map k f is-trunc-map-f x y p =
    is-trunc-is-equiv' k
      ( Id (pair x p) (pair y refl))
      ( eq-fib-fib-ap f x y p)
      ( is-equiv-eq-fib-fib-ap f x y p)
      ( is-trunc-map-f (f y) (pair x p) (pair y refl))

is-prop-map : {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
is-prop-map f = (b : _) → is-trunc neg-one-𝕋 (fib f b)

abstract
  is-emb-is-prop-map : {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
    is-prop-map f → is-emb f
  is-emb-is-prop-map f is-prop-map-f x y =
    is-equiv-is-contr-map
      ( is-trunc-ap-is-trunc-map neg-two-𝕋 f is-prop-map-f x y)

abstract
  is-prop-map-is-emb : {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
    is-emb f → is-prop-map f
  is-prop-map-is-emb f is-emb-f =
    is-trunc-map-is-trunc-ap neg-two-𝕋 f
      ( λ x y → is-contr-map-is-equiv (is-emb-f x y))

fib-prop-emb :
  {i j : Level} {A : UU i} {B : UU j} (f : A ↪ B) → B → UU-Prop (i ⊔ j)
fib-prop-emb f y =
  pair ( fib (map-emb f) y)
       ( is-prop-map-is-emb (map-emb f) (is-emb-map-emb f) y)

abstract
  is-emb-pr1-is-subtype : {i j : Level} {A : UU i} {B : A → UU j} →
    is-subtype B → is-emb (pr1 {B = B})
  is-emb-pr1-is-subtype {B = B} H =
    is-emb-is-prop-map pr1
      ( λ x → is-trunc-equiv neg-one-𝕋 (B x) (equiv-fib-fam-fib-pr1 _ x) (H x))

equiv-ap-pr1-is-subtype : {i j : Level} {A : UU i} {B : A → UU j} →
  is-subtype B → {s t : Σ A B} → Id s t ≃ Id (pr1 s) (pr1 t)
equiv-ap-pr1-is-subtype is-subtype-B {s} {t} =
  pair (ap pr1) (is-emb-pr1-is-subtype is-subtype-B s t)

abstract
  is-subtype-is-emb-pr1 : {i j : Level} {A : UU i} {B : A → UU j} →
    is-emb (pr1 {B = B}) → is-subtype B
  is-subtype-is-emb-pr1 is-emb-pr1-B x =
    is-trunc-equiv neg-one-𝕋
      ( fib pr1 x)
      ( equiv-fib-pr1-fib-fam _ x)
      ( is-prop-map-is-emb pr1 is-emb-pr1-B x)

abstract
  is-trunc-succ-subtype :
    {i j : Level} (k : 𝕋) {A : UU i} {P : A → UU j} →
    ((x : A) → is-prop (P x)) →
    is-trunc (succ-𝕋 k) A → is-trunc (succ-𝕋 k) (Σ A P)
  is-trunc-succ-subtype k H is-trunc-A =
    is-trunc-is-emb k pr1 (is-emb-pr1-is-subtype H) is-trunc-A

is-fiberwise-trunc : {l1 l2 l3 : Level} (k : 𝕋)  {A : UU l1} {B : A → UU l2}
  {C : A → UU l3} (f : (x : A) → B x → C x) → UU (l1 ⊔ (l2 ⊔ l3))
is-fiberwise-trunc k f = (x : _) → is-trunc-map k (f x)

abstract
  is-trunc-tot-is-fiberwise-trunc : {l1 l2 l3 : Level} (k : 𝕋)
    {A : UU l1} {B : A → UU l2} {C : A → UU l3} (f : (x : A) → B x → C x) →
    is-fiberwise-trunc k f → is-trunc-map k (tot f)
  is-trunc-tot-is-fiberwise-trunc k f is-fiberwise-trunc-f (pair x z) =
    is-trunc-is-equiv k
      ( fib (f x) z)
      ( fib-ftr-fib-tot f (pair x z))
      ( is-equiv-fib-ftr-fib-tot f (pair x z))
      ( is-fiberwise-trunc-f x z)

abstract
  is-fiberwise-trunc-is-trunc-tot : {l1 l2 l3 : Level} (k : 𝕋)
    {A : UU l1} {B : A → UU l2} {C : A → UU l3} (f : (x : A) → B x → C x) →
    is-trunc-map k (tot f) → is-fiberwise-trunc k f
  is-fiberwise-trunc-is-trunc-tot k f is-trunc-tot-f x z =
    is-trunc-is-equiv k
      ( fib (tot f) (pair x z))
      ( fib-tot-fib-ftr f (pair x z))
      ( is-equiv-fib-tot-fib-ftr f (pair x z))
      ( is-trunc-tot-f (pair x z))

-- Exercises

-- Exercise 8.1

-- Exercise 8.1

diagonal : {l : Level} (A : UU l) → A → A × A
diagonal A x = pair x x

abstract
  is-prop-is-equiv-diagonal : {l : Level} (A : UU l) →
    is-equiv (diagonal A) → is-prop A
  is-prop-is-equiv-diagonal A is-equiv-d =
    is-prop-is-prop' ( λ x y →
      let α = issec-map-inv-is-equiv is-equiv-d (pair x y) in
      ( inv (ap pr1 α)) ∙ (ap pr2 α))

eq-fib-diagonal : {l : Level} (A : UU l) (t : A × A) →
  fib (diagonal A) t → Id (pr1 t) (pr2 t)
eq-fib-diagonal A (pair x y) (pair z α) = (inv (ap pr1 α)) ∙ (ap pr2 α)

fib-diagonal-eq : {l : Level} (A : UU l) (t : A × A) →
  Id (pr1 t) (pr2 t) → fib (diagonal A) t
fib-diagonal-eq A (pair x y) β =
  pair x (eq-pair-triv (pair refl β))

issec-fib-diagonal-eq : {l : Level} (A : UU l) (t : A × A) →
  ((eq-fib-diagonal A t) ∘ (fib-diagonal-eq A t)) ~ id
issec-fib-diagonal-eq A (pair x .x) refl = refl

isretr-fib-diagonal-eq : {l : Level} (A : UU l) (t : A × A) →
  ((fib-diagonal-eq A t) ∘ (eq-fib-diagonal A t)) ~ id
isretr-fib-diagonal-eq A .(pair z z) (pair z refl) = refl

abstract
  is-equiv-eq-fib-diagonal : {l : Level} (A : UU l) (t : A × A) →
    is-equiv (eq-fib-diagonal A t)
  is-equiv-eq-fib-diagonal A t =
    is-equiv-has-inverse
      ( fib-diagonal-eq A t)
      ( issec-fib-diagonal-eq A t)
      ( isretr-fib-diagonal-eq A t)

abstract
  is-trunc-is-trunc-diagonal : {l : Level} (k : 𝕋) (A : UU l) →
    is-trunc-map k (diagonal A) → is-trunc (succ-𝕋 k) A
  is-trunc-is-trunc-diagonal k A is-trunc-d x y =
    is-trunc-is-equiv' k
      ( fib (diagonal A) (pair x y))
      ( eq-fib-diagonal A (pair x y))
      ( is-equiv-eq-fib-diagonal A (pair x y))
      ( is-trunc-d (pair x y))

abstract
  is-trunc-diagonal-is-trunc : {l : Level} (k : 𝕋) (A : UU l) →
    is-trunc (succ-𝕋 k) A → is-trunc-map k (diagonal A)
  is-trunc-diagonal-is-trunc k A is-trunc-A t =
    is-trunc-is-equiv k
      ( Id (pr1 t) (pr2 t))
      ( eq-fib-diagonal A t)
      ( is-equiv-eq-fib-diagonal A t)
      ( is-trunc-A (pr1 t) (pr2 t))

-- Exercise 8.2

-- Exercise 8.2(a)

abstract
  is-trunc-Σ : {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
    is-trunc k A → ((x : A) → is-trunc k (B x)) → is-trunc k (Σ A B)
  is-trunc-Σ neg-two-𝕋 is-trunc-A is-trunc-B =
    is-contr-Σ is-trunc-A is-trunc-B
  is-trunc-Σ (succ-𝕋 k) {B = B} is-trunc-A is-trunc-B s t =
    is-trunc-is-equiv k
      ( Σ (Id (pr1 s) (pr1 t)) (λ p → Id (tr B p (pr2 s)) (pr2 t)))
      ( pair-eq)
      ( is-equiv-pair-eq s t)
      ( is-trunc-Σ k
        ( is-trunc-A (pr1 s) (pr1 t))
        ( λ p → is-trunc-B (pr1 t) (tr B p (pr2 s)) (pr2 t)))

abstract
  is-trunc-prod : {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
    is-trunc k A → is-trunc k B → is-trunc k (A × B)
  is-trunc-prod k is-trunc-A is-trunc-B =
    is-trunc-Σ k is-trunc-A (λ x → is-trunc-B)

abstract
  is-prop-Σ : {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-prop A → is-subtype B → is-prop (Σ A B)
  is-prop-Σ = is-trunc-Σ neg-one-𝕋

Σ-Prop :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : type-Prop P → UU-Prop l2) →
  UU-Prop (l1 ⊔ l2)
Σ-Prop P Q =
  pair
    ( Σ (type-Prop P) (λ p → type-Prop (Q p)))
    ( is-prop-Σ
      ( is-prop-type-Prop P)
      ( λ p → is-prop-type-Prop (Q p)))

abstract
  is-prop-prod : {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-prop A → is-prop B → is-prop (A × B)
  is-prop-prod = is-trunc-prod neg-one-𝕋

prod-Prop : {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU-Prop (l1 ⊔ l2)
prod-Prop P Q =
  pair
    ( type-Prop P × type-Prop Q)
    ( is-prop-prod (is-prop-type-Prop P) (is-prop-type-Prop Q))

abstract
  is-set-Σ : {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-set A → ((x : A) → is-set (B x)) → is-set (Σ A B)
  is-set-Σ = is-trunc-Σ zero-𝕋

set-Σ :
  {l1 l2 : Level} (A : UU-Set l1) (B : pr1 A → UU-Set l2) → UU-Set (l1 ⊔ l2)
set-Σ (pair A is-set-A) B =
  pair
    ( Σ A (λ x → (pr1 (B x))))
    ( is-set-Σ is-set-A (λ x → pr2 (B x)))

abstract
  is-set-prod : {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-set A → is-set B → is-set (A × B)
  is-set-prod = is-trunc-prod zero-𝕋

set-prod :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2) → UU-Set (l1 ⊔ l2)
set-prod (pair A is-set-A) (pair B is-set-B) =
  pair (A × B) (is-set-prod is-set-A is-set-B)

-- Exercise 8.2 (b)

abstract
  is-trunc-Id : {l : Level} (k : 𝕋) {A : UU l} →
    is-trunc k A → (x y : A) → is-trunc k (Id x y)
  is-trunc-Id neg-two-𝕋 is-trunc-A = is-prop-is-contr is-trunc-A
  is-trunc-Id (succ-𝕋 k) is-trunc-A x y =
    is-trunc-succ-is-trunc k {A = Id x y} (is-trunc-A x y)

-- Exercise 8.2 (c)

abstract
  is-trunc-map-is-trunc-domain-codomain : {l1 l2 : Level} (k : 𝕋) {A : UU l1}
    {B : UU l2} {f : A → B} → is-trunc k A → is-trunc k B → is-trunc-map k f
  is-trunc-map-is-trunc-domain-codomain k {f = f} is-trunc-A is-trunc-B b =
    is-trunc-Σ k is-trunc-A (λ x → is-trunc-Id k is-trunc-B (f x) b)

-- Exercise 8.2 (d)

abstract
  is-trunc-fam-is-trunc-Σ :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
    is-trunc k A → is-trunc k (Σ A B) → (x : A) → is-trunc k (B x)
  is-trunc-fam-is-trunc-Σ k {B = B} is-trunc-A is-trunc-ΣAB x =
    is-trunc-equiv' k
      ( fib pr1 x)
      ( equiv-fib-fam-fib-pr1 B x)
      ( is-trunc-map-is-trunc-domain-codomain k is-trunc-ΣAB is-trunc-A x)

-- Exercise 8.3

abstract
  is-prop-Eq-𝟚 : (x y : bool) → is-prop (Eq-𝟚 x y)
  is-prop-Eq-𝟚 true true = is-prop-unit
  is-prop-Eq-𝟚 true false = is-prop-empty
  is-prop-Eq-𝟚 false true = is-prop-empty
  is-prop-Eq-𝟚 false false = is-prop-unit

abstract
  is-set-bool : is-set bool
  is-set-bool = is-set-prop-in-id Eq-𝟚 is-prop-Eq-𝟚 reflexive-Eq-𝟚 (λ x y → eq-Eq-𝟚)

set-bool : UU-Set lzero
set-bool = pair bool is-set-bool

-- Exercise 8.4

abstract
  is-prop'-coprod :
    {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
    (P → ¬ Q) → is-prop' P → is-prop' Q → is-prop' (coprod P Q)
  is-prop'-coprod
    {P = P} {Q = Q} f is-prop-P is-prop-Q (inl p) (inl p') =
    ap inl (is-prop-P p p')
  is-prop'-coprod
    {P = P} {Q = Q} f is-prop-P is-prop-Q (inl p) (inr q') =
    ex-falso (f p q')
  is-prop'-coprod
    {P = P} {Q = Q} f is-prop-P is-prop-Q (inr q) (inl p') =
    ex-falso (f p' q)
  is-prop'-coprod
    {P = P} {Q = Q} f is-prop-P is-prop-Q (inr q) (inr q') =
    ap inr (is-prop-Q q q')

abstract
  is-prop-coprod :
    {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
    (P → ¬ Q) → is-prop P → is-prop Q → is-prop (coprod P Q)
  is-prop-coprod f is-prop-P is-prop-Q =
    is-prop-is-prop'
      ( is-prop'-coprod f
        ( eq-is-prop is-prop-P)
        ( eq-is-prop is-prop-Q))

abstract
  is-trunc-succ-empty : (k : 𝕋) → is-trunc (succ-𝕋 k) empty
  is-trunc-succ-empty k = ind-empty

abstract
  is-trunc-coprod : {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
    is-trunc (succ-𝕋 (succ-𝕋 k)) A → is-trunc (succ-𝕋 (succ-𝕋 k)) B →
    is-trunc (succ-𝕋 (succ-𝕋 k)) (coprod A B)
  is-trunc-coprod k {A} {B} is-trunc-A is-trunc-B (inl x) (inl y) =
    is-trunc-is-equiv (succ-𝕋 k)
      ( Eq-coprod A B (inl x) (inl y))
      ( Eq-coprod-eq A B (inl x) (inl y))
      ( is-equiv-Eq-coprod-eq A B (inl x) (inl y))
      ( is-trunc-equiv' (succ-𝕋 k)
        ( Id x y)
        ( equiv-raise _ (Id x y))
        ( is-trunc-A x y))
  is-trunc-coprod k {A} {B} is-trunc-A is-trunc-B (inl x) (inr y) =
    is-trunc-is-equiv (succ-𝕋 k)
      ( Eq-coprod A B (inl x) (inr y))
      ( Eq-coprod-eq A B (inl x) (inr y))
      ( is-equiv-Eq-coprod-eq A B (inl x) (inr y))
      ( is-trunc-equiv' (succ-𝕋 k)
        ( empty)
        ( equiv-raise _ empty)
        ( is-trunc-succ-empty k))
  is-trunc-coprod k {A} {B} is-trunc-A is-trunc-B (inr x) (inl y) =
    is-trunc-is-equiv (succ-𝕋 k)
      ( Eq-coprod A B (inr x) (inl y))
      ( Eq-coprod-eq A B (inr x) (inl y))
      ( is-equiv-Eq-coprod-eq A B (inr x) (inl y))
      ( is-trunc-equiv' (succ-𝕋 k)
        ( empty)
        ( equiv-raise _ empty)
        ( is-trunc-succ-empty k))
  is-trunc-coprod k {A} {B} is-trunc-A is-trunc-B (inr x) (inr y) =
    is-trunc-is-equiv (succ-𝕋 k)
      ( Eq-coprod A B (inr x) (inr y))
      ( Eq-coprod-eq A B (inr x) (inr y))
      ( is-equiv-Eq-coprod-eq A B (inr x) (inr y))
      ( is-trunc-equiv' (succ-𝕋 k)
        ( Id x y)
        ( equiv-raise _ (Id x y))
        ( is-trunc-B x y))

abstract
  is-set-coprod : {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-set A → is-set B → is-set (coprod A B)
  is-set-coprod = is-trunc-coprod neg-two-𝕋

set-coprod :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2) → UU-Set (l1 ⊔ l2)
set-coprod (pair A is-set-A) (pair B is-set-B) =
  pair (coprod A B) (is-set-coprod is-set-A is-set-B)

abstract
  is-set-unit : is-set unit
  is-set-unit = is-trunc-succ-is-trunc neg-one-𝕋 is-prop-unit

set-unit : UU-Set lzero
set-unit = pair unit is-set-unit

abstract
  is-set-ℤ : is-set ℤ
  is-set-ℤ = is-set-coprod is-set-ℕ (is-set-coprod is-set-unit is-set-ℕ)

set-ℤ : UU-Set lzero
set-ℤ = pair ℤ is-set-ℤ

ℤ-Set : UU-Set lzero
ℤ-Set = pair ℤ is-set-ℤ

is-set-empty : is-set empty
is-set-empty ()

abstract
  is-set-Fin :
    (n : ℕ) → is-set (Fin n)
  is-set-Fin zero-ℕ = is-set-empty
  is-set-Fin (succ-ℕ n) =
    is-set-coprod (is-set-Fin n) is-set-unit

set-Fin :
  (n : ℕ) → UU-Set lzero
set-Fin n = pair (Fin n) (is-set-Fin n)

-- Exercise 8.7

abstract
  is-trunc-retract-of : {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
    A retract-of B → is-trunc k B → is-trunc k A
  is-trunc-retract-of neg-two-𝕋 (pair i (pair r H)) is-trunc-B =
    is-contr-retract-of _ (pair i (pair r H)) is-trunc-B
  is-trunc-retract-of (succ-𝕋 k) (pair i retr-i) is-trunc-B x y =
    is-trunc-retract-of k
      ( pair (ap i) (retr-ap i retr-i x y))
      ( is-trunc-B (i x) (i y))

-- Exercise 8.8

is-injective-const-true : is-injective (const unit bool true)
is-injective-const-true {x} {y} p = center (is-prop-unit x y)

is-injective-const-false : is-injective (const unit bool false)
is-injective-const-false {x} {y} p = center (is-prop-unit x y)

abstract
  is-equiv-is-prop : {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-prop A →
    is-prop B → {f : A → B} → (B → A) → is-equiv f
  is-equiv-is-prop is-prop-A is-prop-B {f} g =
    is-equiv-has-inverse
      ( g)
      ( λ y → center (is-prop-B (f (g y)) y))
      ( λ x → center (is-prop-A (g (f x)) x))

equiv-prop :
  { l1 l2 : Level} {A : UU l1} {B : UU l2} → is-prop A → is-prop B →
  ( A → B) → (B → A) → A ≃ B
equiv-prop is-prop-A is-prop-B f g =
  pair f (is-equiv-is-prop is-prop-A is-prop-B g)

equiv-total-subtype :
  { l1 l2 l3 : Level} {A : UU l1} {P : A → UU l2} {Q : A → UU l3} →
  ( is-subtype-P : is-subtype P) (is-subtype-Q : is-subtype Q) →
  ( f : (x : A) → P x → Q x) →
  ( g : (x : A) → Q x → P x) →
  ( Σ A P) ≃ (Σ A Q)
equiv-total-subtype is-subtype-P is-subtype-Q f g =
  pair
    ( tot f)
    ( is-equiv-tot-is-fiberwise-equiv {f = f}
      ( λ x → is-equiv-is-prop (is-subtype-P x) (is-subtype-Q x) (g x)))

abstract
  is-emb-is-injective : {l1 l2 : Level} {A : UU l1} (is-set-A : is-set A)
    {B : UU l2} (is-set-B : is-set B) (f : A → B) →
    is-injective f → is-emb f
  is-emb-is-injective is-set-A is-set-B f is-injective-f x y =
    is-equiv-is-prop
      ( is-set-A x y)
      ( is-set-B (f x) (f y))
      ( is-injective-f)

-- Exercise 8.9

abstract
  is-trunc-const-is-trunc : {l : Level} (k : 𝕋) {A : UU l} →
    is-trunc (succ-𝕋 k) A → (x : A) → is-trunc-map k (const unit A x)
  is-trunc-const-is-trunc k is-trunc-A x y =
    is-trunc-equiv k
      ( Id x y)
      ( left-unit-law-Σ (λ t → Id x y))
      ( is-trunc-A x y)

abstract
  is-trunc-is-trunc-const : {l : Level} (k : 𝕋) {A : UU l} →
    ((x : A) → is-trunc-map k (const unit A x)) → is-trunc (succ-𝕋 k) A
  is-trunc-is-trunc-const k is-trunc-const x y =
    is-trunc-equiv' k
      ( Σ unit (λ t → Id x y))
      ( left-unit-law-Σ (λ t → Id x y))
      ( is-trunc-const x y)

-- Exercise 8.10

map-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (g : B → X) (h : A → B) →
  (x : X) → fib (g ∘ h) x → Σ (fib g x) (λ t → fib h (pr1 t))
map-fib-comp g h x (pair a p) =
  pair
    ( pair (h a) p)
    ( pair a refl)

inv-map-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (g : B → X) (h : A → B) →
  (x : X) → Σ (fib g x) (λ t → fib h (pr1 t)) → fib (g ∘ h) x
inv-map-fib-comp g h c t =
  pair (pr1 (pr2 t)) ((ap g (pr2 (pr2 t))) ∙ (pr2 (pr1 t)))

issec-inv-map-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (g : B → X) (h : A → B) →
  (x : X) →
  ((map-fib-comp g h x) ∘ (inv-map-fib-comp g h x)) ~ id
issec-inv-map-fib-comp g h x
  (pair (pair .(h a) refl) (pair a refl)) = refl

isretr-inv-map-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (g : B → X) (h : A → B) (x : X) →
  ((inv-map-fib-comp g h x) ∘ (map-fib-comp g h x)) ~ id
isretr-inv-map-fib-comp g h .(g (h a)) (pair a refl) = refl

abstract
  is-equiv-map-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
    {X : UU l3} (g : B → X) (h : A → B) (x : X) →
    is-equiv (map-fib-comp g h x)
  is-equiv-map-fib-comp g h x =
    is-equiv-has-inverse
      ( inv-map-fib-comp g h x)
      ( issec-inv-map-fib-comp g h x)
      ( isretr-inv-map-fib-comp g h x)

abstract
  is-equiv-inv-map-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
    {X : UU l3} (g : B → X) (h : A → B) (x : X) →
    is-equiv (inv-map-fib-comp g h x)
  is-equiv-inv-map-fib-comp g h x =
    is-equiv-has-inverse
      ( map-fib-comp g h x)
      ( isretr-inv-map-fib-comp g h x)
      ( issec-inv-map-fib-comp g h x)

abstract
  is-trunc-map-htpy : {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    (f g : A → B) → f ~ g → is-trunc-map k g → is-trunc-map k f
  is-trunc-map-htpy k {A} f g H is-trunc-g b =
    is-trunc-is-equiv k
      ( Σ A (λ z → Id (g z) b))
      ( fib-triangle f g id H b)
      ( is-fiberwise-equiv-is-equiv-triangle f g id H is-equiv-id b)
      ( is-trunc-g b)

abstract
  is-trunc-map-comp : {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    {X : UU l3} (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-trunc-map k g → is-trunc-map k h → is-trunc-map k f
  is-trunc-map-comp k f g h H is-trunc-g is-trunc-h =
    is-trunc-map-htpy k f (g ∘ h) H
      ( λ x → is-trunc-is-equiv k
        ( Σ (fib g x) (λ t → fib h (pr1 t)))
        ( map-fib-comp g h x)
        ( is-equiv-map-fib-comp g h x)
        ( is-trunc-Σ k
          ( is-trunc-g x)
          ( λ t → is-trunc-h (pr1 t))))

abstract
  is-trunc-map-right-factor : {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    {X : UU l3} (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-trunc-map k g → is-trunc-map k f → is-trunc-map k h
  is-trunc-map-right-factor k {A} f g h H is-trunc-g is-trunc-f b =
    is-trunc-fam-is-trunc-Σ k
      ( is-trunc-g (g b))
      ( is-trunc-is-equiv' k
        ( Σ A (λ z → Id (g (h z)) (g b)))
        ( map-fib-comp g h (g b))
        ( is-equiv-map-fib-comp g h (g b))
        ( is-trunc-map-htpy k (g ∘ h) f (inv-htpy H) is-trunc-f (g b)))
      ( pair b refl)

abstract
  is-trunc-map-succ-is-trunc-map :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    (f : A → B) → is-trunc-map k f → is-trunc-map (succ-𝕋 k) f
  is-trunc-map-succ-is-trunc-map k f is-trunc-f b =
    is-trunc-succ-is-trunc k (is-trunc-f b)

--------------------------------------------------------------------------------

{- Exercise -}

is-decidable-retract-of :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  A retract-of B → is-decidable B → is-decidable A
is-decidable-retract-of (pair i (pair r H)) (inl b) = inl (r b)
is-decidable-retract-of (pair i (pair r H)) (inr f) = inr (f ∘ i)

is-decidable-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  (is-equiv-f : is-equiv f) → is-decidable B → is-decidable A
is-decidable-is-equiv {f = f} (pair (pair g G) (pair h H)) =
  is-decidable-retract-of (pair f (pair h H))

is-decidable-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-decidable B → is-decidable A
is-decidable-equiv e = is-decidable-iff (map-inv-equiv e) (map-equiv e)

is-decidable-equiv' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-decidable A → is-decidable B
is-decidable-equiv' e = is-decidable-equiv (inv-equiv e)

has-decidable-equality-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  has-decidable-equality A → ((x : A) → has-decidable-equality (B x)) →
  has-decidable-equality (Σ A B)
has-decidable-equality-Σ dA dB (pair x y) (pair x' y') with dA x x'
... | inr np = inr (λ r → np (ap pr1 r))
... | inl p =
  is-decidable-iff eq-pair' pair-eq
    ( is-decidable-equiv'
      ( left-unit-law-Σ-is-contr-gen
        ( λ α → Id (tr _ α y) y')
        ( is-contr-is-prop-inh
          ( is-set-has-decidable-equality dA x x') p)
        ( p))
      ( dB x' (tr _ p y) y'))

--------------------------------------------------------------------------------

{- We show that if f : A → B is an embedding, then the induced map
   Σ A (C ∘ f) → Σ A C is also an embedding. -}

is-emb-map-Σ-map-base :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  is-emb f → is-emb (map-Σ-map-base f C)
is-emb-map-Σ-map-base f C is-emb-f =
  is-emb-is-prop-map
    ( map-Σ-map-base f C)
    ( λ x →
      is-prop-equiv'
        ( fib f (pr1 x))
        ( equiv-fib-map-Σ-map-base-fib f C x)
        ( is-prop-map-is-emb f is-emb-f (pr1 x)))
