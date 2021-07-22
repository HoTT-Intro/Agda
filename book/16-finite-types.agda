{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module book.16-finite-types where

open import book.15-image public

--------------------------------------------------------------------------------

-- Section 16 Finite types

--------------------------------------------------------------------------------

-- Section 16.1 Counting in type theory

-- Definition 16.1.1

count : {l : Level} → UU l → UU l
count X = Σ ℕ (λ k → Fin k ≃ X)

number-of-elements-count : {l : Level} {X : UU l} → count X → ℕ
number-of-elements-count = pr1

equiv-count :
  {l : Level} {X : UU l} (e : count X) → Fin (number-of-elements-count e) ≃ X
equiv-count = pr2

map-equiv-count :
  {l : Level} {X : UU l} (e : count X) → Fin (number-of-elements-count e) → X
map-equiv-count e = map-equiv (equiv-count e)

map-inv-equiv-count :
  {l : Level} {X : UU l} (e : count X) → X → Fin (number-of-elements-count e)
map-inv-equiv-count e = map-inv-equiv (equiv-count e)

-- Example 16.1.2

-- Fin k has a count

count-Fin : (k : ℕ) → count (Fin k)
count-Fin k = pair k equiv-id

-- Types equipped with countings are closed under equivalences

abstract
  equiv-count-equiv :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) (f : count X) →
    Fin (number-of-elements-count f) ≃ Y
  equiv-count-equiv e f = e ∘e (equiv-count f)

count-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) → count X → count Y
count-equiv e f =
  pair (number-of-elements-count f) (equiv-count-equiv e f)

count-equiv' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) → count Y → count X
count-equiv' e = count-equiv (inv-equiv e)

count-is-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y} →
  is-equiv f → count X → count Y
count-is-equiv is-equiv-f = count-equiv (pair _ is-equiv-f)

count-is-equiv' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y} →
  is-equiv f → count Y → count X
count-is-equiv' is-equiv-f = count-equiv' (pair _ is-equiv-f)

-- Example 16.1.3

-- A type as 0 elements if and only if it is empty

is-empty-is-zero-number-of-elements-count :
  {l : Level} {X : UU l} (e : count X) →
  is-zero-ℕ (number-of-elements-count e) → is-empty X
is-empty-is-zero-number-of-elements-count (pair .zero-ℕ e) refl x =
  map-inv-equiv e x

is-zero-number-of-elements-count-is-empty :
  {l : Level} {X : UU l} (e : count X) →
  is-empty X → is-zero-ℕ (number-of-elements-count e)
is-zero-number-of-elements-count-is-empty (pair zero-ℕ e) H = refl
is-zero-number-of-elements-count-is-empty (pair (succ-ℕ k) e) H =
  ex-falso (H (map-equiv e zero-Fin))

count-is-empty :
  {l : Level} {X : UU l} → is-empty X → count X
count-is-empty H =
  pair zero-ℕ (inv-equiv (pair H (is-equiv-is-empty' H)))

count-empty : count empty
count-empty = count-Fin zero-ℕ

-- Example 16.1.4

-- A type has 1 element if and only if it is contractible

count-is-contr :
  {l : Level} {X : UU l} → is-contr X → count X
count-is-contr H = pair one-ℕ (equiv-is-contr is-contr-Fin-one-ℕ H)

is-contr-is-one-number-of-elements-count :
  {l : Level} {X : UU l} (e : count X) →
  is-one-ℕ (number-of-elements-count e) → is-contr X
is-contr-is-one-number-of-elements-count (pair .(succ-ℕ zero-ℕ) e) refl =
  is-contr-equiv' (Fin one-ℕ) e is-contr-Fin-one-ℕ

is-one-number-of-elements-count-is-contr :
  {l : Level} {X : UU l} (e : count X) →
  is-contr X → is-one-ℕ (number-of-elements-count e)
is-one-number-of-elements-count-is-contr (pair zero-ℕ e) H =
  ex-falso (map-inv-equiv e (center H))
is-one-number-of-elements-count-is-contr (pair (succ-ℕ zero-ℕ) e) H =
  refl
is-one-number-of-elements-count-is-contr (pair (succ-ℕ (succ-ℕ k)) e) H =
  ex-falso
    ( Eq-Fin-eq
      ( is-injective-map-equiv e
        ( eq-is-contr' H (map-equiv e zero-Fin) (map-equiv e neg-one-Fin))))

count-unit : count unit
count-unit = count-is-contr is-contr-unit

-- Example 16.1.5

-- Propositions have countings if and only if they are decidable

is-decidable-count :
  {l : Level} {X : UU l} → count X → is-decidable X
is-decidable-count (pair zero-ℕ e) =
  inr (is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl)
is-decidable-count (pair (succ-ℕ k) e) =
  inl (map-equiv e zero-Fin)

count-is-decidable-is-prop :
  {l : Level} {A : UU l} → is-prop A → is-decidable A → count A
count-is-decidable-is-prop H (inl x) =
  count-is-contr (is-proof-irrelevant-is-prop H x)
count-is-decidable-is-prop H (inr f) = count-is-empty f

count-decidable-Prop :
  {l1 : Level} (P : UU-Prop l1) →
  is-decidable (type-Prop P) → count (type-Prop P)
count-decidable-Prop P (inl p) =
  count-is-contr (is-proof-irrelevant-is-prop (is-prop-type-Prop P) p)
count-decidable-Prop P (inr f) = count-is-empty f

-- Example 16.1.6

-- Types with a count have decidable equality

has-decidable-equality-count :
  {l : Level} {X : UU l} → count X → has-decidable-equality X
has-decidable-equality-count (pair k e) =
  has-decidable-equality-equiv' e has-decidable-equality-Fin

{- We can count the elements of an identity type of a type that has decidable
   equality. -}

cases-count-eq :
  {l : Level} {X : UU l} (d : has-decidable-equality X) {x y : X}
  (e : is-decidable (Id x y)) → count (Id x y)
cases-count-eq d {x} {y} (inl p) =
  count-is-contr
    ( is-proof-irrelevant-is-prop (is-set-has-decidable-equality d x y) p)
cases-count-eq d (inr f) =
  count-is-empty f

count-eq :
  {l : Level} {X : UU l} → has-decidable-equality X → (x y : X) → count (Id x y)
count-eq d x y = cases-count-eq d (d x y)

cases-number-of-elements-count-eq' :
  {l : Level} {X : UU l} {x y : X} →
  is-decidable (Id x y) → ℕ
cases-number-of-elements-count-eq' (inl p) = one-ℕ
cases-number-of-elements-count-eq' (inr f) = zero-ℕ

number-of-elements-count-eq' :
  {l : Level} {X : UU l} (d : has-decidable-equality X) (x y : X) → ℕ
number-of-elements-count-eq' d x y =
  cases-number-of-elements-count-eq' (d x y)

cases-number-of-elements-count-eq :
  {l : Level} {X : UU l} (d : has-decidable-equality X) {x y : X}
  (e : is-decidable (Id x y)) →
  Id ( number-of-elements-count (cases-count-eq d e))
     ( cases-number-of-elements-count-eq' e)
cases-number-of-elements-count-eq d (inl p) = refl
cases-number-of-elements-count-eq d (inr f) = refl

number-of-elements-count-eq :
  {l : Level} {X : UU l} (d : has-decidable-equality X) (x y : X) →
  Id ( number-of-elements-count (count-eq d x y))
     ( number-of-elements-count-eq' d x y)
number-of-elements-count-eq d x y =
  cases-number-of-elements-count-eq d (d x y)

-- Theorem 16.1.7

-- Theorem 16.1.7 (i) Forward direction

-- Types equipped with a count are closed under coproducts

count-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  count X → count Y → count (coprod X Y)
count-coprod (pair k e) (pair l f) =
  pair
    ( add-ℕ k l)
    ( ( equiv-coprod e f) ∘e
      ( inv-equiv (coprod-Fin k l)))

number-of-elements-count-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : count X) (f : count Y) →
  Id ( number-of-elements-count (count-coprod e f))
     ( add-ℕ (number-of-elements-count e) (number-of-elements-count f))
number-of-elements-count-coprod (pair k e) (pair l f) = refl

-- Theorem 16.1.7 (ii) (a) Forward direction

count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (k : ℕ) (e : Fin k ≃ A) → ((x : A) → count (B x)) → count (Σ A B)
count-Σ' zero-ℕ e f =
  count-is-empty
    ( λ x →
      is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl (pr1 x))
count-Σ' {l1} {l2} {A} {B} (succ-ℕ k) e f =
  count-equiv
    ( ( equiv-Σ-equiv-base B e) ∘e
      ( ( inv-equiv
          ( right-distributive-Σ-coprod (Fin k) unit (B ∘ map-equiv e))) ∘e
        ( equiv-coprod
          ( equiv-id)
          ( inv-equiv
            ( left-unit-law-Σ (B ∘ (map-equiv e ∘ inr)))))))
    ( count-coprod
      ( count-Σ' k equiv-id (λ x → f (map-equiv e (inl x))))
      ( f (map-equiv e (inr star))))

abstract
  equiv-count-Σ' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    (k : ℕ) (e : Fin k ≃ A) (f : (x : A) → count (B x)) →
    Fin (number-of-elements-count (count-Σ' k e f)) ≃ Σ A B
  equiv-count-Σ' k e f = pr2 (count-Σ' k e f)

count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → ((x : A) → count (B x)) → count (Σ A B)
count-Σ (pair k e) f =
  pair (number-of-elements-count (count-Σ' k e f)) (equiv-count-Σ' k e f)

{- In order to compute the number of elements of a Σ-type, We introduce finite 
   sums and sums indexed by counted types. -}

sum-Fin-ℕ : {k : ℕ} → (Fin k → ℕ) → ℕ
sum-Fin-ℕ {zero-ℕ} f = zero-ℕ
sum-Fin-ℕ {succ-ℕ k} f = add-ℕ (sum-Fin-ℕ (λ x → f (inl x))) (f (inr star))

htpy-sum-Fin-ℕ :
  {k : ℕ} {f g : Fin k → ℕ} (H : f ~ g) → Id (sum-Fin-ℕ f) (sum-Fin-ℕ g)
htpy-sum-Fin-ℕ {zero-ℕ} H = refl
htpy-sum-Fin-ℕ {succ-ℕ k} H =
  ap-add-ℕ
    ( htpy-sum-Fin-ℕ (λ x → H (inl x)))
    ( H (inr star))

constant-sum-Fin-ℕ :
  (m n : ℕ) → Id (sum-Fin-ℕ (const (Fin m) ℕ n)) (mul-ℕ m n)
constant-sum-Fin-ℕ zero-ℕ n = refl
constant-sum-Fin-ℕ (succ-ℕ m) n = ap (add-ℕ' n) (constant-sum-Fin-ℕ m n)

sum-count-ℕ : {l : Level} {A : UU l} (e : count A) → (f : A → ℕ) → ℕ
sum-count-ℕ (pair k e) f = sum-Fin-ℕ (f ∘ (map-equiv e))

ap-sum-count-ℕ :
  {l : Level} {A : UU l} (e : count A) {f g : A → ℕ} (H : f ~ g) →
  Id (sum-count-ℕ e f) (sum-count-ℕ e g)
ap-sum-count-ℕ (pair k e) H = htpy-sum-Fin-ℕ (H ·r (map-equiv e))

constant-sum-count-ℕ :
  {l : Level} {A : UU l} (e : count A) (n : ℕ) →
  Id (sum-count-ℕ e (const A ℕ n)) (mul-ℕ (number-of-elements-count e) n)
constant-sum-count-ℕ (pair m e) n = constant-sum-Fin-ℕ m n

-- We compute the number of elements of a Σ-type

number-of-elements-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (k : ℕ) (e : Fin k ≃ A) →
  (f : (x : A) → count (B x)) →
  Id ( number-of-elements-count (count-Σ' k e f))
     ( sum-Fin-ℕ (λ x → number-of-elements-count (f (map-equiv e x)))) 
number-of-elements-count-Σ' zero-ℕ e f = refl
number-of-elements-count-Σ' (succ-ℕ k) e f =
  ( number-of-elements-count-coprod
    ( count-Σ' k equiv-id (λ x → f (map-equiv e (inl x))))
    ( f (map-equiv e (inr star)))) ∙
  ( ap
    ( add-ℕ' (number-of-elements-count (f (map-equiv e (inr star)))))
    ( number-of-elements-count-Σ' k equiv-id (λ x → f (map-equiv e (inl x)))))

number-of-elements-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (e : count A)
  (f : (x : A) → count (B x)) →
  Id ( number-of-elements-count (count-Σ e f))
     ( sum-count-ℕ e (λ x → number-of-elements-count (f x)))
number-of-elements-count-Σ (pair k e) f = number-of-elements-count-Σ' k e f

-- Theorem 16.1.7 (ii) (a) Converse direction

-- We show that if A and Σ A B can be counted, then each B x can be counted

count-fiber-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → count (Σ A B) → (x : A) → count (B x)
count-fiber-count-Σ {B = B} e f x =
  count-equiv
    ( equiv-fib-pr1 x)
    ( count-Σ f
      ( λ z → count-eq (has-decidable-equality-count e) (pr1 z) x))

{- As a corollary we obtain that if A and B can be counted, then the fibers of
   a map f : A → B can be counted. -}

count-fib :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  count A → count B → (y : B) → count (fib f y)
count-fib f count-A count-B =
  count-fiber-count-Σ count-B (count-equiv' (equiv-total-fib f) count-A)

-- Theorem 16.1.7 (ii) (b)

{- If Σ A B and each B x can be counted, and if B has a section, then A can be
   counted. -}

equiv-total-fib-map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  Σ (Σ A B) (fib (map-section b)) ≃ A
equiv-total-fib-map-section b = equiv-total-fib (map-section b)

count-fib-map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  count (Σ A B) → ((x : A) → count (B x)) →
  (t : Σ A B) → count (fib (map-section b) t)
count-fib-map-section {l1} {l2} {A} {B} b e f (pair y z) =
  count-equiv'
    ( ( ( left-unit-law-Σ-is-contr
            ( is-contr-total-path' y)
            ( pair y refl)) ∘e
        ( inv-assoc-Σ A
          ( λ x → Id x y)
          ( λ t → Id (tr B (pr2 t) (b (pr1 t))) z))) ∘e
      ( equiv-tot (λ x → equiv-pair-eq-Σ (pair x (b x)) (pair y z))))
    ( count-eq (has-decidable-equality-count (f y)) (b y) z)

count-base-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  count (Σ A B) → ((x : A) → count (B x)) → count A
count-base-count-Σ b e f =
  count-equiv
    ( equiv-total-fib-map-section b)
    ( count-Σ e (count-fib-map-section b e f))

{- More generally, if Σ A B and each B x can be counted, then A can be counted
   if and only if the type Σ A (¬ ∘ B) can be counted. However, to avoid having
   to invoke function extensionality, we show that if Σ A B and each B x can be
   counted, then A can be counted if and only if

   count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (f x)))),

   where f : (x : A) → count (B x). 

   Thus, we have a precise characterization of when A can be counted, if it is 
   given that Σ A B and each B x can be counted. -}

section-count-base-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count (Σ A B) →
  (f : (x : A) → count (B x)) →
  count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (f x)))) →
  (x : A) → coprod (B x) (is-zero-ℕ (number-of-elements-count (f x)))
section-count-base-count-Σ' e f g x with
  is-decidable-is-zero-ℕ (number-of-elements-count (f x))
... | inl p = inr p
... | inr H with is-successor-is-nonzero-ℕ H
... | (pair k p) = inl (map-equiv-count (f x) (tr Fin (inv p) zero-Fin))

count-base-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count (Σ A B) →
  (f : (x : A) → count (B x)) →
  count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (f x)))) → count A
count-base-count-Σ' {l1} {l2} {A} {B} e f g =
  count-base-count-Σ
    ( section-count-base-count-Σ' e f g)
    ( count-equiv'
      ( left-distributive-Σ-coprod A B
        ( λ x → is-zero-ℕ (number-of-elements-count (f x))))
      ( count-coprod e g))
    ( λ x →
      count-coprod
        ( f x)
        ( count-eq has-decidable-equality-ℕ
          ( number-of-elements-count (f x))
          ( zero-ℕ)))

-- Theorem 16.1.7 (ii) Consequences

-- A decidable subtype of a type that can be counted can be counted

count-decidable-subtype :
  {l1 l2 : Level} {X : UU l1} (P : X → UU-Prop l2) →
  ((x : X) → is-decidable (type-Prop (P x))) →
  count X → count (Σ X (λ x → type-Prop (P x)))
count-decidable-subtype P d e =
  count-Σ e (λ x → count-decidable-Prop (P x) (d x))

{- If A can be counted and Σ A P can be counted for a subtype of A, then P is
   decidable -}

is-decidable-count-Σ :
  {l1 l2 : Level} {X : UU l1} {P : X → UU l2} →
  count X → count (Σ X P) → (x : X) → is-decidable (P x)
is-decidable-count-Σ e f x =
  is-decidable-count (count-fiber-count-Σ e f x)

is-decidable-count-subtype :
  {l1 l2 : Level} {X : UU l1} (P : X → UU-Prop l2) → count X →
  count (Σ X (λ x → type-Prop (P x))) → (x : X) → is-decidable (type-Prop (P x))
is-decidable-count-subtype P = is-decidable-count-Σ

-- Theorem 16.1.7 (i) Converse direction

-- A coproduct X + Y has a count if and only if both X and Y have a count.

is-left : {l1 l2 : Level} {X : UU l1} {Y : UU l2} → coprod X Y → UU lzero
is-left (inl x) = unit
is-left (inr x) = empty

equiv-left-summand :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (Σ (coprod X Y) is-left) ≃ X
equiv-left-summand {l1} {l2} {X} {Y} =
  ( ( right-unit-law-coprod X) ∘e
    ( equiv-coprod right-unit-law-prod (right-absorption-prod Y))) ∘e
  ( right-distributive-Σ-coprod X Y is-left)

count-is-left :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (t : coprod X Y) → count (is-left t)
count-is-left (inl x) = count-unit
count-is-left (inr x) = count-empty

count-left-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (coprod X Y) → count X
count-left-coprod e = count-equiv equiv-left-summand (count-Σ e count-is-left)

is-right : {l1 l2 : Level} {X : UU l1} {Y : UU l2} → coprod X Y → UU lzero
is-right (inl x) = empty
is-right (inr x) = unit

equiv-right-summand :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (Σ (coprod X Y) is-right) ≃ Y
equiv-right-summand {l1} {l2} {X} {Y} =
  ( ( left-unit-law-coprod Y) ∘e
    ( equiv-coprod (right-absorption-prod X) right-unit-law-prod)) ∘e
    ( right-distributive-Σ-coprod X Y is-right)

count-is-right :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (t : coprod X Y) → count (is-right t)
count-is-right (inl x) = count-empty
count-is-right (inr x) = count-unit

count-right-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (coprod X Y) → count Y
count-right-coprod e =
  count-equiv equiv-right-summand (count-Σ e count-is-right)

-- Corollary 16.1.4

count-prod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count X → count Y → count (X × Y)
count-prod (pair k e) (pair l f) =
  pair
    ( mul-ℕ k l)
    ( ( equiv-prod e f) ∘e
      ( inv-equiv (prod-Fin k l)))

number-of-elements-count-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (count-A : count A)
  (count-B : count B) →
  Id ( number-of-elements-count
       ( count-prod count-A count-B))
     ( mul-ℕ
       ( number-of-elements-count count-A)
       ( number-of-elements-count count-B))
number-of-elements-count-prod (pair k e) (pair l f) = refl

equiv-left-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (y : Y) →
  (Σ (X × Y) (λ t → Id (pr2 t) y)) ≃ X
equiv-left-factor {l1} {l2} {X} {Y} y =
  ( ( right-unit-law-prod) ∘e
    ( equiv-tot
      ( λ x → equiv-is-contr (is-contr-total-path' y) is-contr-unit))) ∘e
  ( assoc-Σ X (λ x → Y) (λ t → Id (pr2 t) y))

count-left-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (X × Y) → Y → count X
count-left-factor e y =
  count-equiv
    ( equiv-left-factor y)
    ( count-Σ e
      ( λ z →
        count-eq
          ( has-decidable-equality-right-factor
            ( has-decidable-equality-count e)
            ( pr1 z))
          ( pr2 z)
          ( y)))

count-right-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (X × Y) → X → count Y
count-right-factor e x =
  count-left-factor (count-equiv commutative-prod e) x

--------------------------------------------------------------------------------

-- Double counting

-- The Maybe modality

Maybe : {l : Level} → UU l → UU l
Maybe X = coprod X unit

unit-Maybe : {l : Level} {X : UU l} → X → Maybe X
unit-Maybe = inl

is-emb-unit-Maybe : {l : Level} {X : UU l} → is-emb (unit-Maybe {X = X})
is-emb-unit-Maybe {l} {X} = is-emb-inl X unit

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

-- If f is an injective map and f (inl x) is an exception, then f exception is
-- not an exception.

is-not-exception-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) → is-exception-Maybe (f (inl x)) →
  is-not-exception-Maybe (f exception-Maybe)
is-not-exception-injective-map-exception-Maybe is-inj-f x p q =
  is-not-exception-unit-Maybe x (is-inj-f (p ∙ inv q))

is-not-exception-map-equiv-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-exception-Maybe (map-equiv e (inl x)) →
  is-not-exception-Maybe (map-equiv e exception-Maybe)
is-not-exception-map-equiv-exception-Maybe e =
  is-not-exception-injective-map-exception-Maybe (is-injective-map-equiv e)

-- If f is injective and f (inl x) is an exception, then f exception is a value
is-value-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) → is-exception-Maybe (f (inl x)) →
  is-value-Maybe (f exception-Maybe)
is-value-injective-map-exception-Maybe {f = f} is-inj-f x H =
  is-value-is-not-exception-Maybe
    ( f exception-Maybe)
    ( is-not-exception-injective-map-exception-Maybe is-inj-f x H)

value-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) → is-exception-Maybe (f (inl x)) → Y
value-injective-map-exception-Maybe {f = f} is-inj-f x H =
  value-is-value-Maybe
    ( f exception-Maybe)
    ( is-value-injective-map-exception-Maybe is-inj-f x H)

comp-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) (H : is-exception-Maybe (f (inl x))) →
  Id ( inl (value-injective-map-exception-Maybe is-inj-f x H))
     ( f exception-Maybe)
comp-injective-map-exception-Maybe {f = f} is-inj-f x H =
  eq-is-value-Maybe
    ( f exception-Maybe)
    ( is-value-injective-map-exception-Maybe is-inj-f x H)

is-not-exception-emb-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ↪ Maybe Y)
  (x : X) → is-exception-Maybe (map-emb e (inl x)) →
  is-not-exception-Maybe (map-emb e exception-Maybe)
is-not-exception-emb-exception-Maybe e =
  is-not-exception-injective-map-exception-Maybe (is-injective-emb e)

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

restrict-injective-map-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) (u : Maybe Y) (p : Id (f (inl x)) u) → Y
restrict-injective-map-Maybe' {f = f} is-inj-f x (inl y) p = y
restrict-injective-map-Maybe' {f = f} is-inj-f x (inr star) p =
  value-injective-map-exception-Maybe is-inj-f x p

restrict-injective-map-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → X → Y
restrict-injective-map-Maybe {f = f} is-inj-f x =
  restrict-injective-map-Maybe' is-inj-f x (f (inl x)) refl

comp-restrict-injective-map-is-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) (u : Maybe Y) (p : Id (f (inl x)) u) →
  is-exception-Maybe (f (inl x)) →
  Id (inl (restrict-injective-map-Maybe' is-inj-f x u p)) (f exception-Maybe)
comp-restrict-injective-map-is-exception-Maybe' {f = f} is-inj-f x (inl y) p q =
  ex-falso (is-not-exception-unit-Maybe y (inv p ∙ q))
comp-restrict-injective-map-is-exception-Maybe' {f = f} is-inj-f x (inr star) p q =
  comp-injective-map-exception-Maybe is-inj-f x p

comp-restrict-injective-map-is-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) → is-exception-Maybe (f (inl x)) →
  Id (inl (restrict-injective-map-Maybe is-inj-f x)) (f exception-Maybe)
comp-restrict-injective-map-is-exception-Maybe {f = f} is-inj-f x =
  comp-restrict-injective-map-is-exception-Maybe' is-inj-f x (f (inl x)) refl

comp-restrict-injective-map-is-not-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) (u : Maybe Y) (p : Id (f (inl x)) u) →
  is-not-exception-Maybe (f (inl x)) →
  Id (inl (restrict-injective-map-Maybe' is-inj-f x u p)) (f (inl x))
comp-restrict-injective-map-is-not-exception-Maybe' is-inj-f x (inl y) p H =
  inv p
comp-restrict-injective-map-is-not-exception-Maybe' is-inj-f x (inr star) p H =
  ex-falso (H p)

comp-restrict-injective-map-is-not-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) → is-not-exception-Maybe (f (inl x)) →
  Id (inl (restrict-injective-map-Maybe is-inj-f x)) (f (inl x))
comp-restrict-injective-map-is-not-exception-Maybe {f = f} is-inj-f x =
  comp-restrict-injective-map-is-not-exception-Maybe' is-inj-f x (f (inl x))
    refl

-- An equivalence e : Maybe X ≃ Maybe Y induces a map X → Y. We don't use
-- with-abstraction to keep full control over the definitional equalities, so
-- we give the definition in two steps. After the definition is complete, we
-- also prove two computation rules. Since we will prove computation rules, we
-- make the definition abstract.

map-equiv-equiv-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y)
  (x : X) (u : Maybe Y) (p : Id (map-equiv e (inl x)) u) → Y
map-equiv-equiv-Maybe' e =
  restrict-injective-map-Maybe' (is-injective-map-equiv e)

map-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) → X → Y
map-equiv-equiv-Maybe e =
  restrict-injective-map-Maybe (is-injective-map-equiv e)

comp-map-equiv-equiv-is-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  (u : Maybe Y) (p : Id (map-equiv e (inl x)) u) →
  is-exception-Maybe (map-equiv e (inl x)) →
  Id (inl (map-equiv-equiv-Maybe' e x u p)) (map-equiv e exception-Maybe)
comp-map-equiv-equiv-is-exception-Maybe' e =
  comp-restrict-injective-map-is-exception-Maybe' (is-injective-map-equiv e)

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

double-counting-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (count-A : count A)
  (count-B : count B) (e : A ≃ B) →
  Id (number-of-elements-count count-A) (number-of-elements-count count-B)
double-counting-equiv (pair k f) (pair l g) e =
  is-injective-Fin ((inv-equiv g ∘e e) ∘e f)

double-counting :
  {l : Level} {A : UU l} (count-A count-A' : count A) →
  Id (number-of-elements-count count-A) (number-of-elements-count count-A')
double-counting count-A count-A' =
  double-counting-equiv count-A count-A' equiv-id

{- Maybe X has a count if and only if X has a count -}

count-Maybe : {l : Level} {X : UU l} → count X → count (Maybe X)
count-Maybe {l} {X} e = count-coprod e count-unit

is-nonzero-number-of-elements-count-Maybe :
  {l : Level} {X : UU l} (e : count (Maybe X)) →
  is-nonzero-ℕ (number-of-elements-count e)
is-nonzero-number-of-elements-count-Maybe e p =
  is-empty-is-zero-number-of-elements-count e p exception-Maybe

is-successor-number-of-elements-count-Maybe :
  {l : Level} {X : UU l} (e : count (Maybe X)) →
  is-successor-ℕ (number-of-elements-count e)
is-successor-number-of-elements-count-Maybe e =
  is-successor-is-nonzero-ℕ (is-nonzero-number-of-elements-count-Maybe e)

count-count-Maybe :
  {l : Level} {X : UU l} → count (Maybe X) → count X
count-count-Maybe (pair k e) with
  is-successor-number-of-elements-count-Maybe (pair k e)
... | pair l refl = pair l (equiv-equiv-Maybe e)

--------------------------------------------------------------------------------

-- Double counting in several specific situations

double-counting-coprod :
  { l1 l2 : Level} {A : UU l1} {B : UU l2}
  ( count-A : count A) (count-B : count B) (count-C : count (coprod A B)) →
  Id ( number-of-elements-count count-C)
     ( add-ℕ
       ( number-of-elements-count count-A)
       ( number-of-elements-count count-B))
double-counting-coprod count-A count-B count-C =
  ( double-counting count-C (count-coprod count-A count-B)) ∙
  ( number-of-elements-count-coprod count-A count-B)

double-counting-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
  (count-B : (x : A) → count (B x)) (count-C : count (Σ A B)) →
  Id ( number-of-elements-count count-C)
     ( sum-count-ℕ count-A (λ x → number-of-elements-count (count-B x)))
double-counting-Σ count-A count-B count-C =
  ( double-counting count-C (count-Σ count-A count-B)) ∙
  ( number-of-elements-count-Σ count-A count-B)

sum-number-of-elements-count-fiber-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (e : count A)
  (f : count (Σ A B)) →
  Id ( sum-count-ℕ e
       ( λ x → number-of-elements-count (count-fiber-count-Σ e f x)))
     ( number-of-elements-count f)
sum-number-of-elements-count-fiber-count-Σ e f =
  ( inv (number-of-elements-count-Σ e (λ x → count-fiber-count-Σ e f x))) ∙
  ( double-counting (count-Σ e (λ x → count-fiber-count-Σ e f x)) f)

double-counting-fiber-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
  (count-B : (x : A) → count (B x)) (count-C : count (Σ A B)) (x : A) →
  Id ( number-of-elements-count (count-B x))
     ( number-of-elements-count (count-fiber-count-Σ count-A count-C x))
double-counting-fiber-count-Σ count-A count-B count-C x =
  double-counting (count-B x) (count-fiber-count-Σ count-A count-C x)

sum-number-of-elements-count-fib :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (count-A : count A) (count-B : count B) →
  Id ( sum-count-ℕ count-B
       ( λ x → number-of-elements-count (count-fib f count-A count-B x)))
     ( number-of-elements-count count-A)
sum-number-of-elements-count-fib f count-A count-B =
  sum-number-of-elements-count-fiber-count-Σ count-B
    ( count-equiv' (equiv-total-fib f) count-A)

double-counting-fib :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (count-A : count A) →
  (count-B : count B) (count-fib-f : (y : B) → count (fib f y)) (y : B) →
  Id ( number-of-elements-count (count-fib-f y))
     ( number-of-elements-count (count-fib f count-A count-B y))
double-counting-fib f count-A count-B count-fib-f y =
  double-counting (count-fib-f y) (count-fib f count-A count-B y)

sum-number-of-elements-count-base-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  (count-ΣAB : count (Σ A B)) (count-B : (x : A) → count (B x)) →
  Id ( sum-count-ℕ
       ( count-base-count-Σ b count-ΣAB count-B)
       ( λ x → number-of-elements-count (count-B x)))
     ( number-of-elements-count count-ΣAB)
sum-number-of-elements-count-base-count-Σ b count-ΣAB count-B =
  ( inv
    ( number-of-elements-count-Σ
      ( count-base-count-Σ b count-ΣAB count-B)
      ( count-B))) ∙
  ( double-counting
    ( count-Σ (count-base-count-Σ b count-ΣAB count-B) count-B)
    ( count-ΣAB))

double-counting-base-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  (count-A : count A) (count-B : (x : A) → count (B x))
  (count-ΣAB : count (Σ A B)) →
  Id ( number-of-elements-count (count-base-count-Σ b count-ΣAB count-B))
     ( number-of-elements-count count-A)
double-counting-base-count-Σ b count-A count-B count-ΣAB =
  double-counting (count-base-count-Σ b count-ΣAB count-B) count-A

sum-number-of-elements-count-base-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-ΣAB : count (Σ A B)) →
  ( count-B : (x : A) → count (B x)) →
  ( count-nB :
    count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (count-B x))))) →
  Id ( sum-count-ℕ
       ( count-base-count-Σ' count-ΣAB count-B count-nB)
       ( λ x → number-of-elements-count (count-B x)))
     ( number-of-elements-count count-ΣAB)
sum-number-of-elements-count-base-count-Σ' count-ΣAB count-B count-nB =
  ( inv
    ( number-of-elements-count-Σ
      ( count-base-count-Σ' count-ΣAB count-B count-nB)
      ( count-B))) ∙
  ( double-counting
    ( count-Σ
      ( count-base-count-Σ' count-ΣAB count-B count-nB)
      ( count-B))
    ( count-ΣAB))

double-counting-base-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
  ( count-B : (x : A) → count (B x)) (count-ΣAB : count (Σ A B)) →
  ( count-nB :
    count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (count-B x))))) →
  Id ( number-of-elements-count
       ( count-base-count-Σ' count-ΣAB count-B count-nB))
     ( number-of-elements-count count-A)
double-counting-base-count-Σ' count-A count-B count-ΣAB count-nB =
  double-counting (count-base-count-Σ' count-ΣAB count-B count-nB) count-A

sum-number-of-elements-coprod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : count (coprod A B)) →
  Id ( add-ℕ ( number-of-elements-count (count-left-coprod e))
             ( number-of-elements-count (count-right-coprod e)))
     ( number-of-elements-count e)
sum-number-of-elements-coprod e =
  ( inv
    ( number-of-elements-count-coprod
      ( count-left-coprod e)
      ( count-right-coprod e))) ∙
  ( inv
    ( double-counting-coprod (count-left-coprod e) (count-right-coprod e) e))

product-number-of-elements-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (count-AB : count (A × B)) →
  (a : A) (b : B) →
  Id ( mul-ℕ ( number-of-elements-count (count-left-factor count-AB b))
             ( number-of-elements-count (count-right-factor count-AB a)))
     ( number-of-elements-count count-AB)
product-number-of-elements-prod count-AB a b =
  ( inv
    ( number-of-elements-count-prod
      ( count-left-factor count-AB b)
      ( count-right-factor count-AB a))) ∙
  ( double-counting
    ( count-prod (count-left-factor count-AB b) (count-right-factor count-AB a))
    ( count-AB))


--------------------------------------------------------------------------------

-- Ordering relation on any type A that comes equipped with a count

leq-count :
  {l : Level} {X : UU l} → count X → X → X → UU lzero
leq-count e x y =
  leq-Fin (map-inv-equiv-count e x) (map-inv-equiv-count e y)

refl-leq-count :
  {l : Level} {X : UU l} (e : count X) (x : X) → leq-count e x x
refl-leq-count (pair k e) x = refl-leq-Fin (map-inv-equiv e x)

antisymmetric-leq-count :
  {l : Level} {X : UU l} (e : count X) {x y : X} →
  leq-count e x y → leq-count e y x → Id x y
antisymmetric-leq-count (pair k e) H K =
  is-injective-map-inv-equiv e (antisymmetric-leq-Fin H K)

transitive-leq-count :
  {l : Level} {X : UU l} (e : count X) {x y z : X} →
  leq-count e x y → leq-count e y z → leq-count e x z
transitive-leq-count (pair k e) {x} {y} {z} H K =
  transitive-leq-Fin {x = map-inv-equiv e x} {map-inv-equiv e y} H K

preserves-leq-equiv-count :
  {l : Level} {X : UU l} (e : count X)
  {x y : Fin (number-of-elements-count e)} →
  leq-Fin x y → leq-count e (map-equiv-count e x) (map-equiv-count e y)
preserves-leq-equiv-count e {x} {y} H =
  concatenate-eq-leq-eq-Fin
    ( isretr-map-inv-equiv (equiv-count e) x)
    ( H)
    ( inv (isretr-map-inv-equiv (equiv-count e) y))

reflects-leq-equiv-count :
  {l : Level} {X : UU l} (e : count X)
  {x y : Fin (number-of-elements-count e)} →
  leq-count e (map-equiv-count e x) (map-equiv-count e y) → leq-Fin x y
reflects-leq-equiv-count e {x} {y} H =
  concatenate-eq-leq-eq-Fin
    ( inv (isretr-map-inv-equiv (equiv-count e) x))
    ( H)
    ( isretr-map-inv-equiv (equiv-count e) y)

transpose-leq-equiv-count :
  {l : Level} {X : UU l} (e : count X) →
  {x : Fin (number-of-elements-count e)} {y : X} →
  leq-Fin x (map-inv-equiv-count e y) → leq-count e (map-equiv-count e x) y
transpose-leq-equiv-count e {x} {y} H =
  concatenate-eq-leq-eq-Fin
    ( isretr-map-inv-equiv (equiv-count e) x)
    ( H)
    ( refl)

transpose-leq-equiv-count' :
  {l : Level} {X : UU l} (e : count X) →
  {x : X} {y : Fin (number-of-elements-count e)} →
  leq-Fin (map-inv-equiv-count e x) y → leq-count e x (map-equiv-count e y)
transpose-leq-equiv-count' e {x} {y} H =
  concatenate-eq-leq-eq-Fin
    ( refl)
    ( H)
    ( inv (isretr-map-inv-equiv (equiv-count e) y))

is-lower-bound-count :
  {l1 l2 : Level} {A : UU l1} → count A → (A → UU l2) → A → UU (l1 ⊔ l2)
is-lower-bound-count {l1} {l2} {A} e B a = (x : A) → B x → leq-count e a x

first-element-count :
  {l1 l2 : Level} {A : UU l1} (e : count A) (B : A → UU l2) → UU (l1 ⊔ l2)
first-element-count {l1} {l2} {A} e B =
  Σ A (λ x → (B x) × is-lower-bound-count e B x)

first-element-is-decidable-subtype-count :
  {l1 l2 : Level} {A : UU l1} (e : count A) {B : A → UU l2} →
  ((x : A) → is-decidable (B x)) → ((x : A) → is-prop (B x)) →
  Σ A B → first-element-count e B
first-element-is-decidable-subtype-count (pair k e) {B} d H (pair a b) =
  map-Σ
    ( λ x → (B x) × is-lower-bound-count (pair k e) B x)
    ( map-equiv e)
    ( λ x → map-prod {B = is-lower-bound-Fin (B ∘ map-equiv e) x} id
      ( λ L y b →
        transpose-leq-equiv-count
          ( pair k e)
          ( L (map-inv-equiv e y) (tr B (inv (issec-map-inv-equiv e y)) b))))
    ( minimal-element-decidable-subtype-Fin
      ( λ x → d (map-equiv e x))
      ( pair (map-inv-equiv e a) (tr B (inv (issec-map-inv-equiv e a)) b)))

--------------------------------------------------------------------------------

-- Section 15.3 Finite types

{- Definition -}

is-finite-Prop :
  {l : Level} → UU l → UU-Prop l
is-finite-Prop X = trunc-Prop (count X)

is-finite :
  {l : Level} → UU l → UU l
is-finite X = type-Prop (is-finite-Prop X)

is-prop-is-finite :
  {l : Level} (X : UU l) → is-prop (is-finite X)
is-prop-is-finite X = is-prop-type-Prop (is-finite-Prop X)

is-finite-count :
  {l : Level} {X : UU l} → count X → is-finite X
is-finite-count = unit-trunc-Prop

𝔽 : UU (lsuc lzero)
𝔽 = Σ (UU lzero) is-finite

type-𝔽 : 𝔽 → UU lzero
type-𝔽 X = pr1 X

is-finite-type-𝔽 : (X : 𝔽) → is-finite (type-𝔽 X)
is-finite-type-𝔽 X = pr2 X

is-finite-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-finite A → is-finite B
is-finite-equiv e =
  map-universal-property-trunc-Prop
    ( is-finite-Prop _)
    ( is-finite-count ∘ (count-equiv e))

is-finite-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-equiv f → is-finite A → is-finite B
is-finite-is-equiv is-equiv-f =
  map-universal-property-trunc-Prop
    ( is-finite-Prop _)
    ( is-finite-count ∘ (count-equiv (pair _ is-equiv-f)))

is-finite-equiv' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-finite B → is-finite A
is-finite-equiv' e = is-finite-equiv (inv-equiv e)

{- Theorem -}

mere-equiv-Prop :
  {l1 l2 : Level} → UU l1 → UU l2 → UU-Prop (l1 ⊔ l2)
mere-equiv-Prop X Y = trunc-Prop (X ≃ Y)

mere-equiv :
  {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
mere-equiv X Y = type-Prop (mere-equiv-Prop X Y)

is-prop-mere-equiv :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) → is-prop (mere-equiv X Y)
is-prop-mere-equiv X Y = is-prop-type-Prop (mere-equiv-Prop X Y)

has-cardinality-Prop :
  {l : Level} → UU l → ℕ → UU-Prop l
has-cardinality-Prop X k = mere-equiv-Prop (Fin k) X

has-cardinality :
  {l : Level} → UU l → ℕ → UU l
has-cardinality X k = mere-equiv (Fin k) X

UU-Fin' : (l : Level) → ℕ → UU (lsuc l)
UU-Fin' l k = Σ (UU l) (mere-equiv (Fin k))

UU-Fin : ℕ → UU (lsuc lzero)
UU-Fin k = UU-Fin' lzero k

has-finite-cardinality :
  {l : Level} → UU l → UU l
has-finite-cardinality X = Σ ℕ (has-cardinality X)

number-of-elements-has-finite-cardinality :
  {l : Level} {X : UU l} → has-finite-cardinality X → ℕ
number-of-elements-has-finite-cardinality = pr1

mere-equiv-has-finite-cardinality :
  {l : Level} {X : UU l} (c : has-finite-cardinality X) →
  type-trunc-Prop (Fin (number-of-elements-has-finite-cardinality c) ≃ X)
mere-equiv-has-finite-cardinality = pr2

is-prop-has-finite-cardinality' :
  {l1 : Level} {X : UU l1} → is-prop' (has-finite-cardinality X)
is-prop-has-finite-cardinality' {l1} {X} (pair k K) (pair l L) =
  eq-subtype
    ( λ k → is-prop-type-trunc-Prop)
    ( apply-universal-property-trunc-Prop K
      ( pair (Id k l) (is-set-ℕ k l))
      ( λ (e : Fin k ≃ X) →
        apply-universal-property-trunc-Prop L
          ( pair (Id k l) (is-set-ℕ k l))
          ( λ (f : Fin l ≃ X) → is-injective-Fin ((inv-equiv f) ∘e e))))

is-prop-has-finite-cardinality :
  {l1 : Level} {X : UU l1} → is-prop (has-finite-cardinality X)
is-prop-has-finite-cardinality =
  is-prop-is-prop' is-prop-has-finite-cardinality'

has-finite-cardinality-Prop :
  {l1 : Level} (X : UU l1) → UU-Prop l1
has-finite-cardinality-Prop X =
  pair (has-finite-cardinality X) (is-prop-has-finite-cardinality)

is-finite-has-finite-cardinality :
  {l : Level} {X : UU l} → has-finite-cardinality X → is-finite X
is-finite-has-finite-cardinality {l} {X} (pair k K) =
  apply-universal-property-trunc-Prop K
    ( is-finite-Prop X)
    ( is-finite-count ∘ (pair k))

has-finite-cardinality-count :
  {l1  : Level} {X : UU l1} → count X → has-finite-cardinality X
has-finite-cardinality-count e =
  pair (number-of-elements-count e) (unit-trunc-Prop (equiv-count e))

has-finite-cardinality-is-finite :
  {l1 : Level} {X : UU l1} → is-finite X → has-finite-cardinality X
has-finite-cardinality-is-finite =
  map-universal-property-trunc-Prop
    ( has-finite-cardinality-Prop _)
    ( has-finite-cardinality-count)

number-of-elements-is-finite :
  {l1 : Level} {X : UU l1} → is-finite X → ℕ
number-of-elements-is-finite =
  number-of-elements-has-finite-cardinality ∘ has-finite-cardinality-is-finite

mere-equiv-is-finite :
  {l1 : Level} {X : UU l1} (f : is-finite X) →
  mere-equiv (Fin (number-of-elements-is-finite f)) X
mere-equiv-is-finite f =
  mere-equiv-has-finite-cardinality (has-finite-cardinality-is-finite f)

compute-number-of-elements-is-finite :
  {l1 : Level} {X : UU l1} (e : count X) (f : is-finite X) →
  Id (number-of-elements-count e) (number-of-elements-is-finite f)
compute-number-of-elements-is-finite e f =
  ind-trunc-Prop
    ( λ g →
      pair
        ( Id (number-of-elements-count e) (number-of-elements-is-finite g))
        ( is-set-ℕ
          ( number-of-elements-count e)
          ( number-of-elements-is-finite g)))
    ( λ g →
      ( is-injective-Fin ((inv-equiv (equiv-count g)) ∘e (equiv-count e))) ∙
      ( ap pr1
        ( eq-is-prop' is-prop-has-finite-cardinality
          ( has-finite-cardinality-count g)
          ( has-finite-cardinality-is-finite (unit-trunc-Prop g)))))
    ( f)

{- Closure properties of finite sets -}

is-finite-empty : is-finite empty
is-finite-empty = is-finite-count count-empty

has-finite-cardinality-empty : has-finite-cardinality empty
has-finite-cardinality-empty = pair zero-ℕ (unit-trunc-Prop equiv-id)

is-finite-is-empty :
  {l1 : Level} {X : UU l1} → is-empty X → is-finite X
is-finite-is-empty H = is-finite-count (count-is-empty H)

empty-𝔽 : 𝔽
empty-𝔽 = pair empty (is-finite-is-empty id)

has-finite-cardinality-is-empty :
  {l1 : Level} {X : UU l1} → is-empty X → has-finite-cardinality X
has-finite-cardinality-is-empty f =
  pair zero-ℕ (unit-trunc-Prop (equiv-count (count-is-empty f)))

is-empty-is-zero-number-of-elements-is-finite :
  {l1 : Level} {X : UU l1} (f : is-finite X) →
  is-zero-ℕ (number-of-elements-is-finite f) → is-empty X
is-empty-is-zero-number-of-elements-is-finite {l1} {X} f p =
  apply-universal-property-trunc-Prop f
    ( is-empty-Prop X)
    ( λ e →
      is-empty-is-zero-number-of-elements-count e
        ( compute-number-of-elements-is-finite e f ∙ p))

is-finite-unit : is-finite unit
is-finite-unit = is-finite-count count-unit

unit-𝔽 : 𝔽
unit-𝔽 = pair unit is-finite-unit

is-finite-is-contr :
  {l1 : Level} {X : UU l1} → is-contr X → is-finite X
is-finite-is-contr H = is-finite-count (count-is-contr H)

is-finite-Fin : {k : ℕ} → is-finite (Fin k)
is-finite-Fin {k} = is-finite-count (count-Fin k)

Fin-𝔽 : ℕ → 𝔽
Fin-𝔽 k = pair (Fin k) (is-finite-Fin)

{- Finiteness and coproducts -}

is-finite-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  is-finite X → is-finite Y → is-finite (coprod X Y)
is-finite-coprod {X = X} {Y} is-finite-X is-finite-Y =
  apply-universal-property-trunc-Prop is-finite-X
    ( is-finite-Prop (coprod X Y))
    ( λ (e : count X) →
      apply-universal-property-trunc-Prop is-finite-Y
        ( is-finite-Prop (coprod X Y))
        ( is-finite-count ∘ (count-coprod e)))

coprod-𝔽 : 𝔽 → 𝔽 → 𝔽
coprod-𝔽 X Y =
  pair ( coprod (type-𝔽 X) (type-𝔽 Y))
       ( is-finite-coprod (is-finite-type-𝔽 X) (is-finite-type-𝔽 Y))

is-finite-left-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → is-finite (coprod X Y) → is-finite X
is-finite-left-coprod =
  functor-trunc-Prop count-left-coprod

is-finite-right-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → is-finite (coprod X Y) → is-finite Y
is-finite-right-coprod =
  functor-trunc-Prop count-right-coprod

{- Finiteness and products -}

is-finite-prod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  is-finite X → is-finite Y → is-finite (X × Y)
is-finite-prod {X = X} {Y} is-finite-X is-finite-Y =
  apply-universal-property-trunc-Prop is-finite-X
    ( is-finite-Prop (X × Y))
    ( λ (e : count X) →
      apply-universal-property-trunc-Prop is-finite-Y
        ( is-finite-Prop (X × Y))
        ( is-finite-count ∘ (count-prod e)))

prod-𝔽 : 𝔽 → 𝔽 → 𝔽
prod-𝔽 X Y =
  pair ( prod (type-𝔽 X) (type-𝔽 Y))
       ( is-finite-prod (is-finite-type-𝔽 X) (is-finite-type-𝔽 Y))

is-finite-left-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  is-finite (X × Y) → Y → is-finite X
is-finite-left-factor f y =
  functor-trunc-Prop (λ e → count-left-factor e y) f

is-finite-right-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  is-finite (X × Y) → X → is-finite Y
is-finite-right-factor f x =
  functor-trunc-Prop (λ e → count-right-factor e x) f

{- Finite choice -}

finite-choice-Fin :
  {l1 : Level} {k : ℕ} {Y : Fin k → UU l1} →
  ((x : Fin k) → type-trunc-Prop (Y x)) → type-trunc-Prop ((x : Fin k) → Y x)
finite-choice-Fin {l1} {zero-ℕ} {Y} H = unit-trunc-Prop ind-empty
finite-choice-Fin {l1} {succ-ℕ k} {Y} H =
  map-inv-equiv-trunc-Prop
    ( equiv-dependent-universal-property-coprod Y)
    ( map-inv-distributive-trunc-prod-Prop
      ( pair
        ( finite-choice-Fin (λ x → H (inl x)))
        ( map-inv-equiv-trunc-Prop
          ( equiv-ev-star (Y ∘ inr))
          ( H (inr star)))))

finite-choice-count :
  {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} → count X →
  ((x : X) → type-trunc-Prop (Y x)) → type-trunc-Prop ((x : X) → Y x)
finite-choice-count {l1} {l2} {X} {Y} (pair k e) H =
  map-inv-equiv-trunc-Prop
    ( equiv-precomp-Π e Y)
    ( finite-choice-Fin (λ x → H (map-equiv e x)))

finite-choice :
  {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} → is-finite X →
  ((x : X) → type-trunc-Prop (Y x)) → type-trunc-Prop ((x : X) → Y x)
finite-choice {l1} {l2} {X} {Y} is-finite-X H =
  apply-universal-property-trunc-Prop is-finite-X
    ( trunc-Prop ((x : X) → Y x))
    ( λ e → finite-choice-count e H)

{- Finiteness and Σ-types -}

is-finite-Σ :
  {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} →
  is-finite X → ((x : X) → is-finite (Y x)) → is-finite (Σ X Y)
is-finite-Σ {X = X} {Y} is-finite-X is-finite-Y =
  apply-universal-property-trunc-Prop is-finite-X
    ( is-finite-Prop (Σ X Y))
    ( λ (e : count X) →
      apply-universal-property-trunc-Prop
        ( finite-choice is-finite-X is-finite-Y)
        ( is-finite-Prop (Σ X Y))
        ( is-finite-count ∘ (count-Σ e)))

Σ-𝔽 : (X : 𝔽) (Y : type-𝔽 X → 𝔽) → 𝔽
Σ-𝔽 X Y =
  pair ( Σ (type-𝔽 X) (λ x → type-𝔽 (Y x)))
       ( is-finite-Σ
         ( is-finite-type-𝔽 X)
         ( λ x → is-finite-type-𝔽 (Y x)))

is-finite-fiber-is-finite-Σ :
  {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} →
  is-finite X → is-finite (Σ X Y) → (x : X) → is-finite (Y x)
is-finite-fiber-is-finite-Σ {l1} {l2} {X} {Y} f g x =
  apply-universal-property-trunc-Prop f
    ( is-finite-Prop (Y x))
    ( λ e → functor-trunc-Prop (λ h → count-fiber-count-Σ e h x) g)

is-finite-fib :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) →
  is-finite X → is-finite Y → (y : Y) → is-finite (fib f y)
is-finite-fib f is-finite-X is-finite-Y y =
  apply-universal-property-trunc-Prop
    ( is-finite-X)
    ( is-finite-Prop (fib f y))
    ( λ H →
      apply-universal-property-trunc-Prop
        ( is-finite-Y)
        ( is-finite-Prop (fib f y))
        ( λ K → unit-trunc-Prop (count-fib f H K y)))

fib-𝔽 : (X Y : 𝔽) (f : type-𝔽 X → type-𝔽 Y) → type-𝔽 Y → 𝔽
fib-𝔽 X Y f y =
  pair (fib f y) (is-finite-fib f (is-finite-type-𝔽 X) (is-finite-type-𝔽 Y) y)

is-prop-is-inhabited :
  {l1 : Level} {X : UU l1} → (X → is-prop X) → is-prop X
is-prop-is-inhabited f x y = f x x y

is-prop-has-decidable-equality :
  {l1 : Level} {X : UU l1} → is-prop (has-decidable-equality X)
is-prop-has-decidable-equality {l1} {X} =
  is-prop-is-inhabited
    ( λ d →
      is-prop-Π
      ( λ x →
        is-prop-Π
        ( λ y →
          is-prop-coprod
          ( intro-dn)
          ( is-set-has-decidable-equality d x y)
          ( is-prop-neg))))

has-decidable-equality-is-finite :
  {l1 : Level} {X : UU l1} → is-finite X → has-decidable-equality X
has-decidable-equality-is-finite {l1} {X} is-finite-X =
  apply-universal-property-trunc-Prop is-finite-X
    ( pair (has-decidable-equality X) is-prop-has-decidable-equality)
    ( λ e →
      has-decidable-equality-equiv' (equiv-count e) has-decidable-equality-Fin)

is-finite-eq :
  {l1 : Level} {X : UU l1} →
  has-decidable-equality X → {x y : X} → is-finite (Id x y)
is-finite-eq d {x} {y} = is-finite-count (count-eq d x y)

Id-𝔽 : (X : 𝔽) (x y : type-𝔽 X) → 𝔽
Id-𝔽 X x y =
  pair ( Id x y)
       ( is-finite-eq (has-decidable-equality-is-finite (is-finite-type-𝔽 X)))

is-finite-fib-map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  is-finite (Σ A B) → ((x : A) → is-finite (B x)) →
  (t : Σ A B) → is-finite (fib (map-section b) t)
is-finite-fib-map-section {l1} {l2} {A} {B} b f g (pair y z) =
  is-finite-equiv'
    ( ( ( left-unit-law-Σ-is-contr
            ( is-contr-total-path' y)
            ( pair y refl)) ∘e
        ( inv-assoc-Σ A
          ( λ x → Id x y)
          ( λ t → Id (tr B (pr2 t) (b (pr1 t))) z))) ∘e
      ( equiv-tot (λ x → equiv-pair-eq-Σ (pair x (b x)) (pair y z))))
    ( is-finite-eq (has-decidable-equality-is-finite (g y)))

is-empty-type-trunc-Prop :
  {l1 : Level} {X : UU l1} → is-empty X → is-empty (type-trunc-Prop X)
is-empty-type-trunc-Prop f =
  map-universal-property-trunc-Prop empty-Prop f

is-empty-type-trunc-Prop' :
  {l1 : Level} {X : UU l1} → is-empty (type-trunc-Prop X) → is-empty X
is-empty-type-trunc-Prop' f = f ∘ unit-trunc-Prop

elim-trunc-decidable-fam-Fin :
  {l1 : Level} {k : ℕ} {B : Fin k → UU l1} →
  ((x : Fin k) → is-decidable (B x)) →
  type-trunc-Prop (Σ (Fin k) B) → Σ (Fin k) B
elim-trunc-decidable-fam-Fin {l1} {zero-ℕ} {B} d y =
  ex-falso (is-empty-type-trunc-Prop pr1 y)
elim-trunc-decidable-fam-Fin {l1} {succ-ℕ k} {B} d y
  with d (inr star)
... | inl x = pair (inr star) x
... | inr f =
  map-Σ-map-base inl B
    ( elim-trunc-decidable-fam-Fin {l1} {k} {B ∘ inl}
      ( λ x → d (inl x))
      ( map-equiv-trunc-Prop
        ( ( ( right-unit-law-coprod-is-empty
              ( Σ (Fin k) (B ∘ inl))
              ( B (inr star)) f) ∘e
            ( equiv-coprod equiv-id (left-unit-law-Σ (B ∘ inr)))) ∘e
          ( right-distributive-Σ-coprod (Fin k) unit B))
        ( y)))

is-finite-base-is-finite-Σ-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  is-finite (Σ A B) → ((x : A) → is-finite (B x)) → is-finite A
is-finite-base-is-finite-Σ-section {l1} {l2} {A} {B} b f g =
  apply-universal-property-trunc-Prop f
    ( is-finite-Prop A)
    ( λ e →
      is-finite-count
        ( count-equiv
          ( ( equiv-total-fib-map-section b) ∘e
            ( equiv-tot
              ( λ t →
                ( equiv-tot (λ x → equiv-eq-pair-Σ (map-section b x) t)) ∘e
                ( ( assoc-Σ A
                    ( λ (x : A) → Id x (pr1 t))
                    ( λ s → Id (tr B (pr2 s) (b (pr1 s))) (pr2 t))) ∘e
                  ( inv-left-unit-law-Σ-is-contr
                    ( is-contr-total-path' (pr1 t))
                    ( pair (pr1 t) refl))))))
          ( count-Σ e
            ( λ t →
              count-eq
                ( has-decidable-equality-is-finite (g (pr1 t)))
                ( b (pr1 t))
                ( pr2 t)))))

is-finite-base-is-finite-Σ-mere-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  type-trunc-Prop ((x : A) → B x) →
  is-finite (Σ A B) → ((x : A) → is-finite (B x)) → is-finite A
is-finite-base-is-finite-Σ-mere-section {l1} {l2} {A} {B} H f g =
  apply-universal-property-trunc-Prop H
    ( is-finite-Prop A)
    ( λ b → is-finite-base-is-finite-Σ-section b f g)

is-prop-leq-Fin :
  {k : ℕ} (x y : Fin k) → is-prop (leq-Fin x y)
is-prop-leq-Fin {succ-ℕ k} (inl x) (inl y) = is-prop-leq-Fin x y
is-prop-leq-Fin {succ-ℕ k} (inl x) (inr star) = is-prop-unit
is-prop-leq-Fin {succ-ℕ k} (inr star) (inl y) = is-prop-empty
is-prop-leq-Fin {succ-ℕ k} (inr star) (inr star) = is-prop-unit

is-prop-is-lower-bound-Fin :
  {l : Level} {k : ℕ} {P : Fin k → UU l} (x : Fin k) →
  is-prop (is-lower-bound-Fin P x)
is-prop-is-lower-bound-Fin x =
  is-prop-Π (λ y → is-prop-function-type (is-prop-leq-Fin x y))

is-prop-minimal-element-subtype-Fin' :
  {l : Level} {k : ℕ} (P : Fin k → UU l) →
  ((x : Fin k) → is-prop (P x)) → is-prop' (minimal-element-Fin P)
is-prop-minimal-element-subtype-Fin' P H
  (pair x (pair p l)) (pair y (pair q m)) =
  eq-subtype
    ( λ t → is-prop-prod (H t) (is-prop-is-lower-bound-Fin t))
    ( antisymmetric-leq-Fin (l y q) (m x p))

is-prop-minimal-element-subtype-Fin :
  {l : Level} {k : ℕ} (P : Fin k → UU l) →
  ((x : Fin k) → is-prop (P x)) → is-prop (minimal-element-Fin P)
is-prop-minimal-element-subtype-Fin P H =
  is-prop-is-prop' (is-prop-minimal-element-subtype-Fin' P H)

is-prop-leq-count :
  {l : Level} {A : UU l} (e : count A) {x y : A} → is-prop (leq-count e x y)
is-prop-leq-count e {x} {y} =
  is-prop-leq-Fin (map-inv-equiv-count e x) (map-inv-equiv-count e y)

is-prop-is-lower-bound-count :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (e : count A) →
  (x : A) → is-prop (is-lower-bound-count e B x)
is-prop-is-lower-bound-count e x =
  is-prop-Π ( λ x → is-prop-function-type (is-prop-leq-count e))

equiv-is-lower-bound-count :
  {l1 l2 : Level} {A : UU l1} (e : count A) {B : A → UU l2} →
  (x : Fin (number-of-elements-count e)) →
  is-lower-bound-Fin (B ∘ map-equiv-count e) x ≃
  is-lower-bound-count e B (map-equiv-count e x)
equiv-is-lower-bound-count e {B} x =
  equiv-prop
    ( is-prop-is-lower-bound-Fin x)
    ( is-prop-is-lower-bound-count e (map-equiv-count e x))
    ( λ H y l →
      transpose-leq-equiv-count e
        ( H ( map-inv-equiv-count e y)
            ( tr B (inv (issec-map-inv-equiv (equiv-count e) y)) l)))
    ( λ H y l →
      reflects-leq-equiv-count e (H (map-equiv-count e y) l))

is-prop-first-element-subtype-count :
  {l1 l2 : Level} {A : UU l1} (e : count A) {P : A → UU l2} →
  ((x : A) → is-prop (P x)) → is-prop (first-element-count e P)
is-prop-first-element-subtype-count e {P} H =
  is-prop-equiv'
    ( minimal-element-Fin (P ∘ map-equiv-count e))
    ( equiv-Σ
      ( λ x → P x × is-lower-bound-count e P x)
      ( equiv-count e)
      ( λ x → equiv-prod equiv-id (equiv-is-lower-bound-count e x)))
    ( is-prop-minimal-element-subtype-Fin
      ( P ∘ map-equiv-count e)
      ( λ y → H (map-equiv-count e y)))

first-element-subtype-count-Prop :
  {l1 l2 : Level} {A : UU l1} (e : count A) {P : A → UU l2} →
  ((x : A) → is-prop (P x)) → UU-Prop (l1 ⊔ l2)
first-element-subtype-count-Prop e {P} H =
  pair
    ( first-element-count e P)
    ( is-prop-first-element-subtype-count e H)

element-inhabited-decidable-subtype-Fin :
  {l : Level} {k : ℕ} {P : Fin k → UU l} →
  ((x : Fin k) → is-decidable (P x)) → ((x : Fin k) → is-prop (P x)) →
  type-trunc-Prop (Σ (Fin k) P) → Σ (Fin k) P
element-inhabited-decidable-subtype-Fin {l} {k} {P} d H t =
  tot
    ( λ x → pr1)
    ( apply-universal-property-trunc-Prop t
      ( pair
        ( minimal-element-Fin P)
        ( is-prop-minimal-element-subtype-Fin P H))
      ( minimal-element-decidable-subtype-Fin d))

choice-subtype-count :
  {l1 l2 : Level} {A : UU l1} (e : count A) {P : A → UU l2} →
  ((x : A) → is-decidable (P x)) → ((x : A) → is-prop (P x)) →
  type-trunc-Prop (Σ A P) → Σ A P
choice-subtype-count e d H t =
  tot
    ( λ x → pr1)
    ( apply-universal-property-trunc-Prop t
      ( first-element-subtype-count-Prop e H)
      ( first-element-is-decidable-subtype-count e d H))

is-inhabited-or-empty : {l1 : Level} → UU l1 → UU l1
is-inhabited-or-empty A = coprod (type-trunc-Prop A) (is-empty A)

is-prop-is-inhabited-or-empty :
  {l1 : Level} (A : UU l1) → is-prop (is-inhabited-or-empty A)
is-prop-is-inhabited-or-empty A =
  is-prop-coprod
    ( λ t → apply-universal-property-trunc-Prop t empty-Prop)
    ( is-prop-type-trunc-Prop)
    ( is-prop-neg)

is-inhabited-or-empty-Prop : {l1 : Level} → UU l1 → UU-Prop l1
is-inhabited-or-empty-Prop A =
  pair (is-inhabited-or-empty A) (is-prop-is-inhabited-or-empty A)

is-inhabited-or-empty-count :
  {l1 : Level} {A : UU l1} → count A → is-inhabited-or-empty A
is-inhabited-or-empty-count (pair zero-ℕ e) =
  inr (is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl)
is-inhabited-or-empty-count (pair (succ-ℕ k) e) =
  inl (unit-trunc-Prop (map-equiv e zero-Fin))

is-inhabited-or-empty-is-finite :
  {l1 : Level} {A : UU l1} → is-finite A → is-inhabited-or-empty A
is-inhabited-or-empty-is-finite {l1} {A} f =
  apply-universal-property-trunc-Prop f
    ( is-inhabited-or-empty-Prop A)
    ( is-inhabited-or-empty-count)

choice-emb-count :
  {l1 l2 : Level} {A : UU l1} (e : count A) {B : UU l2} (f : B ↪ A) →
  ((x : A) → is-decidable (fib (map-emb f) x)) → type-trunc-Prop B → B
choice-emb-count e f d t =
  map-equiv-total-fib
    ( map-emb f)
    ( choice-subtype-count e d
      ( is-prop-map-emb f)
      ( functor-trunc-Prop
        ( map-inv-equiv-total-fib (map-emb f))
        ( t)))

{- We show that if A is a proposition, then so is is-decidable A. -}

is-prop-is-decidable :
  {l : Level} {A : UU l} → is-prop A → is-prop (is-decidable A)
is-prop-is-decidable is-prop-A =
  is-prop-coprod intro-dn is-prop-A is-prop-neg

is-decidable-Prop :
  {l : Level} → UU-Prop l → UU-Prop l
is-decidable-Prop P =
  pair (is-decidable (type-Prop P)) (is-prop-is-decidable (is-prop-type-Prop P))

count-total-subtype-is-finite-total-subtype :
  {l1 l2 : Level} {A : UU l1} (e : count A) (P : A → UU-Prop l2) →
  is-finite (Σ A (λ x → type-Prop (P x))) → count (Σ A (λ x → type-Prop (P x)))
count-total-subtype-is-finite-total-subtype {l1} {l2} {A} e P f =
  count-decidable-subtype P d e
  where
  d : (x : A) → is-decidable (type-Prop (P x))
  d x =
    apply-universal-property-trunc-Prop f
      ( is-decidable-Prop (P x))
      ( λ g → is-decidable-count-Σ e g x)

count-domain-emb-is-finite-domain-emb :
  {l1 l2 : Level} {A : UU l1} (e : count A) {B : UU l2} (f : B ↪ A) →
  is-finite B → count B
count-domain-emb-is-finite-domain-emb e f H =
  count-equiv
    ( equiv-total-fib (map-emb f))
    ( count-total-subtype-is-finite-total-subtype e
      ( λ x → pair (fib (map-emb f) x) (is-prop-map-emb f x))
      ( is-finite-equiv'
        ( equiv-total-fib (map-emb f))
        ( H)))

fiber-inclusion :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (x : A) → B x → Σ A B
fiber-inclusion B x = pair x

map-transpose-total-span :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : A → B → UU l3} →
  Σ A (Σ B ∘ C) → Σ B (λ y → Σ A (λ x → C x y))
map-transpose-total-span (pair x (pair y z)) = pair y (pair x z)

map-inv-transpose-total-span :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : A → B → UU l3} →
  Σ B (λ y → Σ A (λ x → C x y)) → Σ A (Σ B ∘ C)
map-inv-transpose-total-span (pair y (pair x z)) = pair x (pair y z)

issec-map-inv-transpose-total-span :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : A → B → UU l3} →
  ( ( map-transpose-total-span {A = A} {B} {C}) ∘
    ( map-inv-transpose-total-span {A = A} {B} {C})) ~ id
issec-map-inv-transpose-total-span (pair y (pair x z)) = refl

isretr-map-inv-transpose-total-span :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : A → B → UU l3} →
  ( ( map-inv-transpose-total-span {A = A} {B} {C}) ∘
    ( map-transpose-total-span {A = A} {B} {C})) ~ id
isretr-map-inv-transpose-total-span (pair x (pair y z)) = refl

is-equiv-map-transpose-total-span :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : A → B → UU l3} →
  is-equiv (map-transpose-total-span {A = A} {B} {C})
is-equiv-map-transpose-total-span =
  is-equiv-has-inverse
    map-inv-transpose-total-span
    issec-map-inv-transpose-total-span
    isretr-map-inv-transpose-total-span

transpose-total-span :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : A → B → UU l3} →
  Σ A (Σ B ∘ C) ≃ Σ B (λ y → Σ A (λ x → C x y))
transpose-total-span =
  pair map-transpose-total-span is-equiv-map-transpose-total-span

is-emb-fiber-inclusion :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
  is-set A → (x : A) → is-emb (fiber-inclusion B x)
is-emb-fiber-inclusion B H x =
  is-emb-is-prop-map
    ( λ z →
      is-prop-equiv
        ( Id x (pr1 z))
        ( ( ( right-unit-law-Σ-is-contr
                ( λ p →
                  is-contr-map-is-equiv (is-equiv-tr B p) (pr2 z))) ∘e
            ( transpose-total-span)) ∘e
          ( equiv-tot (λ y → equiv-pair-eq-Σ (pair x y) z)))
        ( H x (pr1 z)))

emb-fiber-inclusion :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → is-set A → (x : A) → B x ↪ Σ A B
emb-fiber-inclusion B H x =
  pair (fiber-inclusion B x) (is-emb-fiber-inclusion B H x)

choice : {l : Level} → UU l → UU l
choice X = type-trunc-Prop X → X

choice-count :
  {l : Level} {A : UU l} → count A → choice A
choice-count (pair zero-ℕ e) t =
  ex-falso
    ( apply-universal-property-trunc-Prop t empty-Prop
      ( is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl))
choice-count (pair (succ-ℕ k) e) t = map-equiv e zero-Fin

choice-count-Σ-is-finite-fiber :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-set A → count (Σ A B) → ((x : A) → is-finite (B x)) →
  ((x : A) → type-trunc-Prop (B x)) → (x : A) → B x
choice-count-Σ-is-finite-fiber {l1} {l2} {A} {B} K e g H x =
   choice-count
     ( count-domain-emb-is-finite-domain-emb e
       ( emb-fiber-inclusion B K x)
       ( g x))
     ( H x)

choice-is-finite-Σ-is-finite-fiber :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-set A → is-finite (Σ A B) → ((x : A) → is-finite (B x)) →
  ((x : A) → type-trunc-Prop (B x)) → type-trunc-Prop ((x : A) → B x)
choice-is-finite-Σ-is-finite-fiber {l1} {l2} {A} {B} K f g H =
  apply-universal-property-trunc-Prop f
    ( trunc-Prop ((x : A) → B x))
    ( λ e → unit-trunc-Prop (choice-count-Σ-is-finite-fiber K e g H))

is-finite-base-is-finite-Σ-merely-inhabited :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-set A → (b : (x : A) → type-trunc-Prop (B x)) →
  is-finite (Σ A B) → ((x : A) → is-finite (B x)) → is-finite A
is-finite-base-is-finite-Σ-merely-inhabited {l1} {l2} {A} {B} K b f g =
  is-finite-base-is-finite-Σ-mere-section
    ( choice-is-finite-Σ-is-finite-fiber K f g b)
    ( f)
    ( g)

count-type-trunc-Prop :
  {l1 : Level} {A : UU l1} → count A → count (type-trunc-Prop A)
count-type-trunc-Prop (pair zero-ℕ e) =
  count-is-empty
    ( is-empty-type-trunc-Prop
      ( is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl))
count-type-trunc-Prop (pair (succ-ℕ k) e) =
  count-is-contr
    ( is-proof-irrelevant-is-prop
      ( is-prop-type-trunc-Prop)
      ( unit-trunc-Prop (map-equiv e zero-Fin)))

is-finite-type-trunc-Prop :
  {l1 : Level} {A : UU l1} → is-finite A → is-finite (type-trunc-Prop A)
is-finite-type-trunc-Prop = functor-trunc-Prop count-type-trunc-Prop

trunc-Prop-𝔽 : 𝔽 → 𝔽
trunc-Prop-𝔽 A =
  pair ( type-trunc-Prop (type-𝔽 A))
       ( is-finite-type-trunc-Prop (is-finite-type-𝔽 A)) 

complement :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → UU (l1 ⊔ l2)
complement {l1} {l2} {A} B = Σ A (is-empty ∘ B)

is-finite-base-is-finite-complement :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-set A →
  is-finite (Σ A B) → (g : (x : A) → is-finite (B x)) →
  is-finite (complement B) → is-finite A
is-finite-base-is-finite-complement {l1} {l2} {A} {B} K f g h =
  is-finite-equiv
    ( ( right-unit-law-Σ-is-contr
        ( λ x →
          is-proof-irrelevant-is-prop
            ( is-prop-is-inhabited-or-empty (B x))
            ( is-inhabited-or-empty-is-finite (g x)))) ∘e
      ( inv-equiv
        ( left-distributive-Σ-coprod A
          ( λ x → type-trunc-Prop (B x))
          ( λ x → is-empty (B x)))))
    ( is-finite-coprod
      ( is-finite-base-is-finite-Σ-merely-inhabited
        ( is-set-subtype (λ x → is-prop-type-trunc-Prop) K)
        ( λ t → pr2 t)
        ( is-finite-equiv
          ( equiv-double-structure B (λ x → type-trunc-Prop (B x)))
          ( is-finite-Σ
            ( f)
            ( λ x → is-finite-type-trunc-Prop (g (pr1 x)))))
        ( λ x → g (pr1 x)))
      ( h))  

--------------------------------------------------------------------------------

count-Π-Fin :
  {l1 : Level} {k : ℕ} {B : Fin k → UU l1} →
  ((x : Fin k) → count (B x)) → count ((x : Fin k) → B x)
count-Π-Fin {l1} {zero-ℕ} {B} e =
  count-is-contr (dependent-universal-property-empty' B)
count-Π-Fin {l1} {succ-ℕ k} {B} e =
  count-equiv'
    ( equiv-dependent-universal-property-coprod B)
    ( count-prod
      ( count-Π-Fin (λ x → e (inl x)))
      ( count-equiv'
        ( equiv-ev-star (B ∘ inr))
        ( e (inr star))))

count-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → ((x : A) → count (B x)) → count ((x : A) → B x)
count-Π {l1} {l2} {A} {B} e f =
  count-equiv'
    ( equiv-precomp-Π (equiv-count e) B)
    ( count-Π-Fin (λ x → f (map-equiv-count e x)))

is-finite-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-finite A → ((x : A) → is-finite (B x)) → is-finite ((x : A) → B x)
is-finite-Π {l1} {l2} {A} {B} f g =
  apply-universal-property-trunc-Prop f
    ( is-finite-Prop ((x : A) → B x))
    ( λ e →
      apply-universal-property-trunc-Prop
        ( finite-choice f g)
        ( is-finite-Prop ((x : A) → B x))
        ( λ h → unit-trunc-Prop (count-Π e h)))

Π-𝔽 : (A : 𝔽) (B : type-𝔽 A → 𝔽) → 𝔽
Π-𝔽 A B =
  pair ( (x : type-𝔽 A) → type-𝔽 (B x))
       ( is-finite-Π (is-finite-type-𝔽 A) (λ x → is-finite-type-𝔽 (B x)))

is-finite-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-finite A → is-finite B → is-finite (A → B)
is-finite-function-type f g = is-finite-Π f (λ x → g)

_→-𝔽_ : 𝔽 → 𝔽 → 𝔽
A →-𝔽 B =
  pair ( type-𝔽 A → type-𝔽 B)
       ( is-finite-function-type (is-finite-type-𝔽 A) (is-finite-type-𝔽 B))

is-finite-≃ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-finite A → is-finite B → is-finite (A ≃ B)
is-finite-≃ f g =
  is-finite-Σ
    ( is-finite-function-type f g)
    ( λ h →
      is-finite-prod
        ( is-finite-Σ
          ( is-finite-function-type g f)
          ( λ k →
            is-finite-Π g
              ( λ y → is-finite-eq (has-decidable-equality-is-finite g))))
        ( is-finite-Σ
          ( is-finite-function-type g f)
          ( λ k →
            is-finite-Π f
              ( λ x → is-finite-eq (has-decidable-equality-is-finite f)))))

_≃-𝔽_ : 𝔽 → 𝔽 → 𝔽
A ≃-𝔽 B =
  pair ( type-𝔽 A ≃ type-𝔽 B)
       ( is-finite-≃ (is-finite-type-𝔽 A) (is-finite-type-𝔽 B))

Aut-𝔽 : 𝔽 → 𝔽
Aut-𝔽 A = A ≃-𝔽 A

is-injective-is-injective-comp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → C)
  (g : B → C) (h : A → B) (H : f ~ (g ∘ h)) →
  is-injective f → is-injective h
is-injective-is-injective-comp f g h H is-inj-f {x} {x'} p =
  is-inj-f {x} {x'} ((H x) ∙ ((ap g p) ∙ (inv (H x'))))

is-injective-comp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → C)
  (g : B → C) (h : A → B) (H : f ~ (g ∘ h)) →
  is-injective h → is-injective g → is-injective f
is-injective-comp f g h H is-inj-h is-inj-g {x} {x'} p =
  is-inj-h (is-inj-g ((inv (H x)) ∙ (p ∙ (H x'))))

{-
restrict-injective-map-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : Maybe X → Maybe Y) →
  is-injective f → (x : X) (u : Maybe Y) (p : Id (f (inl x)) u) → Y
restrict-injective-map-Maybe' f is-inj-f x (inl x₁) p = {!!}
restrict-injective-map-Maybe' f is-inj-f x (inr x₁) p = {!!}
-}

--------------------------------------------------------------------------------

-- A combinatorial proof that finite sums are associative

associative-sum-count-ℕ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
  (count-B : (x : A) → count (B x)) (f : (x : A) → B x → ℕ) →
  Id ( sum-count-ℕ count-A (λ x → sum-count-ℕ (count-B x) (f x)))
     ( sum-count-ℕ (count-Σ count-A count-B) (ind-Σ f))
associative-sum-count-ℕ {l1} {l2} {A} {B} count-A count-B f =
   ( ( ap-sum-count-ℕ count-A
       ( λ x →
         inv
         ( number-of-elements-count-Σ (count-B x) (λ y → count-Fin (f x y))))) ∙
     ( inv
       ( number-of-elements-count-Σ count-A
         ( λ x → count-Σ (count-B x) (λ y → count-Fin (f x y)))))) ∙
   ( ( double-counting-equiv
       ( count-Σ count-A (λ x → count-Σ (count-B x) (λ y → count-Fin (f x y))))
       ( count-Σ (count-Σ count-A count-B) (λ x → count-Fin (ind-Σ f x)))
       ( inv-assoc-Σ A B (λ x → Fin (ind-Σ f x)))) ∙
     ( number-of-elements-count-Σ
       ( count-Σ count-A count-B)
       ( λ x → (count-Fin (ind-Σ f x)))))

--------------------------------------------------------------------------------

-- Unital magmas

Magma-UU : (l : Level) → UU (lsuc l)
Magma-UU l = Σ (UU l) (λ A → A → A → A)

type-Magma : {l : Level} → Magma-UU l → UU l
type-Magma M = pr1 M

μ-Magma :
  {l : Level} (M : Magma-UU l) → type-Magma M → type-Magma M → type-Magma M
μ-Magma M = pr2 M

fold-Fin-μ-Magma :
  {l : Level} (M : Magma-UU l) → type-Magma M →
  {k : ℕ} → (Fin k → type-Magma M) → type-Magma M
fold-Fin-μ-Magma M m {zero-ℕ} f = m
fold-Fin-μ-Magma M m {succ-ℕ k} f =
  μ-Magma M (fold-Fin-μ-Magma M m (f ∘ inl)) (f (inr star))

fold-count-μ-Magma' :
  {l1 l2 : Level} (M : Magma-UU l1) → type-Magma M →
  {A : UU l2} {k : ℕ} → (Fin k ≃ A) → (A → type-Magma M) → type-Magma M
fold-count-μ-Magma' M m e f = fold-Fin-μ-Magma M m (f ∘ map-equiv e)

fold-count-μ-Magma :
  {l1 l2 : Level} (M : Magma-UU l1) → type-Magma M →
  {A : UU l2} → count A → (A → type-Magma M) → type-Magma M
fold-count-μ-Magma M m e f = fold-Fin-μ-Magma M m (f ∘ map-equiv-count e)

is-unital-Magma : {l : Level} (M : Magma-UU l) → UU l
is-unital-Magma M =
  Σ ( type-Magma M)
    ( λ e →
      ( (x : type-Magma M) → Id (μ-Magma M e x) x) ×
      ( (x : type-Magma M) → Id (μ-Magma M x e) x))

Unital-Magma-UU : (l : Level) → UU (lsuc l)
Unital-Magma-UU l = Σ (Magma-UU l) is-unital-Magma

magma-Unital-Magma :
  {l : Level} → Unital-Magma-UU l → Magma-UU l
magma-Unital-Magma M = pr1 M
  
is-unital-magma-Unital-Magma :
  {l : Level} (M : Unital-Magma-UU l) → is-unital-Magma (magma-Unital-Magma M)
is-unital-magma-Unital-Magma M = pr2 M

is-semigroup-Magma : {l : Level} → Magma-UU l → UU l
is-semigroup-Magma M =
  (x y z : type-Magma M) →
  Id (μ-Magma M (μ-Magma M x y) z) (μ-Magma M x (μ-Magma M y z))

is-commutative-Magma : {l : Level} → Magma-UU l → UU l
is-commutative-Magma M =
  (x y : type-Magma M) → Id (μ-Magma M x y) (μ-Magma M y x)

is-commutative-monoid-Magma : {l : Level} → Magma-UU l → UU l
is-commutative-monoid-Magma M =
  ((is-semigroup-Magma M) × (is-unital-Magma M)) × (is-commutative-Magma M)

unit-is-commutative-monoid-Magma :
  {l : Level} (M : Magma-UU l) → is-commutative-monoid-Magma M → type-Magma M
unit-is-commutative-monoid-Magma M H = pr1 (pr2 (pr1 H))

swap-with-Fin : {k : ℕ} (x y : Fin k) → Fin k → Fin k
swap-with-Fin {k} x y z
  with has-decidable-equality-Fin x z | has-decidable-equality-Fin y z
... | inl p | d = y
... | inr f | inl q = x
... | inr f | inr g = z


{-
permutation-fold-Fin-μ-is-commutative-monoid-Magma :
  {l1 l2 : Level} (M : Magma-UU l1) (H : is-commutative-monoid-Magma M) →
  {k : ℕ} (e : Fin k ≃ Fin k) (f : Fin k → type-Magma M) →
  Id ( fold-Fin-μ-Magma M
       ( unit-is-commutative-monoid-Magma M H)
       ( f ∘ map-equiv e))
     ( fold-Fin-μ-Magma M (unit-is-commutative-monoid-Magma M H) f)
permutation-fold-Fin-μ-is-commutative-monoid-Magma M H {k} e f = {!!}

is-weakly-constant-map-fold-count-μ-is-commutative-monoid-Magma :
  {l1 l2 : Level} (M : Magma-UU l1) (H : is-commutative-monoid-Magma M)
  {A : UU l2} {k : ℕ} →
  is-weakly-constant-map
    ( fold-count-μ-Magma' M (unit-is-commutative-monoid-Magma M H) {A} {k = k})
is-weakly-constant-map-fold-count-μ-is-commutative-monoid-Magma M H {k} e f = {!!}
-}

--------------------------------------------------------------------------------

{- Finiteness of the image of a map -}

{- We characterize when im(f) is finite, given that the domain of f is finite -}

is-prop-Π-is-decidable-Id :
  {l : Level} {A : UU l} (x : A) → is-prop ((y : A) → is-decidable (Id x y))
is-prop-Π-is-decidable-Id {l} {A} x =
  is-prop-is-proof-irrelevant (λ H → is-contr-Π (λ y → is-proof-irrelevant-is-prop (is-prop-coprod intro-dn {!is-set-has-decidable-equality!} {!!}) (H y)))

is-finite-im :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (e : is-finite A) → (d : (x : A) (y : B) → is-decidable (Id (f x) y)) →
  is-finite (im f)
is-finite-im f e d =
  is-finite-base-is-finite-Σ-merely-inhabited
    ( is-set-has-decidable-equality
      {!!})
    {!!}
    {!!}
    {!!}
