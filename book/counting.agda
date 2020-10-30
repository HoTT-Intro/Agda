{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}
module book.counting where

import book.12-truncation-levels
open book.12-truncation-levels public

{- Counting in type theory -}

count : {l : Level} → UU l → UU l
count X = Σ ℕ (λ k → Fin k ≃ X)

number-of-elements : {l : Level} {X : UU l} → count X → ℕ
number-of-elements = pr1

equiv-count :
  {l : Level} {X : UU l} (e : count X) → Fin (number-of-elements e) ≃ X
equiv-count = pr2

map-equiv-count :
  {l : Level} {X : UU l} (e : count X) → Fin (number-of-elements e) → X
map-equiv-count e = map-equiv (equiv-count e)

{- We show that count is closed under equivalences -}

abstract
  equiv-count-equiv :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) (f : count X) →
    Fin (number-of-elements f) ≃ Y
  equiv-count-equiv e f = e ∘e (equiv-count f)

count-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) → count X → count Y
count-equiv e f =
  pair (number-of-elements f) (equiv-count-equiv e f)

count-equiv' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) → count Y → count X
count-equiv' e = count-equiv (inv-equiv e)

{- Types with a count have decidable equality -}

has-decidable-equality-count :
  {l : Level} {X : UU l} → count X → has-decidable-equality X
has-decidable-equality-count (pair k e) =
  has-decidable-equality-equiv' e (has-decidable-equality-Fin k)

{- Fin k has a count -}

count-Fin : (k : ℕ) → count (Fin k)
count-Fin k = pair k equiv-id

{- A type as 0 elements if and only if it is empty -}

is-empty-is-zero-number-of-elements :
  {l : Level} {X : UU l} (e : count X) →
  is-zero-ℕ (number-of-elements e) → is-empty X
is-empty-is-zero-number-of-elements (pair .zero-ℕ e) refl x =
  map-inv-equiv e x

is-zero-number-of-elements-is-empty :
  {l : Level} {X : UU l} (e : count X) →
  is-empty X → is-zero-ℕ (number-of-elements e)
is-zero-number-of-elements-is-empty (pair zero-ℕ e) H = refl
is-zero-number-of-elements-is-empty (pair (succ-ℕ k) e) H =
  ex-falso (H (map-equiv e zero-Fin))

count-is-empty :
  {l : Level} {X : UU l} → is-empty X → count X
count-is-empty H =
  pair zero-ℕ (inv-equiv (pair H (is-equiv-is-empty' H)))

count-empty : count empty
count-empty = count-Fin zero-ℕ

{- A type has 1 element if and only if it is contractible -}

count-is-contr :
  {l : Level} {X : UU l} → is-contr X → count X
count-is-contr H = pair one-ℕ (equiv-is-contr is-contr-Fin-one-ℕ H)

is-contr-is-one-number-of-elements :
  {l : Level} {X : UU l} (e : count X) →
  is-one-ℕ (number-of-elements e) → is-contr X
is-contr-is-one-number-of-elements (pair .(succ-ℕ zero-ℕ) e) refl =
  is-contr-equiv' (Fin one-ℕ) e is-contr-Fin-one-ℕ

is-one-number-of-elements-is-contr :
  {l : Level} {X : UU l} (e : count X) →
  is-contr X → is-one-ℕ (number-of-elements e)
is-one-number-of-elements-is-contr (pair k e) H =
  is-injective-Fin (equiv-is-contr H is-contr-Fin-one-ℕ ∘e e)

count-unit : count unit
count-unit = count-is-contr is-contr-unit

{- We can count the elements of an identity type of a type that has decidable
   equality. -}

count-Eq-has-decidable-equality' :
  {l : Level} {X : UU l} {x y : X} (d : is-decidable (Id x y)) →
  count (Eq-has-decidable-equality' x y d)
count-Eq-has-decidable-equality' {l} {X} {x} {y} (inl p) = count-unit
count-Eq-has-decidable-equality' {l} {X} {x} {y} (inr f) = count-empty

count-Eq-has-decidable-equality :
  {l : Level} {X : UU l} (d : has-decidable-equality X) {x y : X} →
  count (Eq-has-decidable-equality d x y)
count-Eq-has-decidable-equality d {x} {y} =
  count-Eq-has-decidable-equality' (d x y)

count-eq :
  {l : Level} {X : UU l} → has-decidable-equality X → {x y : X} → count (Id x y)
count-eq d {x} {y} =
  count-equiv
    ( equiv-prop
      ( is-prop-Eq-has-decidable-equality d)
      ( is-set-has-decidable-equality d x y)
      ( eq-Eq-has-decidable-equality d)
      ( Eq-has-decidable-equality-eq d))
      ( count-Eq-has-decidable-equality d)

{- Types equipped with a count are closed under coproducts -}

count-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  count X → count Y → count (coprod X Y)
count-coprod (pair k e) (pair l f) =
  pair
    ( add-ℕ k l)
    ( ( equiv-coprod e f) ∘e
      ( inv-equiv (coprod-Fin k l)))

{- Types equipped with a count are closed under Σ-types -}

count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (k : ℕ) (e : Fin k ≃ A) → ((x : A) → count (B x)) → count (Σ A B)
count-Σ' zero-ℕ e f =
  count-is-empty
    ( λ x → is-empty-is-zero-number-of-elements (pair zero-ℕ e) refl (pr1 x))
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
    Fin (number-of-elements (count-Σ' k e f)) ≃ Σ A B
  equiv-count-Σ' k e f = pr2 (count-Σ' k e f)

count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → ((x : A) → count (B x)) → count (Σ A B)
count-Σ (pair k e) f =
  pair (number-of-elements (count-Σ' k e f)) (equiv-count-Σ' k e f)

count-fiber-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → count (Σ A B) → (x : A) → count (B x)
count-fiber-count-Σ {B = B} e f x =
  count-equiv
    ( equiv-fib-pr1 x)
    ( count-Σ f
      ( λ z → count-eq (has-decidable-equality-count e)))

equiv-section-count-base-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  Σ (Σ A B) (fib (map-section b)) ≃ A
equiv-section-count-base-count-Σ b = equiv-total-fib (map-section b)

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
    ( count-eq (has-decidable-equality-count (f y)))

count-base-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  count (Σ A B) → ((x : A) → count (B x)) → count A
count-base-count-Σ b e f =
  count-equiv
    ( equiv-section-count-base-count-Σ b)
    ( count-Σ e (count-fib-map-section b e f))

section-count-base-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count (Σ A B) →
  (f : (x : A) → count (B x)) →
  count (Σ A (λ x → is-zero-ℕ (number-of-elements (f x)))) →
  (x : A) → coprod (B x) (is-zero-ℕ (number-of-elements (f x)))
section-count-base-count-Σ' e f g x with
  is-decidable-is-zero-ℕ (number-of-elements (f x))
... | inl p = inr p
... | inr H =
  inl
    ( map-equiv-count
      ( f x)
      ( tr Fin (inv (pr2 (is-successor-is-nonzero-ℕ H))) zero-Fin))

count-base-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count (Σ A B) →
  (f : (x : A) → count (B x)) →
  count (Σ A (λ x → is-zero-ℕ (number-of-elements (f x)))) → count A
count-base-count-Σ' {l1} {l2} {A} {B} e f g =
  count-base-count-Σ
    ( section-count-base-count-Σ' e f g)
    ( count-equiv'
      ( left-distributive-Σ-coprod A B
        ( λ x → is-zero-ℕ (number-of-elements (f x))))
      ( count-coprod e g))
    ( λ x → count-coprod (f x) (count-eq has-decidable-equality-ℕ))

{- A coproduct X + Y has a count if and only if both X and Y have a count -}

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

count-left-summand :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (coprod X Y) → count X
count-left-summand e = count-equiv equiv-left-summand (count-Σ e count-is-left)

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

count-right-summand :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (coprod X Y) → count Y
count-right-summand e =
  count-equiv equiv-right-summand (count-Σ e count-is-right)

{- Maybe X has a count if and only if X has a count -}

count-Maybe : {l : Level} {X : UU l} → count X → count (Maybe X)
count-Maybe {l} {X} e = count-coprod e count-unit

is-nonzero-number-of-elements-Maybe :
  {l : Level} {X : UU l} (e : count (Maybe X)) →
  is-nonzero-ℕ (number-of-elements e)
is-nonzero-number-of-elements-Maybe e p =
  is-empty-is-zero-number-of-elements e p exception-Maybe

is-successor-number-of-elements-Maybe :
  {l : Level} {X : UU l} (e : count (Maybe X)) →
  is-successor-ℕ (number-of-elements e)
is-successor-number-of-elements-Maybe e =
  is-successor-is-nonzero-ℕ (is-nonzero-number-of-elements-Maybe e)

count-count-Maybe :
  {l : Level} {X : UU l} → count (Maybe X) → count X
count-count-Maybe (pair k e) with
  is-successor-number-of-elements-Maybe (pair k e)
... | pair l refl = pair l (equiv-equiv-Maybe e)

{- X × Y has a count if and only if Y → count X and X → count Y -}

count-prod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count X → count Y → count (X × Y)
count-prod (pair k e) (pair l f) =
  pair
    ( mul-ℕ k l)
    ( ( equiv-prod e f) ∘e
      ( inv-equiv (prod-Fin k l)))

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
            ( pr1 z))))

count-right-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (X × Y) → X → count Y
count-right-factor e x =
  count-left-factor (count-equiv commutative-prod e) x

count-decidable-Prop :
  {l1 : Level} (P : UU-Prop l1) →
  is-decidable (type-Prop P) → count (type-Prop P)
count-decidable-Prop P (inl p) =
  count-is-contr (is-proof-irrelevant-is-prop (is-prop-type-Prop P) p)
count-decidable-Prop P (inr f) = count-is-empty f

count-decidable-subset :
  {l1 l2 : Level} {X : UU l1} (P : X → UU-Prop l2) →
  ((x : X) → is-decidable (type-Prop (P x))) →
  count X → count (Σ X (λ x → type-Prop (P x)))
count-decidable-subset P d e =
  count-Σ e (λ x → count-decidable-Prop (P x) (d x))

is-decidable-count :
  {l : Level} {X : UU l} → count X → is-decidable X
is-decidable-count (pair zero-ℕ e) =
  inr (is-empty-is-zero-number-of-elements (pair zero-ℕ e) refl)
is-decidable-count (pair (succ-ℕ k) e) =
  inl (map-equiv e zero-Fin)

is-decidable-count-Σ :
  {l1 l2 : Level} {X : UU l1} {P : X → UU l2} →
  count X → count (Σ X P) → (x : X) → is-decidable (P x)
is-decidable-count-Σ e f x =
  is-decidable-count (count-fiber-count-Σ e f x)
