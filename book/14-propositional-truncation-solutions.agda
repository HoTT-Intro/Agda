{-# OPTIONS --without-K --exact-split #-}

module book.14-propositional-truncation-solutions where

import book.14-propositional-truncation
open book.14-propositional-truncation public

--------------------------------------------------------------------------------

-- Exercises

-- Exercise 13.1

is-propositional-truncation-retract :
  {l l1 l2 : Level} {A : UU l1} (P : UU-Prop l2) →
  (R : (type-Prop P) retract-of A) →
  is-propositional-truncation l P (retraction-retract-of R)
is-propositional-truncation-retract {A = A} P R Q =
  is-equiv-is-prop
    ( is-prop-function-type (is-prop-type-Prop Q))
    ( is-prop-function-type (is-prop-type-Prop Q))
    ( λ g → g ∘ (section-retract-of R))

-- Exercise 13.2

is-propositional-truncation-prod :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (P : UU-Prop l2) (f : A → type-Prop P)
  {A' : UU l3} (P' : UU-Prop l4) (f' : A' → type-Prop P') →
  ({l : Level} → is-propositional-truncation l P f) →
  ({l : Level} → is-propositional-truncation l P' f') →
  {l : Level} → is-propositional-truncation l (prod-Prop P P') (functor-prod f f')
is-propositional-truncation-prod P f P' f' is-ptr-f is-ptr-f' Q =
  is-equiv-top-is-equiv-bottom-square
    ( ev-pair)
    ( ev-pair)
    ( precomp (functor-prod f f') (type-Prop Q))
    ( λ h a a' → h (f a) (f' a'))
    ( refl-htpy)
    ( is-equiv-ev-pair)
    ( is-equiv-ev-pair)
    ( is-equiv-comp'
      ( λ h a a' → h a (f' a'))
      ( λ h a p' → h (f a) p')
      ( is-ptr-f (pair (type-hom-Prop P' Q) (is-prop-type-hom-Prop P' Q)))
      ( is-equiv-postcomp-Π
        ( λ a g a' → g (f' a'))
        ( λ a → is-ptr-f' Q)))

equiv-prod-trunc-Prop :
  {l1 l2 : Level} (A : UU l1) (A' : UU l2) →
  equiv-Prop (trunc-Prop (A × A')) (prod-Prop (trunc-Prop A) (trunc-Prop A'))
equiv-prod-trunc-Prop A A' =
  pr1
    ( center
      ( is-uniquely-unique-propositional-truncation
        ( trunc-Prop (A × A'))
        ( prod-Prop (trunc-Prop A) (trunc-Prop A'))
        ( unit-trunc-Prop (A × A'))
        ( functor-prod (unit-trunc-Prop A) (unit-trunc-Prop A'))
        ( is-propositional-truncation-trunc-Prop (A × A'))
        ( is-propositional-truncation-prod
          ( trunc-Prop A)
          ( unit-trunc-Prop A)
          ( trunc-Prop A')
          ( unit-trunc-Prop A')
          ( is-propositional-truncation-trunc-Prop A)
          ( is-propositional-truncation-trunc-Prop A'))))

-- Exercise 13.3

-- Exercise 13.9

map-dn-trunc-Prop :
  {l : Level} (A : UU l) → ¬¬ (type-trunc-Prop A) → ¬¬ A
map-dn-trunc-Prop A =
  dn-extend (map-universal-property-trunc-Prop (dn-Prop' A) intro-dn)

inv-map-dn-trunc-Prop :
  {l : Level} (A : UU l) → ¬¬ A → ¬¬ (type-trunc-Prop A)
inv-map-dn-trunc-Prop A =
  dn-extend (λ a → intro-dn (unit-trunc-Prop A a))

equiv-dn-trunc-Prop :
  {l : Level} (A : UU l) → ¬¬ (type-trunc-Prop A) ≃ ¬¬ A
equiv-dn-trunc-Prop A =
  equiv-iff
    ( dn-Prop (trunc-Prop A))
    ( dn-Prop' A)
    ( pair
      ( map-dn-trunc-Prop A)
      ( inv-map-dn-trunc-Prop A))

-- Exercise 13.10

-- The impredicative encoding of the propositional truncation --

impredicative-trunc-Prop :
  {l : Level} → UU l → UU-Prop (lsuc l)
impredicative-trunc-Prop {l} A =
  Π-Prop
    ( UU-Prop l)
    ( λ Q → function-Prop (A → type-Prop Q) Q)

type-impredicative-trunc-Prop :
  {l : Level} → UU l → UU (lsuc l)
type-impredicative-trunc-Prop {l} A =
  type-Prop (impredicative-trunc-Prop A)

map-impredicative-trunc-Prop :
  {l : Level} (A : UU l) →
  type-trunc-Prop A → type-impredicative-trunc-Prop A
map-impredicative-trunc-Prop {l} A =
  map-universal-property-trunc-Prop
    ( impredicative-trunc-Prop A)
    ( λ x Q f → f x)

inv-map-impredicative-trunc-Prop :
  {l : Level} (A : UU l) →
  type-impredicative-trunc-Prop A → type-trunc-Prop A
inv-map-impredicative-trunc-Prop A H =
  H (trunc-Prop A) (unit-trunc-Prop A)

equiv-impredicative-trunc-Prop :
  {l : Level} (A : UU l) →
  type-trunc-Prop A ≃ type-impredicative-trunc-Prop A
equiv-impredicative-trunc-Prop A =
  equiv-iff
    ( trunc-Prop A)
    ( impredicative-trunc-Prop A)
    ( pair
      ( map-impredicative-trunc-Prop A)
      ( inv-map-impredicative-trunc-Prop A))

-- The impredicative encoding of conjunction --

impredicative-conj-Prop :
  {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU-Prop (lsuc (l1 ⊔ l2))
impredicative-conj-Prop {l1} {l2} P1 P2 =
  Π-Prop
    ( UU-Prop (l1 ⊔ l2))
    ( λ Q → function-Prop (type-Prop P1 → (type-Prop P2 → type-Prop Q)) Q)

type-impredicative-conj-Prop :
  {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU (lsuc (l1 ⊔ l2))
type-impredicative-conj-Prop P1 P2 =
  type-Prop (impredicative-conj-Prop P1 P2)

map-impredicative-conj-Prop :
  {l1 l2 : Level} (P1 : UU-Prop l1) (P2 : UU-Prop l2) →
  type-conj-Prop P1 P2 → type-impredicative-conj-Prop P1 P2
map-impredicative-conj-Prop {l1} {l2} P1 P2 (pair p1 p2) Q f =
  f p1 p2

inv-map-impredicative-conj-Prop :
  {l1 l2 : Level} (P1 : UU-Prop l1) (P2 : UU-Prop l2) →
  type-impredicative-conj-Prop P1 P2 → type-conj-Prop P1 P2
inv-map-impredicative-conj-Prop P1 P2 H =
  H (conj-Prop P1 P2) (λ p1 p2 → pair p1 p2)

equiv-impredicative-conj-Prop :
  {l1 l2 : Level} (P1 : UU-Prop l1) (P2 : UU-Prop l2) →
  type-conj-Prop P1 P2 ≃ type-impredicative-conj-Prop P1 P2
equiv-impredicative-conj-Prop P1 P2 =
  equiv-iff
    ( conj-Prop P1 P2)
    ( impredicative-conj-Prop P1 P2)
    ( pair
      ( map-impredicative-conj-Prop P1 P2)
      ( inv-map-impredicative-conj-Prop P1 P2))

-- The impredicative encoding of disjunction --

impredicative-disj-Prop :
  {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU-Prop (lsuc (l1 ⊔ l2))
impredicative-disj-Prop {l1} {l2} P1 P2 =
  Π-Prop
    ( UU-Prop (l1 ⊔ l2))
    ( λ Q →
      function-Prop
        ( type-implication-Prop P1 Q)
        ( function-Prop (type-implication-Prop P2 Q) Q))

type-impredicative-disj-Prop :
  {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU (lsuc (l1 ⊔ l2))
type-impredicative-disj-Prop P1 P2 =
  type-Prop (impredicative-disj-Prop P1 P2)

map-impredicative-disj-Prop :
  {l1 l2 : Level} (P1 : UU-Prop l1) (P2 : UU-Prop l2) →
  type-disj-Prop P1 P2 → type-impredicative-disj-Prop P1 P2
map-impredicative-disj-Prop {l1} {l2} P1 P2 =
  map-universal-property-trunc-Prop
    ( impredicative-disj-Prop P1 P2)
    ( ind-coprod
      ( λ x → type-impredicative-disj-Prop P1 P2)
      ( λ x Q f1 f2 → f1 x)
      ( λ y Q f1 f2 → f2 y))
  
inv-map-impredicative-disj-Prop :
  {l1 l2 : Level} (P1 : UU-Prop l1) (P2 : UU-Prop l2) →
  type-impredicative-disj-Prop P1 P2 → type-disj-Prop P1 P2
inv-map-impredicative-disj-Prop P1 P2 H =
  H (disj-Prop P1 P2) (inl-disj-Prop P1 P2) (inr-disj-Prop P1 P2)

equiv-impredicative-disj-Prop :
  {l1 l2 : Level} (P1 : UU-Prop l1) (P2 : UU-Prop l2) →
  type-disj-Prop P1 P2 ≃ type-impredicative-disj-Prop P1 P2
equiv-impredicative-disj-Prop P1 P2 =
  equiv-iff
    ( disj-Prop P1 P2)
    ( impredicative-disj-Prop P1 P2)
    ( pair
      ( map-impredicative-disj-Prop P1 P2)
      ( inv-map-impredicative-disj-Prop P1 P2))

-- The impredicative encoding of negation --

impredicative-neg-Prop :
  {l : Level} → UU l → UU-Prop (lsuc l)
impredicative-neg-Prop {l} A =
  Π-Prop (UU-Prop l) (λ Q → function-Prop A Q)

type-impredicative-neg-Prop :
  {l : Level} → UU l → UU (lsuc l)
type-impredicative-neg-Prop A =
  type-Prop (impredicative-neg-Prop A)

map-impredicative-neg-Prop :
  {l : Level} (A : UU l) →
  ¬ A → type-impredicative-neg-Prop A
map-impredicative-neg-Prop A f Q a = ex-falso (f a)

inv-map-impredicative-neg-Prop :
  {l : Level} (A : UU l) →
  type-impredicative-neg-Prop A → ¬ A
inv-map-impredicative-neg-Prop A H a = H (neg-Prop' A) a a

equiv-impredicative-neg-Prop :
  {l : Level} (A : UU l) →
  ¬ A ≃ type-impredicative-neg-Prop A
equiv-impredicative-neg-Prop A =
  equiv-iff
    ( neg-Prop' A)
    ( impredicative-neg-Prop A)
    ( pair
      ( map-impredicative-neg-Prop A)
      ( inv-map-impredicative-neg-Prop A))

-- The impredicative encoding of existential quantification --

impredicative-exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) → UU-Prop (lsuc (l1 ⊔ l2))
impredicative-exists-Prop {l1} {l2} {A} P =
  Π-Prop
    ( UU-Prop (l1 ⊔ l2))
    ( λ Q → function-Prop ((x : A) → type-Prop (P x) → type-Prop Q) Q)

type-impredicative-exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) → UU (lsuc (l1 ⊔ l2))
type-impredicative-exists-Prop P =
  type-Prop (impredicative-exists-Prop P)

map-impredicative-exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) →
  exists P → type-impredicative-exists-Prop P
map-impredicative-exists-Prop {l1} {l2} {A} P =
  map-universal-property-trunc-Prop
    ( impredicative-exists-Prop P)
    ( ind-Σ (λ x y Q h → h x y))

inv-map-impredicative-exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) →
  type-impredicative-exists-Prop P → exists P
inv-map-impredicative-exists-Prop {A = A} P H =
  H ( exists-Prop P)
    ( λ x y → unit-trunc-Prop (Σ A (λ x → type-Prop (P x))) (pair x y))

equiv-impredicative-exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) →
  exists P ≃ type-impredicative-exists-Prop P
equiv-impredicative-exists-Prop P =
  equiv-iff
    ( exists-Prop P)
    ( impredicative-exists-Prop P)
    ( pair
      ( map-impredicative-exists-Prop P)
      ( inv-map-impredicative-exists-Prop P))

-- The impredicative encoding of the based identity type of a set --

impredicative-based-id-Prop :
  {l : Level} (A : UU-Set l) (a x : type-Set A) → UU-Prop (lsuc l)
impredicative-based-id-Prop {l} A a x =
  Π-Prop (type-Set A → UU-Prop l) (λ Q → hom-Prop (Q a) (Q x))

type-impredicative-based-id-Prop :
  {l : Level} (A : UU-Set l) (a x : type-Set A) → UU (lsuc l)
type-impredicative-based-id-Prop A a x =
  type-Prop (impredicative-based-id-Prop A a x)

map-impredicative-based-id-Prop :
  {l : Level} (A : UU-Set l) (a x : type-Set A) →
  Id a x → type-impredicative-based-id-Prop A a x
map-impredicative-based-id-Prop A a .a refl Q p = p

inv-map-impredicative-based-id-Prop :
  {l : Level} (A : UU-Set l) (a x : type-Set A) →
  type-impredicative-based-id-Prop A a x → Id a x
inv-map-impredicative-based-id-Prop A a x H =
  H (λ x → pair (Id a x) (is-set-type-Set A a x)) refl

equiv-impredicative-based-id-Prop :
  {l : Level} (A : UU-Set l) (a x : type-Set A) →
  Id a x ≃ type-impredicative-based-id-Prop A a x
equiv-impredicative-based-id-Prop A a x =
  equiv-iff
    ( pair (Id a x) (is-set-type-Set A a x))
    ( impredicative-based-id-Prop A a x)
    ( pair
      ( map-impredicative-based-id-Prop A a x)
      ( inv-map-impredicative-based-id-Prop A a x))

-- The impredicative encoding of Martin-Löf's identity type of a set --

impredicative-id-Prop :
  {l : Level} (A : UU-Set l) (x y : type-Set A) → UU-Prop (lsuc l)
impredicative-id-Prop {l} A x y =
  Π-Prop (type-Set A → type-Set A → UU-Prop l)
    (λ Q → function-Prop ((a : type-Set A) → type-Prop (Q a a)) (Q x y))

type-impredicative-id-Prop :
  {l : Level} (A : UU-Set l) (x y : type-Set A) → UU (lsuc l)
type-impredicative-id-Prop A x y =
  type-Prop (impredicative-id-Prop A x y)

map-impredicative-id-Prop :
  {l : Level} (A : UU-Set l) (x y : type-Set A) →
  Id x y → type-impredicative-id-Prop A x y
map-impredicative-id-Prop A x .x refl Q r = r x

inv-map-impredicative-id-Prop :
  {l : Level} (A : UU-Set l ) (x y : type-Set A) →
  type-impredicative-id-Prop A x y → Id x y
inv-map-impredicative-id-Prop A x y H =
  H (λ a b → pair (Id a b) (is-set-type-Set A a b)) (λ a → refl)

equiv-impredicative-id-Prop :
  {l : Level} (A : UU-Set l) (x y : type-Set A) →
  Id x y ≃ type-impredicative-id-Prop A x y
equiv-impredicative-id-Prop A x y =
  equiv-iff
    ( pair (Id x y) (is-set-type-Set A x y))
    ( impredicative-id-Prop A x y)
    ( pair
      ( map-impredicative-id-Prop A x y)
      ( inv-map-impredicative-id-Prop A x y))
