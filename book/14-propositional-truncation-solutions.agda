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
  {l : Level} → is-propositional-truncation l (prod-Prop P P') (map-prod f f')
is-propositional-truncation-prod P f P' f' is-ptr-f is-ptr-f' Q =
  is-equiv-top-is-equiv-bottom-square
    ( ev-pair)
    ( ev-pair)
    ( precomp (map-prod f f') (type-Prop Q))
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
        ( unit-trunc-Prop)
        ( map-prod unit-trunc-Prop unit-trunc-Prop)
        ( is-propositional-truncation-trunc-Prop (A × A'))
        ( is-propositional-truncation-prod
          ( trunc-Prop A)
          ( unit-trunc-Prop)
          ( trunc-Prop A')
          ( unit-trunc-Prop)
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
  dn-extend (λ a → intro-dn (unit-trunc-Prop a))

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
  H (trunc-Prop A) unit-trunc-Prop

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
    ( λ x y → unit-trunc-Prop (pair x y))

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

--------------------------------------------------------------------------------

is-weakly-constant-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-weakly-constant-map {A = A} f = (x y : A) → Id (f x) (f y)

is-prop-is-weakly-constant-map-Set :
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  is-prop (is-weakly-constant-map f)
is-prop-is-weakly-constant-map-Set B f =
  is-prop-Π (λ x → is-prop-Π (λ y → is-set-type-Set B (f x) (f y)))

is-weakly-constant-map-precomp-unit-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (g : type-trunc-Prop A → B) →
  is-weakly-constant-map (g ∘ unit-trunc-Prop)
is-weakly-constant-map-precomp-unit-trunc-Prop g x y =
  ap ( g)
     ( eq-is-prop
       ( is-prop-type-trunc-Prop)
       ( unit-trunc-Prop x)
       ( unit-trunc-Prop y))

precomp-universal-property-set-quotient-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) →
  (type-trunc-Prop A → type-Set B) → Σ (A → type-Set B) is-weakly-constant-map
precomp-universal-property-set-quotient-trunc-Prop B g =
  pair
    ( g ∘ unit-trunc-Prop)
    ( is-weakly-constant-map-precomp-unit-trunc-Prop g)

is-prop-image-is-weakly-constant-map' :
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  is-weakly-constant-map f →
  is-prop' (Σ (type-Set B) (λ b → type-trunc-Prop (fib f b)))
is-prop-image-is-weakly-constant-map' B f H (pair x s) (pair y t) =
  eq-subtype
    ( λ b → is-prop-type-trunc-Prop)
    ( apply-universal-property-trunc-Prop s
      ( Id-Prop B x y)
      ( λ u →
        apply-universal-property-trunc-Prop t
          ( Id-Prop B x y)
          ( λ v → inv (pr2 u) ∙ (H (pr1 u) (pr1 v) ∙ pr2 v))))

is-prop-image-is-weakly-constant-map :
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  is-weakly-constant-map f →
  is-prop (Σ (type-Set B) (λ b → type-trunc-Prop (fib f b)))
is-prop-image-is-weakly-constant-map B f H =
  is-prop-is-prop' (is-prop-image-is-weakly-constant-map' B f H)

image-weakly-constant-map-Prop :
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  is-weakly-constant-map f → UU-Prop (l1 ⊔ l2)
image-weakly-constant-map-Prop B f H =
  pair
    ( Σ (type-Set B) (λ b → type-trunc-Prop (fib f b)))
    ( is-prop-image-is-weakly-constant-map B f H)

map-extension-weakly-constant-map :
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  is-weakly-constant-map f → type-trunc-Prop A → type-Set B
map-extension-weakly-constant-map B f H =
  ( pr1) ∘
  ( map-universal-property-trunc-Prop
    ( image-weakly-constant-map-Prop B f H)
    ( λ a → pair (f a) (unit-trunc-Prop (pair a refl))))

htpy-extension-weakly-constant-map :
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  (H : is-weakly-constant-map f) →
  ( map-extension-weakly-constant-map B f H ∘ unit-trunc-Prop) ~ f
htpy-extension-weakly-constant-map B f H a =
  ap ( pr1)
     ( eq-is-prop
       ( is-prop-image-is-weakly-constant-map B f H)
       ( map-universal-property-trunc-Prop
         ( image-weakly-constant-map-Prop B f H)
         ( λ x → pair (f x) (unit-trunc-Prop (pair x refl)))
         ( unit-trunc-Prop a))
       ( pair (f a) (unit-trunc-Prop (pair a refl))))

htpy-extension-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) {f : A → type-Set B} →
  (g h : type-trunc-Prop A → type-Set B)
  (G : (g ∘ unit-trunc-Prop) ~ f) (H : (h ∘ unit-trunc-Prop) ~ f) → g ~ h
htpy-extension-trunc-Prop B g h G H =
  ind-trunc-Prop
    ( λ x → Id-Prop B (g x) (h x))
    ( λ a → (G a) ∙ (inv (H a)))

total-extension-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  UU (l1 ⊔ l2)
total-extension-trunc-Prop {A = A} B f =
  Σ ( type-trunc-Prop A → type-Set B)
    ( λ g → (g ∘ unit-trunc-Prop) ~ f)

is-contr-total-extension-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  is-weakly-constant-map f → is-contr (total-extension-trunc-Prop B f)
is-contr-total-extension-trunc-Prop B f H =
  pair
    ( pair
      ( map-extension-weakly-constant-map B f H)
      ( htpy-extension-weakly-constant-map B f H))
    ( λ u →
      eq-subtype
        ( λ g →
          is-prop-Π (λ x → is-set-type-Set B (g (unit-trunc-Prop x)) (f x)))
        ( eq-htpy
          ( htpy-extension-trunc-Prop B
            ( map-extension-weakly-constant-map B f H)
            ( pr1 u)
            ( htpy-extension-weakly-constant-map B f H)
            ( pr2 u))))

universal-property-set-quotient-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) →
  is-equiv (precomp-universal-property-set-quotient-trunc-Prop {A = A} B)
universal-property-set-quotient-trunc-Prop {A = A} B =
  is-equiv-is-contr-map
    ( λ f →
      is-contr-equiv
        ( total-extension-trunc-Prop B (pr1 f))
        ( equiv-tot
          ( λ g →
            equiv-prop
              ( is-set-subtype
                ( is-prop-is-weakly-constant-map-Set B)
                ( is-set-function-type (is-set-type-Set B))
                ( pair
                  ( g ∘ unit-trunc-Prop)
                  ( is-weakly-constant-map-precomp-unit-trunc-Prop g))
                ( f))
              ( is-prop-Π
                ( λ x → is-set-type-Set B (g (unit-trunc-Prop x)) (pr1 f x)))
              ( λ p → htpy-eq (ap pr1 p))
              ( λ G →
                eq-subtype
                  ( is-prop-is-weakly-constant-map-Set B)
                  ( eq-htpy G))))
        ( is-contr-total-extension-trunc-Prop B (pr1 f) (pr2 f)))
