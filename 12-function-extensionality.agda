{-# OPTIONS --without-K --exact-split #-}

module 12-function-extensionality where

import 11-truncation-levels
open 11-truncation-levels public

--------------------------------------------------------------------------------

-- Section 12.1 Equivalent forms of Function Extensionality.

-- Proposition 12.1.1

-- Proposition 12.1.1, condition (i)

htpy-eq :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (Id f g) → (f ~ g)
htpy-eq refl = refl-htpy

FUNEXT :
  {i j : Level} {A : UU i} {B : A → UU j} →
  (f : (x : A) → B x) → UU (i ⊔ j)
FUNEXT f = is-fiberwise-equiv (λ g → htpy-eq {f = f} {g = g})

-- Proposition 12.1.1, condition (iii)

ev-refl-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
  ((g : (x : A) → B x) (H : f ~ g) → C g H) → C f refl-htpy
ev-refl-htpy f C φ = φ f refl-htpy

IND-HTPY :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) → UU _
IND-HTPY {l1} {l2} {l3} {A} {B} f =
  (C : (g : (x : A) → B x) → (f ~ g) → UU l3) → sec (ev-refl-htpy f C)

-- Proposition 12.1.1, (i) implies (ii)

abstract
  is-contr-total-htpy-FUNEXT :
    {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) →
    FUNEXT f → is-contr (Σ ((x : A) → B x) (λ g → f ~ g))
  is-contr-total-htpy-FUNEXT f funext-f =
    fundamental-theorem-id' f refl-htpy (λ g → htpy-eq {g = g}) funext-f

-- Proposition 12.1.1, (i) implies (iii)

abstract
  IND-HTPY-FUNEXT :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
    FUNEXT f → IND-HTPY {l3 = l3} f
  IND-HTPY-FUNEXT {l3 = l3} {A = A} {B = B} f funext-f =
    Ind-identity-system l3 f
      ( refl-htpy)
      ( is-contr-total-htpy-FUNEXT f funext-f)

-- Proposition 12.1.1, (iii) implies (i)

abstract
  FUNEXT-IND-HTPY :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
    IND-HTPY {l3 = l1 ⊔ l2} f → FUNEXT f
  FUNEXT-IND-HTPY f ind-htpy-f =
    fundamental-theorem-id-IND-identity-system f
      ( refl-htpy)
      ( ind-htpy-f)
      ( λ g → htpy-eq)

-- Theorem 12.1.4

WEAK-FUNEXT :
  {i j : Level} (A : UU i) (B : A → UU j) → UU (i ⊔ j)
WEAK-FUNEXT A B =
  ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)

abstract
  WEAK-FUNEXT-FUNEXT :
    {l1 l2 : Level} →
    ((A : UU l1) (B : A → UU l2) (f : (x : A) → B x) → FUNEXT f) →
    ((A : UU l1) (B : A → UU l2) → WEAK-FUNEXT A B)
  WEAK-FUNEXT-FUNEXT funext A B is-contr-B =
    let pi-center = (λ x → center (is-contr-B x)) in
    pair
      ( pi-center)
      ( λ f → inv-is-equiv (funext A B pi-center f)
        ( λ x → contraction (is-contr-B x) (f x)))

abstract
  FUNEXT-WEAK-FUNEXT :
    {l1 l2 : Level} →
    ((A : UU l1) (B : A → UU l2) → WEAK-FUNEXT A B) →
    ((A : UU l1) (B : A → UU l2) (f : (x : A) → B x) → FUNEXT f)
  FUNEXT-WEAK-FUNEXT weak-funext A B f =
    fundamental-theorem-id f
      ( refl-htpy)
      ( is-contr-retract-of
        ( (x : A) → Σ (B x) (λ b → Id (f x) b))
        ( pair
          ( λ t x → pair (pr1 t x) (pr2 t x))
          ( pair (λ t → pair (λ x → pr1 (t x)) (λ x → pr2 (t x)))
          ( λ t → eq-pair refl refl)))
        ( weak-funext A
          ( λ x → Σ (B x) (λ b → Id (f x) b))
          ( λ x → is-contr-total-path (f x))))
      ( λ g → htpy-eq {g = g})

-- From now on we will be assuming that function extensionality holds

postulate funext : {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) → FUNEXT f

equiv-funext : {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (Id f g) ≃ (f ~ g)
equiv-funext {f = f} {g} = pair htpy-eq (funext f g) 

abstract
  eq-htpy :
    {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
    (f ~ g) → Id f g
  eq-htpy = inv-is-equiv (funext _ _)
  
  issec-eq-htpy :
    {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
    ((htpy-eq {f = f} {g = g}) ∘ (eq-htpy {f = f} {g = g})) ~ id
  issec-eq-htpy = issec-inv-is-equiv (funext _ _)
  
  isretr-eq-htpy :
    {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
    ((eq-htpy {f = f} {g = g}) ∘ (htpy-eq {f = f} {g = g})) ~ id
  isretr-eq-htpy = isretr-inv-is-equiv (funext _ _)

  is-equiv-eq-htpy :
    {i j : Level} {A : UU i} {B : A → UU j}
    (f g : (x : A) → B x) → is-equiv (eq-htpy {f = f} {g = g})
  is-equiv-eq-htpy f g = is-equiv-inv-is-equiv (funext _ _)

  eq-htpy-refl-htpy :
    {i j : Level} {A : UU i} {B : A → UU j}
    (f : (x : A) → B x) → Id (eq-htpy (refl-htpy {f = f})) refl
  eq-htpy-refl-htpy f = isretr-eq-htpy refl

{-
The immediate proof of the following theorem would be

  is-contr-total-htpy-FUNEXT f (funext f)

We give a different proof to ensure that the center of contraction is the 
expected thing: 

  pair f refl-htpy

-}

abstract
  is-contr-total-htpy :
    {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) →
    is-contr (Σ ((x : A) → B x) (λ g → f ~ g))
  is-contr-total-htpy f =
    pair
      ( pair f refl-htpy)
      ( λ t →
        ( inv (contraction
          ( is-contr-total-htpy-FUNEXT f (funext f))
          ( pair f refl-htpy))) ∙
        ( contraction (is-contr-total-htpy-FUNEXT f (funext f)) t))

abstract
  Ind-htpy :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
    IND-HTPY {l3 = l3} f
  Ind-htpy f = IND-HTPY-FUNEXT f (funext f)
  
  ind-htpy :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
    (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
    C f refl-htpy → {g : (x : A) → B x} (H : f ~ g) → C g H
  ind-htpy f C t {g} = pr1 (Ind-htpy f C) t g
  
  comp-htpy :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
    (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
    (c : C f refl-htpy) →
    Id (ind-htpy f C c refl-htpy) c
  comp-htpy f C = pr2 (Ind-htpy f C)

abstract
  is-contr-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)
  is-contr-Π {A = A} {B = B} = WEAK-FUNEXT-FUNEXT (λ X Y → funext) A B

-- Theorem 12.1.5

abstract
  is-trunc-Π :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-trunc k (B x)) → is-trunc k ((x : A) → B x)
  is-trunc-Π neg-two-𝕋 is-trunc-B = is-contr-Π is-trunc-B
  is-trunc-Π (succ-𝕋 k) is-trunc-B f g =
    is-trunc-is-equiv k (f ~ g) htpy-eq
      ( funext f g)
      ( is-trunc-Π k (λ x → is-trunc-B x (f x) (g x)))

abstract
  is-prop-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-subtype B → is-prop ((x : A) → B x)
  is-prop-Π = is-trunc-Π neg-one-𝕋

abstract
  is-set-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-set (B x)) → is-set ((x : A) → (B x))
  is-set-Π = is-trunc-Π zero-𝕋

abstract
  is-1-type-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-1-type (B x)) → is-1-type ((x : A) → B x)
  is-1-type-Π = is-trunc-Π one-𝕋

-- Corollary 12.1.6

abstract
  is-trunc-function-type :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
    is-trunc k B → is-trunc k (A → B)
  is-trunc-function-type k {A} {B} is-trunc-B =
    is-trunc-Π k {B = λ (x : A) → B} (λ x → is-trunc-B)

abstract
  is-prop-function-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-prop B → is-prop (A → B)
  is-prop-function-type = is-trunc-function-type neg-one-𝕋

abstract
  is-set-function-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-set B → is-set (A → B)
  is-set-function-type = is-trunc-function-type zero-𝕋

abstract
  is-1-type-function-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-1-type B → is-1-type (A → B)
  is-1-type-function-type = is-trunc-function-type one-𝕋

--------------------------------------------------------------------------------

{- We now do some bureaucracy, ensuring that propositions, sets, and 1-types
   are closed under Π and exponents. All of these will be used implicitly in
   the text. -}

-- We define dependent products on propositions --

type-Π-Prop :
  {l1 l2 : Level} (A : UU l1) (P : A → UU-Prop l2) → UU (l1 ⊔ l2)
type-Π-Prop A P = (x : A) → type-Prop (P x)

is-prop-type-Π-Prop :
  {l1 l2 : Level} (A : UU l1) (P : A → UU-Prop l2) → is-prop (type-Π-Prop A P)
is-prop-type-Π-Prop A P = is-prop-Π (λ x → is-prop-type-Prop (P x))

Π-Prop :
  {l1 l2 : Level} (A : UU l1) →
  (A → UU-Prop l2) → UU-Prop (l1 ⊔ l2)
Π-Prop A P =
  pair (type-Π-Prop A P) (is-prop-type-Π-Prop A P)

-- A special case for dependent products on propositions is exponents --

type-function-Prop :
  {l1 l2 : Level} → UU l1 → UU-Prop l2 → UU (l1 ⊔ l2)
type-function-Prop A P = A → type-Prop P

is-prop-type-function-Prop :
  {l1 l2 : Level} (A : UU l1) (P : UU-Prop l2) →
  is-prop (type-function-Prop A P)
is-prop-type-function-Prop A P =
  is-prop-function-type (is-prop-type-Prop P)

function-Prop :
  {l1 l2 : Level} → UU l1 → UU-Prop l2 → UU-Prop (l1 ⊔ l2)
function-Prop A P =
  pair (type-function-Prop A P) (is-prop-type-function-Prop A P)

-- We also define the hom-type of propositions --

type-hom-Prop :
  { l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) → UU (l1 ⊔ l2)
type-hom-Prop P Q = type-function-Prop (type-Prop P) Q

is-prop-type-hom-Prop :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  is-prop (type-hom-Prop P Q)
is-prop-type-hom-Prop P Q = is-prop-type-function-Prop (type-Prop P) Q

hom-Prop :
  { l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU-Prop (l1 ⊔ l2)
hom-Prop P Q =
  pair
    ( type-hom-Prop P Q)
    ( is-prop-type-hom-Prop P Q)

implication-Prop :
  {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU-Prop (l1 ⊔ l2)
implication-Prop P Q = hom-Prop P Q

type-implication-Prop :
  {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU (l1 ⊔ l2)
type-implication-Prop P Q = type-hom-Prop P Q

-- Negation is a special case of function-Prop and hom-Prop

is-prop-neg :
  {l : Level} {A : UU l} → is-prop (¬ A)
is-prop-neg {A = A} = is-prop-function-type is-prop-empty

neg-Prop' :
  {l1 : Level} → UU l1 → UU-Prop l1
neg-Prop' A = pair (¬ A) is-prop-neg

neg-Prop :
  {l1 : Level} → UU-Prop l1 → UU-Prop l1
neg-Prop P = neg-Prop' (type-Prop P)

-- Double negation is a special case of negation

dn-Prop' :
  {l : Level} (A : UU l) → UU-Prop l
dn-Prop' A = neg-Prop' (¬ A)

dn-Prop :
  {l : Level} (P : UU-Prop l) → UU-Prop l
dn-Prop P = dn-Prop' (type-Prop P)

-- We define dependent products on sets by an arbitrary indexing type

type-Π-Set' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-Set l2) → UU (l1 ⊔ l2)
type-Π-Set' A B = (x : A) → type-Set (B x)

is-set-type-Π-Set' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-Set l2) → is-set (type-Π-Set' A B)
is-set-type-Π-Set' A B =
  is-set-Π (λ x → is-set-type-Set (B x))

Π-Set' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-Set l2) → UU-Set (l1 ⊔ l2)
Π-Set' A B = pair (type-Π-Set' A B) (is-set-type-Π-Set' A B)

-- We define dependent products on sets --

type-Π-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : type-Set A → UU-Set l2) → UU (l1 ⊔ l2)
type-Π-Set A B = type-Π-Set' (type-Set A) B

is-set-type-Π-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : type-Set A → UU-Set l2) →
  is-set (type-Π-Set A B)
is-set-type-Π-Set A B =
  is-set-type-Π-Set' (type-Set A) B

Π-Set :
  {l1 l2 : Level} (A : UU-Set l1) →
  (type-Set A → UU-Set l2) → UU-Set (l1 ⊔ l2)
Π-Set A B =
  pair (type-Π-Set A B) (is-set-type-Π-Set A B)

-- We define the type of morphisms between sets --

type-hom-Set :
  {l1 l2 : Level} → UU-Set l1 → UU-Set l2 → UU (l1 ⊔ l2)
type-hom-Set A B = type-Set A → type-Set B

is-set-type-hom-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2) →
  is-set (type-hom-Set A B)
is-set-type-hom-Set A B = is-set-function-type (is-set-type-Set B)

hom-Set :
  {l1 l2 : Level} → UU-Set l1 → UU-Set l2 → UU-Set (l1 ⊔ l2)
hom-Set A B =
  pair (type-hom-Set A B) (is-set-type-hom-Set A B)

-- We define the dependent product of 1-types indexed by an arbitrary type

type-Π-1-Type' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-1-Type l2) → UU (l1 ⊔ l2)
type-Π-1-Type' A B = (x : A) → type-1-Type (B x)

is-1-type-type-Π-1-Type' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-1-Type l2) →
  is-1-type (type-Π-1-Type' A B)
is-1-type-type-Π-1-Type' A B =
  is-1-type-Π (λ x → is-1-type-type-1-Type (B x))

Π-1-Type' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-1-Type l2) → UU-1-Type (l1 ⊔ l2)
Π-1-Type' A B =
  pair (type-Π-1-Type' A B) (is-1-type-type-Π-1-Type' A B)

-- We define the dependent product of 1-types

type-Π-1-Type :
  {l1 l2 : Level} (A : UU-1-Type l1) (B : type-1-Type A → UU-1-Type l2) →
  UU (l1 ⊔ l2)
type-Π-1-Type A B = type-Π-1-Type' (type-1-Type A) B

is-1-type-type-Π-1-Type :
  {l1 l2 : Level} (A : UU-1-Type l1) (B : type-1-Type A → UU-1-Type l2) →
  is-1-type (type-Π-1-Type A B)
is-1-type-type-Π-1-Type A B =
  is-1-type-type-Π-1-Type' (type-1-Type A) B

Π-1-Type :
  {l1 l2 : Level} (A : UU-1-Type l1) (B : type-1-Type A → UU-1-Type l2) →
  UU-1-Type (l1 ⊔ l2)
Π-1-Type A B =
  pair (type-Π-1-Type A B) (is-1-type-type-Π-1-Type A B)

-- We define the type of morphisms between 1-types

type-hom-1-Type :
  {l1 l2 : Level} (A : UU-1-Type l1) (B : UU-1-Type l2) → UU (l1 ⊔ l2)
type-hom-1-Type A B = type-1-Type A → type-1-Type B

is-1-type-type-hom-1-Type :
  {l1 l2 : Level} (A : UU-1-Type l1) (B : UU-1-Type l2) →
  is-1-type (type-hom-1-Type A B)
is-1-type-type-hom-1-Type A B =
  is-1-type-function-type (is-1-type-type-1-Type B)

hom-1-Type :
  {l1 l2 : Level} (A : UU-1-Type l1) (B : UU-1-Type l2) → UU-1-Type (l1 ⊔ l2)
hom-1-Type A B =
  pair (type-hom-1-Type A B) (is-1-type-type-hom-1-Type A B)

{- We define the dependent product of truncated types indexed by an arbitrary
   type. -}

type-Π-Truncated-Type' :
  (k : 𝕋) {l1 l2 : Level} (A : UU l1) (B : A → UU-Truncated-Type k l2) →
  UU (l1 ⊔ l2)
type-Π-Truncated-Type' k A B = (x : A) → type-Truncated-Type k (B x)

is-trunc-type-Π-Truncated-Type' :
  (k : 𝕋) {l1 l2 : Level} (A : UU l1) (B : A → UU-Truncated-Type k l2) →
  is-trunc k (type-Π-Truncated-Type' k A B)
is-trunc-type-Π-Truncated-Type' k A B =
  is-trunc-Π k (λ x → is-trunc-type-Truncated-Type k (B x))

Π-Truncated-Type' :
  (k : 𝕋) {l1 l2 : Level} (A : UU l1) (B : A → UU-Truncated-Type k l2) →
  UU-Truncated-Type k (l1 ⊔ l2)
Π-Truncated-Type' k A B =
  pair (type-Π-Truncated-Type' k A B) (is-trunc-type-Π-Truncated-Type' k A B)

-- We define the dependent product of truncated types

type-Π-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : UU-Truncated-Type k l1)
  (B : type-Truncated-Type k A → UU-Truncated-Type k l2) →
  UU (l1 ⊔ l2)
type-Π-Truncated-Type k A B =
  type-Π-Truncated-Type' k (type-Truncated-Type k A) B

is-trunc-type-Π-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : UU-Truncated-Type k l1)
  (B : type-Truncated-Type k A → UU-Truncated-Type k l2) →
  is-trunc k (type-Π-Truncated-Type k A B)
is-trunc-type-Π-Truncated-Type k A B =
  is-trunc-type-Π-Truncated-Type' k (type-Truncated-Type k A) B

Π-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : UU-Truncated-Type k l1)
  (B : type-Truncated-Type k A → UU-Truncated-Type k l2) →
  UU-Truncated-Type k (l1 ⊔ l2)
Π-Truncated-Type k A B =
  Π-Truncated-Type' k (type-Truncated-Type k A) B

-- We define the type of morphisms between truncated types

type-hom-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : UU-Truncated-Type k l1)
  (B : UU-Truncated-Type k l2) → UU (l1 ⊔ l2)
type-hom-Truncated-Type k A B =
  type-Truncated-Type k A → type-Truncated-Type k B

is-trunc-type-hom-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : UU-Truncated-Type k l1)
  (B : UU-Truncated-Type k l2) →
  is-trunc k (type-hom-Truncated-Type k A B)
is-trunc-type-hom-Truncated-Type k A B =
  is-trunc-function-type k (is-trunc-type-Truncated-Type k B)

hom-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : UU-Truncated-Type k l1)
  (B : UU-Truncated-Type k l2) → UU-Truncated-Type k (l1 ⊔ l2)
hom-Truncated-Type k A B =
  pair (type-hom-Truncated-Type k A B) (is-trunc-type-hom-Truncated-Type k A B)

--------------------------------------------------------------------------------

-- Section 12.2 The type theoretic principle of choice

{- The type theoretic principle of choice is the assertion that Π distributes
   over Σ. In other words, there is an equivalence

   ((x : A) → Σ (B x) (C x)) ≃ Σ ((x : A) → B x) (λ f → (x : A) → C x (f x)).

   In the following we construct this equivalence, and we also characterize the
   relevant identity types. 

   We call the type on the left-hand side Π-total-fam, and we call the type on
   the right-hand side type-choice-∞. -}
   
Π-total-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (C : (x : A) → B x → UU l3) → UU (l1 ⊔ (l2 ⊔ l3))
Π-total-fam {A = A} {B} C = (x : A) → Σ (B x) (C x)

type-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (C : (x : A) → B x → UU l3) → UU (l1 ⊔ (l2 ⊔ l3))
type-choice-∞ {A = A} {B} C = Σ ((x : A) → B x) (λ f → (x : A) → C x (f x))

{- We compute the identity type of Π-total-fam. Note that its characterization
   is again of the form Π-total-fam. -}

{- We compute the identity type of type-choice-∞. Note that its identity 
   type is again of the form type-choice-∞. -}

Eq-type-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : type-choice-∞ C) → UU (l1 ⊔ (l2 ⊔ l3))
Eq-type-choice-∞ {A = A} {B} C t t' =
  type-choice-∞
    ( λ (x : A) (p : Id ((pr1 t) x) ((pr1 t') x)) →
      Id (tr (C x) p ((pr2 t) x)) ((pr2 t') x))

reflexive-Eq-type-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t : type-choice-∞ C) → Eq-type-choice-∞ C t t
reflexive-Eq-type-choice-∞ C (pair f g) = pair refl-htpy refl-htpy

Eq-type-choice-∞-eq :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : type-choice-∞ C) → Id t t' → Eq-type-choice-∞ C t t'
Eq-type-choice-∞-eq C t .t refl = reflexive-Eq-type-choice-∞ C t

abstract
  is-contr-total-Eq-type-choice-∞ :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
    (t : type-choice-∞ C) →
    is-contr (Σ (type-choice-∞ C) (Eq-type-choice-∞ C t))
  is-contr-total-Eq-type-choice-∞ {A = A} {B} C t =
    is-contr-total-Eq-structure
      ( λ f g H → (x : A) → Id (tr (C x) (H x) ((pr2 t) x)) (g x))
      ( is-contr-total-htpy (pr1 t))
      ( pair (pr1 t) refl-htpy)
      ( is-contr-total-htpy (pr2 t))
  
  is-equiv-Eq-type-choice-∞-eq :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
    (t t' : type-choice-∞ C) → is-equiv (Eq-type-choice-∞-eq C t t')
  is-equiv-Eq-type-choice-∞-eq C t =
    fundamental-theorem-id t
      ( reflexive-Eq-type-choice-∞ C t)
      ( is-contr-total-Eq-type-choice-∞ C t)
      ( Eq-type-choice-∞-eq C t)
  
  eq-Eq-type-choice-∞ :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
    {t t' : type-choice-∞ C} → Eq-type-choice-∞ C t t' → Id t t'
  eq-Eq-type-choice-∞ C {t} {t'} =
    inv-is-equiv (is-equiv-Eq-type-choice-∞-eq C t t')

-- We define the map choice-∞, which is not given its own definition environment

choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  Π-total-fam C → type-choice-∞ C
choice-∞ φ = pair (λ x → pr1 (φ x)) (λ x → pr2 (φ x))

-- Theorem 12.2.1

inv-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  type-choice-∞ C → Π-total-fam C
inv-choice-∞ ψ x = pair ((pr1 ψ) x) ((pr2 ψ) x)

issec-inv-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  ( ( choice-∞ {A = A} {B = B} {C = C}) ∘
    ( inv-choice-∞ {A = A} {B = B} {C = C})) ~ id
issec-inv-choice-∞ {A = A} {C = C} (pair ψ ψ') =
  eq-Eq-type-choice-∞ C (pair refl-htpy refl-htpy)

isretr-inv-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  ( ( inv-choice-∞ {A = A} {B = B} {C = C}) ∘
    ( choice-∞ {A = A} {B = B} {C = C})) ~ id
isretr-inv-choice-∞ φ =
  eq-htpy (λ x → eq-pair refl refl)

abstract
  is-equiv-choice-∞ :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
    is-equiv (choice-∞ {A = A} {B = B} {C = C})
  is-equiv-choice-∞ {A = A} {B = B} {C = C} =
    is-equiv-has-inverse
      ( inv-choice-∞ {A = A} {B = B} {C = C})
      ( issec-inv-choice-∞ {A = A} {B = B} {C = C})
      ( isretr-inv-choice-∞ {A = A} {B = B} {C = C})

equiv-choice-∞ :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  Π-total-fam C ≃ type-choice-∞ C
equiv-choice-∞ = pair choice-∞ is-equiv-choice-∞

abstract
  is-equiv-inv-choice-∞ :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
    is-equiv (inv-choice-∞ {A = A} {B = B} {C = C})
  is-equiv-inv-choice-∞ {A = A} {B = B} {C = C} =
    is-equiv-has-inverse
      ( choice-∞ {A = A} {B = B} {C = C})
      ( isretr-inv-choice-∞ {A = A} {B = B} {C = C})
      ( issec-inv-choice-∞ {A = A} {B = B} {C = C})

equiv-inv-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3) →
  (type-choice-∞ C) ≃ (Π-total-fam C)
equiv-inv-choice-∞ C = pair inv-choice-∞ is-equiv-inv-choice-∞

-- Corollary 12.2.2

mapping-into-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : B → UU l3} →
  (A → Σ B C) → Σ (A → B) (λ f → (x : A) → C (f x))
mapping-into-Σ {B = B} = choice-∞ {B = λ x → B}

abstract
  is-equiv-mapping-into-Σ :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
    {C : B → UU l3} → is-equiv (mapping-into-Σ {A = A} {C = C})
  is-equiv-mapping-into-Σ = is-equiv-choice-∞

{- Next we compute the identity type of products of total spaces. Note again
   that the identity type of a product of total spaces is again a product of
   total spaces. -}

Eq-Π-total-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : (a : A) → Σ (B a) (C a)) → UU (l1 ⊔ (l2 ⊔ l3))
Eq-Π-total-fam {A = A} C t t' =
  Π-total-fam (λ x (p : Id (pr1 (t x)) (pr1 (t' x))) →
    Id (tr (C x) p (pr2 (t x))) (pr2 (t' x)))

reflexive-Eq-Π-total-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t : (a : A) → Σ (B a) (C a)) → Eq-Π-total-fam C t t
reflexive-Eq-Π-total-fam C t a = pair refl refl

Eq-Π-total-fam-eq :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : (a : A) → Σ (B a) (C a)) → Id t t' → Eq-Π-total-fam C t t'
Eq-Π-total-fam-eq C t .t refl = reflexive-Eq-Π-total-fam C t

is-contr-total-Eq-Π-total-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t : (a : A) → Σ (B a) (C a)) →
  is-contr (Σ ((a : A) → Σ (B a) (C a)) (Eq-Π-total-fam C t))
is-contr-total-Eq-Π-total-fam {A = A} {B} C t =
  is-contr-equiv'
    ( (a : A) →
      Σ (Σ (B a) (C a)) (λ t' →
        Σ (Id (pr1 (t a)) (pr1 t')) (λ p →
          Id (tr (C a) p (pr2 (t a))) (pr2 t'))))
    ( equiv-choice-∞)
    ( is-contr-Π
      ( λ a →
        is-contr-total-Eq-structure
        ( λ b c p → Id (tr (C a) p (pr2 (t a))) c)
        ( is-contr-total-path (pr1 (t a)))
        ( pair (pr1 (t a)) refl)
        ( is-contr-total-path (pr2 (t a)))))

is-equiv-Eq-Π-total-fam-eq :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : (a : A) → Σ (B a) (C a)) → is-equiv (Eq-Π-total-fam-eq C t t')
is-equiv-Eq-Π-total-fam-eq C t =
  fundamental-theorem-id t
    ( reflexive-Eq-Π-total-fam C t)
    ( is-contr-total-Eq-Π-total-fam C t)
    ( Eq-Π-total-fam-eq C t)

eq-Eq-Π-total-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : (a : A) → Σ (B a) (C a)) → Eq-Π-total-fam C t t' → Id t t'
eq-Eq-Π-total-fam C t t' = inv-is-equiv (is-equiv-Eq-Π-total-fam-eq C t t')

-- Corollary 12.2.3

is-contr-total-Eq-Π :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3) →
  ( is-contr-total-C : (x : A) → is-contr (Σ (B x) (C x))) →
  ( f : (x : A) → B x) →
  is-contr (Σ ((x : A) → B x) (λ g → (x : A) → C x (g x)))
is-contr-total-Eq-Π {A = A} {B} C is-contr-total-C f =
  is-contr-equiv'
    ( (x : A) → Σ (B x) (C x))
    ( equiv-choice-∞)
    ( is-contr-Π is-contr-total-C)

--------------------------------------------------------------------------------

-- Section 12.3 Universal properties

-- Theorem 12.3.1

abstract
  is-equiv-ev-pair :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
    is-equiv (ev-pair {C = C})
  is-equiv-ev-pair =
    pair
      ( pair ind-Σ refl-htpy)
      ( pair ind-Σ
        ( λ f → eq-htpy
          ( ind-Σ
            {C = (λ t → Id (ind-Σ (ev-pair f) t) (f t))}
            (λ x y → refl))))

equiv-ev-pair :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  ((x : Σ A B) → C x) ≃ ((a : A) (b : B a) → C (pair a b))
equiv-ev-pair = pair ev-pair is-equiv-ev-pair

-- Corollary 12.3.2

-- Theorem 12.3.3

ev-refl :
  {l1 l2 : Level} {A : UU l1} (a : A) {B : (x : A) → Id a x → UU l2} →
  ((x : A) (p : Id a x) → B x p) → B a refl
ev-refl a f = f a refl

abstract
  is-equiv-ev-refl :
    {l1 l2 : Level} {A : UU l1} (a : A)
    {B : (x : A) → Id a x → UU l2} → is-equiv (ev-refl a {B = B})
  is-equiv-ev-refl a =
    is-equiv-has-inverse
      ( ind-Id a _)
      ( λ b → refl)
      ( λ f → eq-htpy
        ( λ x → eq-htpy
          ( ind-Id a
            ( λ x' p' → Id (ind-Id a _ (f a refl) x' p') (f x' p'))
            ( refl) x)))

equiv-ev-refl :
  {l1 l2 : Level} {A : UU l1} (a : A) {B : (x : A) → Id a x → UU l2} →
  ((x : A) (p : Id a x) → B x p) ≃ (B a refl)
equiv-ev-refl a = pair (ev-refl a) (is-equiv-ev-refl a)

--------------------------------------------------------------------------------

-- Section 12.4 Composing with equivalences.

precomp-Π :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ((b : B) → C b) → ((a : A) → C (f a))
precomp-Π f C h a = h (f a)

-- Theorem 12.4.1

tr-precompose-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
  (f : A → B) {x y : A} (p : Id x y) → tr C (ap f p) ~ tr (λ x → C (f x)) p
tr-precompose-fam C f refl = refl-htpy

abstract
  is-equiv-precomp-Π-is-half-adjoint-equivalence :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-half-adjoint-equivalence f →
    (C : B → UU l3) → is-equiv (precomp-Π f C)
  is-equiv-precomp-Π-is-half-adjoint-equivalence f
    ( pair g (pair issec-g (pair isretr-g coh))) C = 
    is-equiv-has-inverse
      (λ s y → tr C (issec-g y) (s (g y)))
      ( λ s → eq-htpy (λ x → 
        ( ap (λ t → tr C t (s (g (f x)))) (coh x)) ∙
        ( ( tr-precompose-fam C f (isretr-g x) (s (g (f x)))) ∙
          ( apd s (isretr-g x)))))
      ( λ s → eq-htpy λ y → apd s (issec-g y))

abstract
  is-equiv-precomp-Π-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) → is-equiv f →
    (C : B → UU l3) → is-equiv (precomp-Π f C)
  is-equiv-precomp-Π-is-equiv f is-equiv-f =
    is-equiv-precomp-Π-is-half-adjoint-equivalence f
      ( is-half-adjoint-equivalence-is-path-split f
        ( is-path-split-is-equiv f is-equiv-f))

precomp-Π-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  (C : B → UU l3) → ((b : B) → C b) ≃ ((a : A) → C (map-equiv e a))
precomp-Π-equiv e C =
  pair
    ( precomp-Π (map-equiv e) C)
    ( is-equiv-precomp-Π-is-equiv (map-equiv e) (is-equiv-map-equiv e) C)

abstract
  ind-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
    (C : B → UU l3) (f : A → B) (is-equiv-f : is-equiv f) →
    ((x : A) → C (f x)) → ((y : B) → C y)
  ind-is-equiv C f is-equiv-f =
    inv-is-equiv (is-equiv-precomp-Π-is-equiv f is-equiv-f C)
  
  comp-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
    (f : A → B) (is-equiv-f : is-equiv f) (h : (x : A) → C (f x)) →
    Id (λ x → (ind-is-equiv C f is-equiv-f h) (f x)) h
  comp-is-equiv C f is-equiv-f h =
    issec-inv-is-equiv (is-equiv-precomp-Π-is-equiv f is-equiv-f C) h
  
  htpy-comp-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
    (C : B → UU l3) (f : A → B) (is-equiv-f : is-equiv f)
    (h : (x : A) → C (f x)) →
    (λ x → (ind-is-equiv C f is-equiv-f h) (f x)) ~ h
  htpy-comp-is-equiv C f is-equiv-f h = htpy-eq (comp-is-equiv C f is-equiv-f h)

precomp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : UU l3) →
  (B → C) → (A → C)
precomp f C = precomp-Π f (λ b → C)

abstract
  is-equiv-precomp-is-equiv-precomp-Π :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    ((C : B → UU l3) → is-equiv (precomp-Π f C)) →
    ((C : UU l3) → is-equiv (precomp f C))
  is-equiv-precomp-is-equiv-precomp-Π f is-equiv-precomp-Π-f C =
    is-equiv-precomp-Π-f (λ y → C)

abstract
  is-equiv-precomp-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) → is-equiv f →
    (C : UU l3) → is-equiv (precomp f C)
  is-equiv-precomp-is-equiv f is-equiv-f =
    is-equiv-precomp-is-equiv-precomp-Π f
      ( is-equiv-precomp-Π-is-equiv f is-equiv-f)

equiv-precomp-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) (C : UU l3) →
  (B → C) ≃ (A → C)
equiv-precomp-equiv e C =
  pair
    ( precomp (map-equiv e) C)
    ( is-equiv-precomp-is-equiv (map-equiv e) (is-equiv-map-equiv e) C)

abstract
  is-equiv-is-equiv-precomp-subuniverse :
    { l1 l2 : Level}
    ( α : Level → Level) (P : (l : Level) → UU l → UU (α l))
    ( A : Σ (UU l1) (P l1)) (B : Σ (UU l2) (P l2)) (f : pr1 A → pr1 B) →
    ( (l : Level) (C : Σ (UU l) (P l)) →
      is-equiv (precomp f (pr1 C))) →
    is-equiv f
  is-equiv-is-equiv-precomp-subuniverse α P A B f is-equiv-precomp-f =
    let retr-f = center (is-contr-map-is-equiv (is-equiv-precomp-f _ A) id) in
    is-equiv-has-inverse
      ( pr1 retr-f)
      ( htpy-eq (ap pr1 (eq-is-contr
        ( is-contr-map-is-equiv (is-equiv-precomp-f _ B) f)
          ( pair
            ( f ∘ (pr1 retr-f))
            ( ap (λ (g : pr1 A → pr1 A) → f ∘ g) (pr2 retr-f)))
        ( pair id refl))))
      ( htpy-eq (pr2 retr-f))

abstract
  is-equiv-is-equiv-precomp :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    ((l : Level) (C : UU l) → is-equiv (precomp f C)) → is-equiv f
  is-equiv-is-equiv-precomp {A = A} {B = B} f is-equiv-precomp-f =
    is-equiv-is-equiv-precomp-subuniverse
      ( const Level Level lzero)
      ( λ l X → unit)
      ( pair A star)
      ( pair B star)
      ( f)
      ( λ l C → is-equiv-precomp-f l (pr1 C))
