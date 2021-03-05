{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module book.18-set-quotients where

open import book.17-univalence public

--------------------------------------------------------------------------------

-- Section 16.1 Equivalence relations

-- Definition 16.1.1

Rel-Prop :
  (l : Level) {l1 : Level} (A : UU l1) → UU ((lsuc l) ⊔ l1)
Rel-Prop l A = A → (A → UU-Prop l)

type-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} (R : Rel-Prop l2 A) → A → A → UU l2
type-Rel-Prop R x y = pr1 (R x y)

is-prop-type-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} (R : Rel-Prop l2 A) →
  (x y : A) → is-prop (type-Rel-Prop R x y)
is-prop-type-Rel-Prop R x y = pr2 (R x y)

is-reflexive-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} → Rel-Prop l2 A → UU (l1 ⊔ l2)
is-reflexive-Rel-Prop {A = A} R =
  (x : A) → type-Rel-Prop R x x

is-symmetric-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} → Rel-Prop l2 A → UU (l1 ⊔ l2)
is-symmetric-Rel-Prop {A = A} R =
  (x y : A) → type-Rel-Prop R x y → type-Rel-Prop R y x

is-transitive-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} → Rel-Prop l2 A → UU (l1 ⊔ l2)
is-transitive-Rel-Prop {A = A} R =
  (x y z : A) → type-Rel-Prop R x y → type-Rel-Prop R y z → type-Rel-Prop R x z

is-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} (R : Rel-Prop l2 A) → UU (l1 ⊔ l2)
is-equivalence-relation R =
  is-reflexive-Rel-Prop R ×
    ( is-symmetric-Rel-Prop R × is-transitive-Rel-Prop R)

Eq-Rel :
  (l : Level) {l1 : Level} (A : UU l1) → UU ((lsuc l) ⊔ l1)
Eq-Rel l A = Σ (Rel-Prop l A) is-equivalence-relation

prop-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} → Eq-Rel l2 A → Rel-Prop l2 A
prop-Eq-Rel = pr1

type-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} → Eq-Rel l2 A → A → A → UU l2
type-Eq-Rel R = type-Rel-Prop (prop-Eq-Rel R)

is-equivalence-relation-prop-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  is-equivalence-relation (prop-Eq-Rel R)
is-equivalence-relation-prop-Eq-Rel R = pr2 R

refl-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  is-reflexive-Rel-Prop (prop-Eq-Rel R)
refl-Eq-Rel R = pr1 (is-equivalence-relation-prop-Eq-Rel R)

symm-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  is-symmetric-Rel-Prop (prop-Eq-Rel R)
symm-Eq-Rel R = pr1 (pr2 (is-equivalence-relation-prop-Eq-Rel R))

trans-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  is-transitive-Rel-Prop (prop-Eq-Rel R)
trans-Eq-Rel R = pr2 (pr2 (is-equivalence-relation-prop-Eq-Rel R))

-- Definition 16.1.2

class-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (x : A) → A → UU l2
class-Eq-Rel = type-Eq-Rel

is-equivalence-class-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  (A → UU-Prop l2) → UU (l1 ⊔ lsuc l2)
is-equivalence-class-Eq-Rel {A = A} R P = 
  type-trunc-Prop (Σ A (λ x → Id (type-Prop ∘ P) (class-Eq-Rel R x)))

quotient-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) → UU (l1 ⊔ lsuc l2)
quotient-Eq-Rel R = im (prop-Eq-Rel R)

map-quotient-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  A → quotient-Eq-Rel R
map-quotient-Eq-Rel R = map-im (prop-Eq-Rel R)

class-quotient-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  quotient-Eq-Rel R → (A → UU-Prop l2)
class-quotient-Eq-Rel R P = pr1 P

type-class-quotient-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  quotient-Eq-Rel R → (A → UU l2)
type-class-quotient-Eq-Rel R P x = type-Prop (class-quotient-Eq-Rel R P x)

-- Proposition 16.1.3

center-total-class-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (x : A) →
  Σ (quotient-Eq-Rel R) (λ P → type-class-quotient-Eq-Rel R P x)
center-total-class-Eq-Rel R x =
  pair
    ( map-quotient-Eq-Rel R x)
    ( refl-Eq-Rel R x)

contraction-total-class-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (x : A) →
  ( t : Σ (quotient-Eq-Rel R) (λ P → type-class-quotient-Eq-Rel R P x)) →
  Id (center-total-class-Eq-Rel R x) t
contraction-total-class-Eq-Rel R x (pair (pair P p) H) =
  map-universal-property-trunc-Prop
    ( pair
      ( Id (center-total-class-Eq-Rel R x) (pair (pair P p) H))
      {! is-set-im!})
    {!!}
    {!!}

is-contr-total-class-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (x : A) →
  is-contr
    ( Σ (quotient-Eq-Rel R) (λ P → type-class-quotient-Eq-Rel R P x))
is-contr-total-class-Eq-Rel R x =
  pair
    ( center-total-class-Eq-Rel R x)
    ( contraction-total-class-Eq-Rel R x)

--------------------------------------------------------------------------------

{- Section 15.2 The universal property of set quotients -}

identifies-Eq-Rel :
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  {B : UU l3} → (A → B) → UU (l1 ⊔ (l2 ⊔ l3))
identifies-Eq-Rel {A = A} R f =
  (x y : A) → type-Eq-Rel R x y → Id (f x) (f y)

precomp-map-universal-property-Eq-Rel :
  {l l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  {B : UU-Set l3} (f : A → type-Set B) (H : identifies-Eq-Rel R f) →
  (X : UU-Set l) → (type-hom-Set B X) → Σ (A → type-Set X) (identifies-Eq-Rel R)
precomp-map-universal-property-Eq-Rel R f H X g =
  pair (g ∘ f) (λ x y r → ap g (H x y r))

universal-property-set-quotient :
  (l : Level) {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  {B : UU-Set l3} (f : A → type-Set B) (H : identifies-Eq-Rel R f) → UU _
universal-property-set-quotient l R {B} f H =
  (X : UU-Set l) → is-equiv (precomp-map-universal-property-Eq-Rel R {B} f H X)

{- Effective quotients -}

is-effective-Set-Quotient :
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU-Set l3)
  (f : A → type-Set B) (H : identifies-Eq-Rel R f) → UU (l1 ⊔ l2 ⊔ l3)
is-effective-Set-Quotient {A = A} R B f H = (x y : A) → is-equiv (H x y)

-- Section 13.4

--------------------------------------------------------------------------------

{- Set truncations -}

precomp-Set :
  { l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) →
  (A → type-Set B) → (C : UU-Set l3) →
  (type-hom-Set B C) → (A → type-Set C)
precomp-Set B f C g = g ∘ f

is-set-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) →
  ( A → type-Set B) → UU (lsuc l ⊔ l1 ⊔ l2)
is-set-truncation l B f =
  (C : UU-Set l) → is-equiv (precomp-Set B f C)

universal-property-set-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1}
  (B : UU-Set l2) (f : A → type-Set B) → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-set-truncation l {A = A} B f =
  (C : UU-Set l) (g : A → type-Set C) →
  is-contr (Σ (type-hom-Set B C) (λ h → (h ∘ f) ~  g))

universal-property-is-set-truncation :
  (l : Level) {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  is-set-truncation l B f → universal-property-set-truncation l B f
universal-property-is-set-truncation l B f is-settr-f C g =
  is-contr-equiv'
    ( Σ (type-hom-Set B C) (λ h → Id (h ∘ f) g))
    ( equiv-tot (λ h → equiv-funext))
    ( is-contr-map-is-equiv (is-settr-f C) g)

map-is-set-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  ({l : Level} → is-set-truncation l B f) →
  (C : UU-Set l3) (g : A → type-Set C) → type-hom-Set B C
map-is-set-truncation B f is-settr-f C g =
  pr1
    ( center
      ( universal-property-is-set-truncation _ B f is-settr-f C g))

htpy-is-set-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  (is-settr-f : {l : Level} → is-set-truncation l B f) →
  (C : UU-Set l3) (g : A → type-Set C) →
  ((map-is-set-truncation B f is-settr-f C g) ∘ f) ~ g
htpy-is-set-truncation B f is-settr-f C g =
  pr2
    ( center
      ( universal-property-is-set-truncation _ B f is-settr-f C g))

is-set-truncation-universal-property :
  (l : Level) {l1 l2 : Level} {A : UU l1}
  (B : UU-Set l2) (f : A → type-Set B) →
  universal-property-set-truncation l B f →
  is-set-truncation l B f
is-set-truncation-universal-property l B f up-f C =
  is-equiv-is-contr-map
    ( λ g → is-contr-equiv
      ( Σ (type-hom-Set B C) (λ h → (h ∘ f) ~ g))
      ( equiv-tot (λ h → equiv-funext))
      ( up-f C g))

postulate type-trunc-Set : {l : Level} → UU l → UU l

postulate is-set-type-trunc-Set : {l : Level} {A : UU l} → is-set (type-trunc-Set A)

trunc-Set : {l : Level} → UU l → UU-Set l
trunc-Set A = pair (type-trunc-Set A) is-set-type-trunc-Set

postulate unit-trunc-Set : {l : Level} {A : UU l} → A → type-Set (trunc-Set A)

postulate is-set-truncation-trunc-Set : {l1 l2 : Level} (A : UU l1) → is-set-truncation l2 (trunc-Set A) unit-trunc-Set

universal-property-trunc-Set : {l1 l2 : Level} (A : UU l1) →
  universal-property-set-truncation l2
    ( trunc-Set A)
    ( unit-trunc-Set)
universal-property-trunc-Set A =
  universal-property-is-set-truncation _
    ( trunc-Set A)
    ( unit-trunc-Set)
    ( is-set-truncation-trunc-Set A)

map-universal-property-trunc-Set :
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) →
  (A → type-Set B) → type-hom-Set (trunc-Set A) B
map-universal-property-trunc-Set {A = A} B f =
  map-is-set-truncation
    ( trunc-Set A)
    ( unit-trunc-Set)
    ( is-set-truncation-trunc-Set A)
    ( B)
    ( f)

apply-universal-property-trunc-Set :
  {l1 l2 : Level} {A : UU l1} (t : type-trunc-Set A) (B : UU-Set l2) →
  (A → type-Set B) → type-Set B
apply-universal-property-trunc-Set t B f =
  map-universal-property-trunc-Set B f t
