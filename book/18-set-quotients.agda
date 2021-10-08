{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module book.18-set-quotients where

open import book.17-univalence public

--------------------------------------------------------------------------------

-- Section 18.0 Resizing axioms

-- Definition 18.0.1

is-small :
  (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
is-small l A = Σ (UU l) (λ X → A ≃ X)

type-is-small :
  {l l1 : Level} {A : UU l1} → is-small l A → UU l
type-is-small = pr1

equiv-is-small :
  {l l1 : Level} {A : UU l1} (H : is-small l A) → A ≃ type-is-small H
equiv-is-small = pr2

map-equiv-is-small :
  {l l1 : Level} {A : UU l1} (H : is-small l A) → A → type-is-small H
map-equiv-is-small H = map-equiv (equiv-is-small H)

map-inv-equiv-is-small :
  {l l1 : Level} {A : UU l1} (H : is-small l A) → type-is-small H → A
map-inv-equiv-is-small H = map-inv-equiv (equiv-is-small H)

is-small-map :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A → B) → UU (lsuc l ⊔ (l1 ⊔ l2))
is-small-map l {B = B} f = (b : B) → is-small l (fib f b)

is-locally-small :
  (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
is-locally-small l A = (x y : A) → is-small l (Id x y)

-- Example 18.0.2

-- Closure properties of small types

is-small-equiv :
  (l : Level) {l1 l2 : Level} {A : UU l1} (B : UU l2) →
  A ≃ B → is-small l B → is-small l A
is-small-equiv l B e (pair X h) = pair X (h ∘e e)

is-small-Σ :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-small l A → ((x : A) → is-small l (B x)) → is-small l (Σ A B)
is-small-Σ l {B = B} (pair X e) H =
  pair
    ( Σ X (λ x → pr1 (H (map-inv-equiv e x))))
    ( equiv-Σ
      ( λ x → pr1 (H (map-inv-equiv e x)))
      ( e)
      ( λ a →
        ( equiv-tr
          ( λ t → pr1 (H t))
          ( inv (isretr-map-inv-equiv e a))) ∘e
        ( pr2 (H a))))

-- Example 18.0.2 (i)

is-locally-small-is-small :
  (l : Level) {l1 : Level} {A : UU l1} → is-small l A → is-locally-small l A
is-locally-small-is-small l (pair X e) x y =
  pair
    ( Id (map-equiv e x) (map-equiv e y))
    ( equiv-ap e x y)

is-small-fib :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-small l A → is-small l B → (b : B) → is-small l (fib f b)
is-small-fib l f H K b =
  is-small-Σ l H (λ a → is-locally-small-is-small l K (f a) b)

-- Example 18.0.2 (ii)

is-small-is-contr :
  (l : Level) {l1 : Level} {A : UU l1} → is-contr A → is-small l A
is-small-is-contr l H =
  pair (raise-unit l) (equiv-is-contr H is-contr-raise-unit)

is-small-is-prop :
  (l : Level) {l1 : Level} {A : UU l1} → is-prop A → is-locally-small l A
is-small-is-prop l H x y = is-small-is-contr l (H x y)

-- Example 18.0.2 (iii)

is-locally-small-UU :
  {l : Level} → is-locally-small l (UU l)
is-locally-small-UU X Y = pair (X ≃ Y) equiv-univalence

-- Example 18.0.2 (iv)

is-small-Π :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-small l A → ((x : A) → is-small l (B x)) → is-small l ((x : A) → B x)
is-small-Π l {B = B} (pair X e) H =
  pair
    ( (x : X) → pr1 (H (map-inv-equiv e x)))
    ( equiv-Π
      ( λ (x : X) → pr1 (H (map-inv-equiv e x)))
      ( e)
      ( λ a →
        ( equiv-tr
          ( λ t → pr1 (H t))
          ( inv (isretr-map-inv-equiv e a))) ∘e
        ( pr2 (H a))))

is-locally-small-Π :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-small l A → ((x : A) → is-locally-small l (B x)) →
  is-locally-small l ((x : A) → B x)
is-locally-small-Π l H K f g =
  is-small-equiv l (f ~ g) equiv-funext
    ( is-small-Π l H (λ x → K x (f x) (g x)))

-- Example 18.0.2 (v)

UU-is-small : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
UU-is-small l1 l2 = Σ (UU l2) (is-small l1)

equiv-UU-is-small :
  (l1 l2 : Level) → UU-is-small l1 l2 ≃ UU-is-small l2 l1
equiv-UU-is-small l1 l2 =
  ( equiv-tot (λ X → equiv-tot (λ Y → equiv-inv-equiv))) ∘e
  ( equiv-Σ-swap (UU l2) (UU l1) _≃_)

-- Example 18.0.2 (vi)

is-small-decidable-Prop :
  (l1 l2 : Level) → is-small l2 (decidable-Prop l1)
is-small-decidable-Prop l1 l2 =
  pair ( raise-Fin l2 two-ℕ)
       ( equiv-raise l2 (Fin two-ℕ) ∘e equiv-Fin-two-ℕ-decidable-Prop)

-- Proposition 18.0.3

is-prop-is-small :
  (l : Level) {l1 : Level} (A : UU l1) → is-prop (is-small l A)
is-prop-is-small l A =
  is-prop-is-proof-irrelevant
    ( λ Xe →
      is-contr-equiv'
        ( Σ (UU l) (λ Y → (pr1 Xe) ≃ Y))
        ( equiv-tot ((λ Y → equiv-precomp-equiv (pr2 Xe) Y)))
        ( is-contr-total-equiv (pr1 Xe)))

is-small-Prop :
  (l : Level) {l1 : Level} (A : UU l1) → UU-Prop (lsuc l ⊔ l1)
is-small-Prop l A = pair (is-small l A) (is-prop-is-small l A)

-- Corollary 18.0.4

is-prop-is-locally-small :
  (l : Level) {l1 : Level} (A : UU l1) → is-prop (is-locally-small l A)
is-prop-is-locally-small l A =
  is-prop-Π (λ x → is-prop-Π (λ y → is-prop-is-small l (Id x y)))

is-locally-small-Prop :
  (l : Level) {l1 : Level} (A : UU l1) → UU-Prop (lsuc l ⊔ l1)
is-locally-small-Prop l A =
  pair (is-locally-small l A) (is-prop-is-locally-small l A)

is-prop-is-small-map :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-prop (is-small-map l f)
is-prop-is-small-map l f =
  is-prop-Π (λ x → is-prop-is-small l (fib f x))

is-small-map-Prop :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  UU-Prop (lsuc l ⊔ l1 ⊔ l2)
is-small-map-Prop l f =
  pair (is-small-map l f) (is-prop-is-small-map l f)

-- Corollary 18.0.5

is-small-mere-equiv :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} → mere-equiv A B →
  is-small l B → is-small l A
is-small-mere-equiv l e H =
  apply-universal-property-trunc-Prop e
    ( is-small-Prop l _)
    ( λ e' → is-small-equiv l _ e' H)

--------------------------------------------------------------------------------

-- Section 18.1 Equivalence relations

-- Definition 18.1.1

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
  {x : A} → type-Rel-Prop R x x

is-symmetric-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} → Rel-Prop l2 A → UU (l1 ⊔ l2)
is-symmetric-Rel-Prop {A = A} R =
  {x y : A} → type-Rel-Prop R x y → type-Rel-Prop R y x

is-transitive-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} → Rel-Prop l2 A → UU (l1 ⊔ l2)
is-transitive-Rel-Prop {A = A} R =
  {x y z : A} → type-Rel-Prop R x y → type-Rel-Prop R y z → type-Rel-Prop R x z

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

is-prop-type-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (x y : A) →
  is-prop (type-Eq-Rel R x y)
is-prop-type-Eq-Rel R = is-prop-type-Rel-Prop (prop-Eq-Rel R)

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

equiv-symm-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (x y : A) →
  type-Eq-Rel R x y ≃ type-Eq-Rel R y x
equiv-symm-Eq-Rel R x y =
  equiv-prop
    ( is-prop-type-Eq-Rel R x y)
    ( is-prop-type-Eq-Rel R y x)
    ( symm-Eq-Rel R)
    ( symm-Eq-Rel R)

trans-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  is-transitive-Rel-Prop (prop-Eq-Rel R)
trans-Eq-Rel R = pr2 (pr2 (is-equivalence-relation-prop-Eq-Rel R))

-- Example

ℕ\0 : UU lzero
ℕ\0 = Σ ℕ is-nonzero-ℕ

pre-ℚ : UU lzero
pre-ℚ = ℤ × ℕ\0

numerator-pre-ℚ : pre-ℚ → ℤ
numerator-pre-ℚ x = pr1 x

denominator-pre-ℚ : pre-ℚ → ℕ
denominator-pre-ℚ x = pr1 (pr2 x)

int-denominator-pre-ℚ : pre-ℚ → ℤ
int-denominator-pre-ℚ x = int-ℕ (denominator-pre-ℚ x)

is-nonzero-denominator-pre-ℚ : (x : pre-ℚ) → is-nonzero-ℕ (denominator-pre-ℚ x)
is-nonzero-denominator-pre-ℚ x = pr2 (pr2 x)

is-nonzero-int-denominator-pre-ℚ :
  (x : pre-ℚ) → is-nonzero-ℤ (int-denominator-pre-ℚ x)
is-nonzero-int-denominator-pre-ℚ x =
  is-nonzero-int-ℕ
    ( denominator-pre-ℚ x)
    ( is-nonzero-denominator-pre-ℚ x)

sim-pre-ℚ-Prop : pre-ℚ → pre-ℚ → UU-Prop lzero
sim-pre-ℚ-Prop x y =
  Id-Prop ℤ-Set
    (mul-ℤ (numerator-pre-ℚ x) (int-ℕ (denominator-pre-ℚ y)))
    (mul-ℤ (numerator-pre-ℚ y) (int-ℕ (denominator-pre-ℚ x)))

sim-pre-ℚ : pre-ℚ → pre-ℚ → UU lzero
sim-pre-ℚ x y = type-Prop (sim-pre-ℚ-Prop x y)

is-prop-sim-pre-ℚ : (x y : pre-ℚ) → is-prop (sim-pre-ℚ x y)
is-prop-sim-pre-ℚ x y = is-prop-type-Prop (sim-pre-ℚ-Prop x y)

refl-sim-pre-ℚ : (x : pre-ℚ) → sim-pre-ℚ x x
refl-sim-pre-ℚ x = refl

symm-sim-pre-ℚ : {x y : pre-ℚ} → sim-pre-ℚ x y → sim-pre-ℚ y x
symm-sim-pre-ℚ r = inv r

trans-sim-pre-ℚ :
  {x y z : pre-ℚ} → sim-pre-ℚ x y → sim-pre-ℚ y z → sim-pre-ℚ x z
trans-sim-pre-ℚ {x} {y} {z} r s =
  is-injective-mul-ℤ'
    ( int-denominator-pre-ℚ y)
    ( is-nonzero-int-denominator-pre-ℚ y)
    ( ( associative-mul-ℤ
        ( numerator-pre-ℚ x)
        ( int-denominator-pre-ℚ z)
        ( int-denominator-pre-ℚ y)) ∙
      ( ( ap
          ( mul-ℤ (numerator-pre-ℚ x))
          ( commutative-mul-ℤ
            ( int-denominator-pre-ℚ z)
            ( int-denominator-pre-ℚ y))) ∙
        ( ( inv
            ( associative-mul-ℤ
              ( numerator-pre-ℚ x)
              ( int-denominator-pre-ℚ y)
              ( int-denominator-pre-ℚ z))) ∙
          ( ( ap ( mul-ℤ' (int-denominator-pre-ℚ z)) r) ∙
            ( ( associative-mul-ℤ
                ( numerator-pre-ℚ y)
                ( int-denominator-pre-ℚ x)
                ( int-denominator-pre-ℚ z)) ∙
              ( ( ap
                  ( mul-ℤ (numerator-pre-ℚ y))
                  ( commutative-mul-ℤ
                    ( int-denominator-pre-ℚ x)
                    ( int-denominator-pre-ℚ z))) ∙
                ( ( inv
                    ( associative-mul-ℤ
                      ( numerator-pre-ℚ y)
                      ( int-denominator-pre-ℚ z)
                      ( int-denominator-pre-ℚ x))) ∙
                  ( ( ap (mul-ℤ' (int-denominator-pre-ℚ x)) s) ∙
                    ( ( associative-mul-ℤ
                        ( numerator-pre-ℚ z)
                        ( int-denominator-pre-ℚ y)
                        ( int-denominator-pre-ℚ x)) ∙
                      ( ( ap
                          ( mul-ℤ (numerator-pre-ℚ z))
                          ( commutative-mul-ℤ
                            ( int-denominator-pre-ℚ y)
                            ( int-denominator-pre-ℚ x))) ∙
                        ( inv
                          ( associative-mul-ℤ
                            ( numerator-pre-ℚ z)
                            ( int-denominator-pre-ℚ x)
                            ( int-denominator-pre-ℚ y)))))))))))))

-- Definition 18.1.2

class-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (x : A) → A → UU l2
class-Eq-Rel = type-Eq-Rel

is-equivalence-class-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  (A → UU-Prop l2) → UU (l1 ⊔ lsuc l2)
is-equivalence-class-Eq-Rel {A = A} R P =
  ∃ (λ x → Id (type-Prop ∘ P) (class-Eq-Rel R x))

set-quotient :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) → UU (l1 ⊔ lsuc l2)
set-quotient R = im (prop-Eq-Rel R)

map-set-quotient :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  A → set-quotient R
map-set-quotient R = map-im (prop-Eq-Rel R)

class-set-quotient :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  set-quotient R → (A → UU-Prop l2)
class-set-quotient R P = pr1 P

type-class-set-quotient :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  set-quotient R → (A → UU l2)
type-class-set-quotient R P x = type-Prop (class-set-quotient R P x)

is-prop-type-class-set-quotient :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  (x : set-quotient R) (a : A) → is-prop (type-class-set-quotient R x a)
is-prop-type-class-set-quotient R P x =
  is-prop-type-Prop (class-set-quotient R P x)

-- Bureaucracy

is-set-set-quotient :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) → is-set (set-quotient R)
is-set-set-quotient {l1} {l2} R =
  is-set-im (prop-Eq-Rel R) (is-set-function-type (is-set-UU-Prop l2))

quotient-Set :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) → UU-Set (l1 ⊔ lsuc l2)
quotient-Set R = pair (set-quotient R) (is-set-set-quotient R)

-- Proposition 18.1.3

center-total-class-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (x : A) →
  Σ (set-quotient R) (λ P → type-class-set-quotient R P x)
center-total-class-Eq-Rel R x =
  pair
    ( map-set-quotient R x)
    ( refl-Eq-Rel R)

contraction-total-class-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (a : A) →
  ( t : Σ (set-quotient R) (λ P → type-class-set-quotient R P a)) →
  Id (center-total-class-Eq-Rel R a) t
contraction-total-class-Eq-Rel {l1} {l2} {A} R a (pair (pair P p) H) =
  eq-subtype
    ( λ Q → is-prop-type-class-set-quotient R Q a)
    ( apply-universal-property-trunc-Prop
      ( p)
      ( Id-Prop (quotient-Set R) (map-set-quotient R a) (pair P p))
      ( α))
  where
  α : fib (pr1 R) P → Id (map-set-quotient R a) (pair P p)
  α (pair x refl) =
    eq-subtype
      ( λ z → is-prop-type-trunc-Prop)
      ( eq-htpy
        ( λ y →
          eq-iff
            ( trans-Eq-Rel R H)
            ( trans-Eq-Rel R (symm-Eq-Rel R H))))

is-contr-total-class-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (a : A) →
  is-contr
    ( Σ (set-quotient R) (λ P → type-class-set-quotient R P a))
is-contr-total-class-Eq-Rel R a =
  pair
    ( center-total-class-Eq-Rel R a)
    ( contraction-total-class-Eq-Rel R a)

related-eq-quotient :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (a : A)
  (q : set-quotient R) → Id (map-set-quotient R a) q →
  type-class-set-quotient R q a
related-eq-quotient R a .(map-set-quotient R a) refl = refl-Eq-Rel R

is-equiv-related-eq-quotient :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (a : A)
  (q : set-quotient R) → is-equiv (related-eq-quotient R a q)
is-equiv-related-eq-quotient R a =
  fundamental-theorem-id
    ( map-set-quotient R a)
    ( refl-Eq-Rel R)
    ( is-contr-total-class-Eq-Rel R a)
    ( related-eq-quotient R a)

effective-quotient' :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (a : A)
  (q : set-quotient R) →
  Id (map-set-quotient R a) q ≃ type-class-set-quotient R q a
effective-quotient' R a q =
  pair (related-eq-quotient R a q) (is-equiv-related-eq-quotient R a q)

eq-effective-quotient' :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (a : A)
  (q : set-quotient R) → type-class-set-quotient R q a →
  Id (map-set-quotient R a) q
eq-effective-quotient' R a q =
  map-inv-is-equiv (is-equiv-related-eq-quotient R a q)

-- Corollary 18.1.4

is-effective :
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) {B : UU l3}
  (f : A → B) → UU (l1 ⊔ l2 ⊔ l3)
is-effective {A = A} R f =
  (x y : A) → (Id (f x) (f y) ≃ type-Eq-Rel R x y)

is-effective-map-set-quotient :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  is-effective R (map-set-quotient R)
is-effective-map-set-quotient R x y =
  ( equiv-symm-Eq-Rel R y x) ∘e
  ( effective-quotient' R x (map-set-quotient R y))

--------------------------------------------------------------------------------

{- Section 18.2 The universal property of set quotients -}

-- Definition 18.2.1

identifies-Eq-Rel :
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  {B : UU l3} → (A → B) → UU (l1 ⊔ (l2 ⊔ l3))
identifies-Eq-Rel {A = A} R f =
  {x y : A} → type-Eq-Rel R x y → Id (f x) (f y)

is-prop-identifies-Eq-Rel :
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU-Set l3)
  (f : A → type-Set B) → is-prop (identifies-Eq-Rel R f)
is-prop-identifies-Eq-Rel R B f =
  is-prop-Π'
    ( λ x →
      is-prop-Π'
        ( λ y →
          is-prop-function-type (is-set-type-Set B (f x) (f y))))

precomp-Set-Quotient :
  {l l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  (B : UU-Set l3) (f : A → type-Set B) (H : identifies-Eq-Rel R f) →
  (X : UU-Set l) → (type-hom-Set B X) → Σ (A → type-Set X) (identifies-Eq-Rel R)
precomp-Set-Quotient R B f H X g =
  pair (g ∘ f) (λ r → ap g (H r))

is-set-quotient :
  (l : Level) {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  (B : UU-Set l3) (f : A → type-Set B) (H : identifies-Eq-Rel R f) → UU _
is-set-quotient l R B f H =
  (X : UU-Set l) →
  is-equiv (precomp-Set-Quotient R B f H X)

universal-property-set-quotient :
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU-Set l3)
  (f : A → type-Set B) (H : identifies-Eq-Rel R f) →
  ({l : Level} → is-set-quotient l R B f H) → {l : Level} (X : UU-Set l)
  (g : A → type-Set X) (G : identifies-Eq-Rel R g) →
  is-contr
    ( fib (precomp-Set-Quotient R B f H X) (pair g G))
universal-property-set-quotient R B f H Q X g G =
  is-contr-map-is-equiv (Q X) (pair g G)

-- Remark 18.2.2

-- Theorem 18.2.3

-- Theorem 18.2.3 Condition (ii)

is-surjective-and-effective :
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) {B : UU l3}
  (f : A → B) → UU (l1 ⊔ l2 ⊔ l3)
is-surjective-and-effective {A = A} R f =
  is-surjective f × is-effective R f

module _
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU-Set l3)
  (q : A → type-Set B)
  where

  -- Theorem 18.2.3 (iii) implies (ii)
  
  is-effective-is-image :
    (i : type-Set B ↪ (A → UU-Prop l2)) →
    (T : (prop-Eq-Rel R) ~ ((map-emb i) ∘ q)) →
    ({l : Level} → universal-property-image l (prop-Eq-Rel R) i (pair q T)) →
    is-effective R q
  is-effective-is-image i T H x y =
    ( is-effective-map-set-quotient R x y) ∘e
    ( ( inv-equiv (equiv-ap-emb (emb-im (prop-Eq-Rel R)))) ∘e
      ( ( inv-equiv (convert-eq-values-htpy T x y)) ∘e
        ( equiv-ap-emb i)))

  is-surjective-and-effective-is-image :
    (i : type-Set B ↪ (A → UU-Prop l2)) → 
    (T : (prop-Eq-Rel R) ~ ((map-emb i) ∘ q)) →
    ({l : Level} → universal-property-image l (prop-Eq-Rel R) i (pair q T)) →
    is-surjective-and-effective R q
  is-surjective-and-effective-is-image i T H =
    pair
      ( is-surjective-universal-property-image (prop-Eq-Rel R) i (pair q T) H)
      ( is-effective-is-image i T H)

  -- Theorem 18.2.3 (ii) implies (iii)

  is-locally-small-is-surjective-and-effective :
    is-surjective-and-effective R q → is-locally-small l2 (type-Set B)
  is-locally-small-is-surjective-and-effective e x y =
    apply-universal-property-trunc-Prop
      ( pr1 e x)
      ( is-small-Prop l2 (Id x y))
      ( λ u →
        apply-universal-property-trunc-Prop
          ( pr1 e y)
          ( is-small-Prop l2 (Id x y))
          ( α u))
    where
    α : fib q x → fib q y → is-small l2 (Id x y)
    α (pair a refl) (pair b refl) =
      pair (type-Eq-Rel R a b) (pr2 e a b)

  large-map-emb-is-surjective-and-effective :
    is-surjective-and-effective R q → type-Set B → A → UU-Prop l3
  large-map-emb-is-surjective-and-effective H b a = Id-Prop B b (q a)

  small-map-emb-is-surjective-and-effective :
    is-surjective-and-effective R q → type-Set B → A →
    Σ (UU-Prop l3) (λ P → is-small l2 (type-Prop P))
  small-map-emb-is-surjective-and-effective H b a =
    pair ( large-map-emb-is-surjective-and-effective H b a)
         ( is-locally-small-is-surjective-and-effective H b (q a))

  abstract
    map-emb-is-surjective-and-effective :
      is-surjective-and-effective R q → type-Set B → A → UU-Prop l2
    map-emb-is-surjective-and-effective H b a =
      pair ( pr1 (pr2 (small-map-emb-is-surjective-and-effective H b a)))
           ( is-prop-equiv'
             ( type-Prop (large-map-emb-is-surjective-and-effective H b a))
             ( pr2 (pr2 (small-map-emb-is-surjective-and-effective H b a)))
             ( is-prop-type-Prop
               ( large-map-emb-is-surjective-and-effective H b a)))
  
    compute-map-emb-is-surjective-and-effective :
      (H : is-surjective-and-effective R q) (b : type-Set B) (a : A) →
      type-Prop (large-map-emb-is-surjective-and-effective H b a) ≃
      type-Prop (map-emb-is-surjective-and-effective H b a) 
    compute-map-emb-is-surjective-and-effective H b a =
      pr2 (pr2 (small-map-emb-is-surjective-and-effective H b a))
  
    triangle-emb-is-surjective-and-effective :
      (H : is-surjective-and-effective R q) →
      prop-Eq-Rel R ~ (map-emb-is-surjective-and-effective H ∘ q)
    triangle-emb-is-surjective-and-effective H a =
      eq-htpy
        ( λ x →
          eq-equiv-Prop
            ( ( compute-map-emb-is-surjective-and-effective H (q a) x) ∘e
              ( inv-equiv (pr2 H a x))))
  
    is-emb-map-emb-is-surjective-and-effective :
      (H : is-surjective-and-effective R q) →
      is-emb (map-emb-is-surjective-and-effective H)
    is-emb-map-emb-is-surjective-and-effective H =
      is-emb-is-injective
        ( is-set-function-type (is-set-UU-Prop l2))
        ( λ {x} {y} p →
          apply-universal-property-trunc-Prop
            ( pr1 H y)
            ( Id-Prop B x y)
            ( α p))
      where
      α : {x y : type-Set B}
          (p : Id ( map-emb-is-surjective-and-effective H x)
                  ( map-emb-is-surjective-and-effective H y)) →
          fib q y → type-Prop (Id-Prop B x y)
      α {x} p (pair a refl) =
        map-inv-equiv
          ( ( inv-equiv
              ( pr2
                ( is-locally-small-is-surjective-and-effective
                  H (q a) (q a)))) ∘e
            ( ( equiv-eq (ap pr1 (htpy-eq p a))) ∘e
              ( pr2
                ( is-locally-small-is-surjective-and-effective H x (q a)))))
          ( refl)

  emb-is-surjective-and-effective :
    (H : is-surjective-and-effective R q) →
    type-Set B ↪ (A → UU-Prop l2)
  emb-is-surjective-and-effective H =
    pair ( map-emb-is-surjective-and-effective H)
         ( is-emb-map-emb-is-surjective-and-effective H)

  abstract
    is-emb-large-map-emb-is-surjective-and-effective :
      (e : is-surjective-and-effective R q) →
      is-emb (large-map-emb-is-surjective-and-effective e)
    is-emb-large-map-emb-is-surjective-and-effective e =
      is-emb-is-injective
        ( is-set-function-type (is-set-UU-Prop l3))
        ( λ {x} {y} p →
          apply-universal-property-trunc-Prop
            ( pr1 e y)
            ( Id-Prop B x y)
            ( α p))
      where
      α : {x y : type-Set B}
          (p : Id ( large-map-emb-is-surjective-and-effective e x)
                  ( large-map-emb-is-surjective-and-effective e y)) →
          fib q y → type-Prop (Id-Prop B x y)
      α p (pair a refl) = map-inv-equiv (equiv-eq (ap pr1 (htpy-eq p a))) refl
  
  large-emb-is-surjective-and-effective :
    is-surjective-and-effective R q → type-Set B ↪ (A → UU-Prop l3)
  large-emb-is-surjective-and-effective e =
    pair ( large-map-emb-is-surjective-and-effective e)
         ( is-emb-large-map-emb-is-surjective-and-effective e)

  is-image-is-surjective-and-effective :
    (H : is-surjective-and-effective R q) →
    ( {l : Level} →
      universal-property-image l
        ( prop-Eq-Rel R)
        ( emb-is-surjective-and-effective H)
        ( pair q (triangle-emb-is-surjective-and-effective H)))
  is-image-is-surjective-and-effective H =
    universal-property-image-is-surjective
      ( prop-Eq-Rel R)
      ( emb-is-surjective-and-effective H)
      ( pair q (triangle-emb-is-surjective-and-effective H))
      ( pr1 H)

  -- Theorem 18.2.3 (i) implies (ii)

  is-surjective-is-set-quotient :
    (H : identifies-Eq-Rel R q) → ({l : Level} → is-set-quotient l R B q H) →
    is-surjective q
  is-surjective-is-set-quotient H Q b =
    tr ( λ y → type-trunc-Prop (fib q y))
       ( htpy-eq
         ( ap pr1
           ( eq-is-contr
             ( universal-property-set-quotient R B q H Q B q H)
             { pair ( inclusion-im q ∘ β)
                    ( eq-subtype (is-prop-identifies-Eq-Rel R B) (eq-htpy δ))}
             { pair id (eq-subtype (is-prop-identifies-Eq-Rel R B) refl)}))
         ( b))
       ( pr2 (β b))
    where
    α : identifies-Eq-Rel R (map-im q)
    α {x} {y} r =
      is-injective-is-emb
        ( is-emb-inclusion-im q)
        ( map-equiv (convert-eq-values-htpy (triangle-im q) x y) (H r))
    β : type-Set B → im q
    β = map-inv-is-equiv
          ( Q ( pair (im q) (is-set-im q (is-set-type-Set B))))
          ( pair (map-im q) α)
    γ : (β ∘ q) ~ map-im q
    γ = htpy-eq
          ( ap pr1
            ( issec-map-inv-is-equiv
              ( Q (pair (im q) (is-set-im q (is-set-type-Set B))))
              ( pair (map-im q) α)))
    δ : ((inclusion-im q ∘ β) ∘ q) ~ q
    δ = (inclusion-im q ·l γ) ∙h (triangle-im q)

  is-effective-is-set-quotient :
    (H : identifies-Eq-Rel R q) → ({l : Level} → is-set-quotient l R B q H) →
    is-effective R q
  is-effective-is-set-quotient H Q x y =
    inv-equiv (compute-P y) ∘e δ (q y)
    where
    α : Σ (A → UU-Prop l2) (identifies-Eq-Rel R)
    α = pair
          ( prop-Eq-Rel R x)
          ( λ r →
            eq-iff
              ( λ s → trans-Eq-Rel R s r)
              ( λ s → trans-Eq-Rel R s (symm-Eq-Rel R r)))
    P : type-Set B → UU-Prop l2
    P = map-inv-is-equiv (Q (UU-Prop-Set l2)) α
    compute-P : (a : A) → type-Eq-Rel R x a ≃ type-Prop (P (q a))
    compute-P a =
      equiv-eq
        ( ap pr1
          ( htpy-eq
            ( ap pr1
              ( inv (issec-map-inv-is-equiv (Q (UU-Prop-Set l2)) α)))
            ( a)))
    point-P : type-Prop (P (q x))
    point-P = map-equiv (compute-P x) (refl-Eq-Rel R)
    center-total-P : Σ (type-Set B) (λ b → type-Prop (P b))
    center-total-P = pair (q x) point-P
    contraction-total-P :
      (u : Σ (type-Set B) (λ b → type-Prop (P b))) → Id center-total-P u
    contraction-total-P (pair b p) =
      eq-subtype
        ( λ z → is-prop-type-Prop (P z))
        ( apply-universal-property-trunc-Prop
          ( is-surjective-is-set-quotient H Q b)
          ( Id-Prop B (q x) b)
          ( λ v →
            ( H ( map-inv-equiv
                  ( compute-P (pr1 v))
                  ( inv-tr (λ b → type-Prop (P b)) (pr2 v) p))) ∙
            ( pr2 v)))
    is-contr-total-P : is-contr (Σ (type-Set B) (λ b → type-Prop (P b)))
    is-contr-total-P = pair center-total-P contraction-total-P
    β : (b : type-Set B) → Id (q x) b → type-Prop (P b)
    β .(q x) refl = point-P
    γ : (b : type-Set B) → is-equiv (β b)
    γ = fundamental-theorem-id (q x) point-P is-contr-total-P β
    δ : (b : type-Set B) → Id (q x) b ≃ type-Prop (P b)
    δ b = pair (β b) (γ b)

  is-surjective-and-effective-is-set-quotient :
    (H : identifies-Eq-Rel R q) → ({l : Level} → is-set-quotient l R B q H) →
    is-surjective-and-effective R q
  is-surjective-and-effective-is-set-quotient H Q =
    pair (is-surjective-is-set-quotient H Q) (is-effective-is-set-quotient H Q)

  -- Theorem 18.2.3 (ii) implies (i)

  identifies-Eq-Rel-is-surjective-and-effective :
    is-surjective-and-effective R q → identifies-Eq-Rel R q
  identifies-Eq-Rel-is-surjective-and-effective E {x} {y} =
    map-inv-equiv (pr2 E x y)

  universal-property-set-quotient-is-surjective-and-effective :
    {l : Level} (E : is-surjective-and-effective R q) (X : UU-Set l) →
    is-contr-map
      ( precomp-Set-Quotient R B q
        ( identifies-Eq-Rel-is-surjective-and-effective E)
        ( X))
  universal-property-set-quotient-is-surjective-and-effective
    {l} E X (pair f H) =
    is-proof-irrelevant-is-prop
      ( is-prop-equiv
        ( fib (precomp q (type-Set X)) f)
        ( equiv-tot
          ( λ h → equiv-ap-pr1-is-subtype (is-prop-identifies-Eq-Rel R X)))
        ( is-prop-map-is-emb (is-emb-precomp-is-surjective (pr1 E) X) f))
      ( pair
        ( λ b → pr1 (α b))
        ( eq-subtype
          ( is-prop-identifies-Eq-Rel R X)
          ( eq-htpy (λ a → ap pr1 (β a)))))
    where
    P-Prop : (b : type-Set B) (x : type-Set X) → UU-Prop (l1 ⊔ l3 ⊔ l)
    P-Prop b x = ∃-Prop (λ a → (Id (f a) x) × (Id (q a) b))
    P : (b : type-Set B) (x : type-Set X) → UU (l1 ⊔ l3 ⊔ l)
    P b x = type-Prop (P-Prop b x)
    Q' : (b : type-Set B) → all-elements-equal (Σ (type-Set X) (P b))
    Q' b x y =
      eq-subtype
        ( λ x → is-prop-type-Prop (P-Prop b x))
        ( apply-universal-property-trunc-Prop
          ( pr2 x)
          ( Id-Prop X (pr1 x) (pr1 y))
          ( λ u →
            apply-universal-property-trunc-Prop
              ( pr2 y)
              ( Id-Prop X (pr1 x) (pr1 y))
              ( λ v →
                ( inv (pr1 (pr2 u))) ∙
                ( ( H ( map-equiv
                        ( pr2 E (pr1 u) (pr1 v))
                        ( (pr2 (pr2 u)) ∙ (inv (pr2 (pr2 v)))))) ∙
                  ( pr1 (pr2 v))))))
    Q : (b : type-Set B) → is-prop (Σ (type-Set X) (P b))
    Q b = is-prop-all-elements-equal (Q' b)
    α : (b : type-Set B) → Σ (type-Set X) (P b)
    α =
      map-inv-is-equiv
        ( dependent-universal-property-surj-is-surjective q
          ( pr1 E)
          ( λ b → pair (Σ (type-Set X) (P b)) (Q b)))
        ( λ a → pair (f a) (unit-trunc-Prop (pair a (pair refl refl))))
    β : (a : A) →
        Id (α (q a)) (pair (f a) (unit-trunc-Prop (pair a (pair refl refl))))
    β = htpy-eq
          ( issec-map-inv-is-equiv
            ( dependent-universal-property-surj-is-surjective q
              ( pr1 E)
              ( λ b → pair (Σ (type-Set X) (P b)) (Q b)))
            ( λ a → pair (f a) (unit-trunc-Prop (pair a (pair refl refl)))))

  is-set-quotient-is-surjective-and-effective :
    {l : Level} (E : is-surjective-and-effective R q) →
    is-set-quotient l R B q (identifies-Eq-Rel-is-surjective-and-effective E)
  is-set-quotient-is-surjective-and-effective E X =
    is-equiv-is-contr-map
      ( universal-property-set-quotient-is-surjective-and-effective E X)

--------------------------------------------------------------------------------

-- Section 18.4

--------------------------------------------------------------------------------

-- Section 18.5 Set truncations

-- Definition 18.5.1

is-set-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) →
  ( A → type-Set B) → UU (lsuc l ⊔ l1 ⊔ l2)
is-set-truncation l B f =
  (C : UU-Set l) → is-equiv (precomp-Set f C)

-- Bureaucracy

universal-property-set-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1}
  (B : UU-Set l2) (f : A → type-Set B) → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-set-truncation l {A = A} B f =
  (C : UU-Set l) (g : A → type-Set C) →
  is-contr (Σ (type-hom-Set B C) (λ h → (h ∘ f) ~  g))

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

compute-map-is-set-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  (is-settr-f : {l : Level} → is-set-truncation l B f) →
  (C : UU-Set l3) (g : A → type-Set C) →
  ((map-is-set-truncation B f is-settr-f C g) ∘ f) ~ g
compute-map-is-set-truncation B f is-settr-f C g =
  pr2
    ( center
      ( universal-property-is-set-truncation _ B f is-settr-f C g))

-- Theorem 18.5.2

-- Theorem 18.5.2 Condition (ii)

dependent-universal-property-set-truncation :
  {l1 l2 : Level} (l : Level) {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  UU (l1 ⊔ l2 ⊔ lsuc l)
dependent-universal-property-set-truncation l {A} B f =
  (X : type-Set B → UU-Set l) →
  is-equiv (λ (h : (b : type-Set B) → type-Set (X b)) (a : A) → h (f a))

-- Theorem 18.5.2 Condition (iii)

mere-eq-Eq-Rel : {l1 : Level} (A : UU l1) → Eq-Rel l1 A
mere-eq-Eq-Rel A =
  pair
    mere-eq-Prop
    ( pair refl-mere-eq (pair symm-mere-eq trans-mere-eq))

-- Theorem 18.5.2 (i) implies (ii)
  
dependent-universal-property-is-set-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  ({l : Level} → is-set-truncation l B f) →
  dependent-universal-property-set-truncation l3 B f
dependent-universal-property-is-set-truncation {A = A} B f H X =
  is-fiberwise-equiv-is-equiv-map-Σ
    ( λ (h : A → type-Set B) → (a : A) → type-Set (X (h a)))
    ( λ (g : type-Set B → type-Set B) → g ∘ f)
    ( λ g (s : (b : type-Set B) → type-Set (X (g b))) (a : A) → s (f a))
    ( H B)
    ( is-equiv-equiv
      ( equiv-inv-choice-∞ (λ x y → type-Set (X y)))
      ( equiv-inv-choice-∞ (λ x y → type-Set (X y)))
      ( ind-Σ (λ g s → refl))
      ( H (Σ-Set B X)))
    ( id)

-- Theorem 18.5.2 (ii) implies (i)

is-set-truncation-dependent-universal-property :
  {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  ({l : Level} → dependent-universal-property-set-truncation l B f) →
  is-set-truncation l3 B f
is-set-truncation-dependent-universal-property B f H X =
  H (λ b → X)

-- Theorem 18.5.2 (iii) implies (i)

identifies-mere-eq :
  {l1 l2 : Level} {A : UU l1} (X : UU-Set l2) (f : A → type-Set X) →
  identifies-Eq-Rel (mere-eq-Eq-Rel A) f
identifies-mere-eq X f {x} {y} r =
  apply-universal-property-trunc-Prop r
    ( Id-Prop X (f x) (f y))
    ( ap f)

is-set-truncation-is-set-quotient :
  {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  ( {l : Level} →
    is-set-quotient l (mere-eq-Eq-Rel A) B f (identifies-mere-eq B f)) →
  is-set-truncation l3 B f
is-set-truncation-is-set-quotient {A = A} B f H X =
  is-equiv-comp
    ( precomp-Set f X)
    ( pr1)
    ( precomp-Set-Quotient (mere-eq-Eq-Rel A) B f (identifies-mere-eq B f) X)
    ( refl-htpy)
    ( H X)
    ( is-equiv-pr1-is-contr
      ( λ h →
        is-proof-irrelevant-is-prop
          ( is-prop-identifies-Eq-Rel (mere-eq-Eq-Rel A) X h)
          ( identifies-mere-eq X h)))

is-set-quotient-is-set-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  ( {l : Level} → is-set-truncation l B f) →
  is-set-quotient l3 (mere-eq-Eq-Rel A) B f (identifies-mere-eq B f)
is-set-quotient-is-set-truncation {A = A} B f H X =
  is-equiv-right-factor
    ( precomp-Set f X)
    ( pr1)
    ( precomp-Set-Quotient (mere-eq-Eq-Rel A) B f (identifies-mere-eq B f) X)
    ( refl-htpy)
    ( is-equiv-pr1-is-contr
      ( λ h →
        is-proof-irrelevant-is-prop
          ( is-prop-identifies-Eq-Rel (mere-eq-Eq-Rel A) X h)
          ( identifies-mere-eq X h)))
    ( H X)
  
-- Definition 18.5.3

-- We postulate the existence of set truncations

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

precomp-Π-Set :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU-Set l3) →
  ((b : B) → type-Set (C b)) → ((a : A) → type-Set (C (f a)))
precomp-Π-Set f C h a = h (f a)

dependent-universal-property-trunc-Set :
  {l1 l2 : Level} {A : UU l1} (B : type-trunc-Set A → UU-Set l2) → 
  is-equiv (precomp-Π-Set unit-trunc-Set B)
dependent-universal-property-trunc-Set {A = A} =
  dependent-universal-property-is-set-truncation
    ( trunc-Set A)
    ( unit-trunc-Set)
    ( λ {l} → is-set-truncation-trunc-Set A)

equiv-dependent-universal-property-trunc-Set :
  {l1 l2 : Level} {A : UU l1} (B : type-trunc-Set A → UU-Set l2) →
  ((x : type-trunc-Set A) → type-Set (B x)) ≃
  ((a : A) → type-Set (B (unit-trunc-Set a)))
equiv-dependent-universal-property-trunc-Set B =
  pair ( precomp-Π-Set unit-trunc-Set B)
       ( dependent-universal-property-trunc-Set B)

-- Corollary 18.5.4

is-set-quotient-trunc-Set :
  {l1 l2 : Level} (A : UU l1) →
  is-set-quotient l2
    ( mere-eq-Eq-Rel A)
    ( trunc-Set A)
    ( unit-trunc-Set)
    ( identifies-mere-eq (trunc-Set A) unit-trunc-Set)
is-set-quotient-trunc-Set A =
  is-set-quotient-is-set-truncation
    ( trunc-Set A)
    ( unit-trunc-Set)
    ( λ {l} → is-set-truncation-trunc-Set A)

is-surjective-and-effective-unit-trunc-Set :
  {l1 : Level} (A : UU l1) →
  is-surjective-and-effective (mere-eq-Eq-Rel A) unit-trunc-Set
is-surjective-and-effective-unit-trunc-Set A =
  is-surjective-and-effective-is-set-quotient
    ( mere-eq-Eq-Rel A)
    ( trunc-Set A)
    ( unit-trunc-Set)
    ( identifies-mere-eq (trunc-Set A) unit-trunc-Set)
    ( λ {l} → is-set-quotient-trunc-Set A)

is-surjective-unit-trunc-Set :
  {l1 : Level} (A : UU l1) → is-surjective (unit-trunc-Set {A = A})
is-surjective-unit-trunc-Set A =
  pr1 (is-surjective-and-effective-unit-trunc-Set A)

is-effective-unit-trunc-Set :
  {l1 : Level} (A : UU l1) →
  is-effective (mere-eq-Eq-Rel A) (unit-trunc-Set {A = A})
is-effective-unit-trunc-Set A =
  pr2 (is-surjective-and-effective-unit-trunc-Set A)

emb-trunc-Set :
  {l1 : Level} (A : UU l1) → type-trunc-Set A ↪ (A → UU-Prop l1)
emb-trunc-Set A =
  emb-is-surjective-and-effective
    ( mere-eq-Eq-Rel A)
    ( trunc-Set A)
    ( unit-trunc-Set)
    ( is-surjective-and-effective-unit-trunc-Set A)

hom-slice-trunc-Set :
  {l1 : Level} (A : UU l1) →
  hom-slice (mere-eq-Prop {A = A}) (map-emb (emb-trunc-Set A))
hom-slice-trunc-Set A =
  pair
    ( unit-trunc-Set)
    ( triangle-emb-is-surjective-and-effective
      ( mere-eq-Eq-Rel A)
      ( trunc-Set A)
      ( unit-trunc-Set)
      ( is-surjective-and-effective-unit-trunc-Set A))

is-image-trunc-Set :
  {l1 l2 : Level} (A : UU l1) →
  universal-property-image l2
    ( mere-eq-Prop {A = A})
    ( emb-trunc-Set A)
    ( hom-slice-trunc-Set A)
is-image-trunc-Set A =
  is-image-is-surjective-and-effective
    ( mere-eq-Eq-Rel A)
    ( trunc-Set A)
    ( unit-trunc-Set)
    ( is-surjective-and-effective-unit-trunc-Set A)

-- Proposition 18.5.5

map-trunc-Set :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) →
  type-trunc-Set A → type-trunc-Set B
map-trunc-Set {A = A} {B} f x =
  apply-universal-property-trunc-Set x (trunc-Set B) (unit-trunc-Set ∘ f)

--------------------------------------------------------------------------------

module _
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where
    
  is-choice-of-representatives :
    (A → UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  is-choice-of-representatives P =
    (a : A) → is-contr (Σ A (λ x → P x × type-Eq-Rel R a x))
  
  representatives :
    {P : A → UU l3} → is-choice-of-representatives P → UU (l1 ⊔ l3)
  representatives {P} H = Σ A P
  
  map-set-quotient-representatives :
    {P : A → UU l3} (H : is-choice-of-representatives P) →
    representatives H → set-quotient R
  map-set-quotient-representatives H a = map-set-quotient R (pr1 a)
  
  is-surjective-map-set-quotient-representatives :
    {P : A → UU l3} (H : is-choice-of-representatives P) →
    is-surjective (map-set-quotient-representatives H)
  is-surjective-map-set-quotient-representatives H (pair Q K) =
    apply-universal-property-trunc-Prop K
      ( trunc-Prop (fib (map-set-quotient-representatives H) (pair Q K)))
      ( λ { (pair a refl) →
            unit-trunc-Prop
              ( pair
                ( pair (pr1 (center (H a))) (pr1 (pr2 (center (H a)))))
                ( ( map-inv-equiv
                    ( is-effective-map-set-quotient R (pr1 (center (H a))) a)
                    ( symm-Eq-Rel R (pr2 (pr2 (center (H a)))))) ∙
                  ( ap
                    ( pair (prop-Eq-Rel R a))
                    ( eq-is-prop is-prop-type-trunc-Prop))))})

  is-emb-map-set-quotient-representatives :
    {P : A → UU l3} (H : is-choice-of-representatives P) →
    is-emb (map-set-quotient-representatives H)
  is-emb-map-set-quotient-representatives {P} H (pair a p) =
    fundamental-theorem-id
      ( pair a p)
      ( refl)
      ( is-contr-equiv
        ( Σ A (λ x → P x × type-Eq-Rel R a x))
        ( ( assoc-Σ A P (λ z → type-Eq-Rel R a (pr1 z))) ∘e
          ( equiv-tot (λ t → is-effective-map-set-quotient R a (pr1 t))))
        ( H a))
      ( λ y → ap (map-set-quotient-representatives H) {pair a p} {y})

  is-equiv-map-set-quotient-representatives :
    {P : A → UU l3} (H : is-choice-of-representatives P) →
    is-equiv (map-set-quotient-representatives H)
  is-equiv-map-set-quotient-representatives H =
    is-equiv-is-emb-is-surjective
      ( is-surjective-map-set-quotient-representatives H)
      ( is-emb-map-set-quotient-representatives H)

  equiv-set-quotient-representatives :
    {P : A → UU l3} (H : is-choice-of-representatives P) →
    representatives H ≃ set-quotient R
  equiv-set-quotient-representatives H =
    pair ( map-set-quotient-representatives H)
         ( is-equiv-map-set-quotient-representatives H)

div-ℤ : ℤ → ℤ → UU lzero
div-ℤ d x = fib (mul-ℤ d) x

refl-div-ℤ : (x : ℤ) → div-ℤ x x
refl-div-ℤ x = pair one-ℤ (right-unit-law-mul-ℤ x)

trans-div-ℤ :
  (x y z : ℤ) → div-ℤ x y → div-ℤ y z → div-ℤ x z
trans-div-ℤ x y z (pair d p) (pair e q) =
  pair
    ( mul-ℤ d e)
    ( ( inv (associative-mul-ℤ x d e)) ∙
      ( ( ap (mul-ℤ' e) p) ∙
        ( q)))

div-one-ℤ : (x : ℤ) → div-ℤ one-ℤ x
div-one-ℤ x = pair x (left-unit-law-mul-ℤ x)

div-zero-ℤ : (x : ℤ) → div-ℤ x zero-ℤ
div-zero-ℤ x = pair zero-ℤ (right-zero-law-mul-ℤ x)

is-zero-div-zero-ℤ :
  (x : ℤ) → div-ℤ zero-ℤ x → is-zero-ℤ x
is-zero-div-zero-ℤ x (pair d p) = inv p

is-unit-ℤ : ℤ → UU lzero
is-unit-ℤ x = div-ℤ x one-ℤ

unit-ℤ : UU lzero
unit-ℤ = Σ ℤ is-unit-ℤ

div-is-unit-ℤ :
  (x y : ℤ) → is-unit-ℤ x → div-ℤ x y
div-is-unit-ℤ x y (pair d p) =
  pair
    ( mul-ℤ d y)
    ( inv (associative-mul-ℤ x d y) ∙ (ap (mul-ℤ' y) p ∙ left-unit-law-mul-ℤ y))

is-one-ℤ : ℤ → UU lzero
is-one-ℤ x = Id x one-ℤ

is-neg-one-ℤ : ℤ → UU lzero
is-neg-one-ℤ x = Id x neg-one-ℤ

is-one-or-neg-one-ℤ : ℤ → UU lzero
is-one-or-neg-one-ℤ x = coprod (is-one-ℤ x) (is-neg-one-ℤ x)

is-unit-one-ℤ : is-unit-ℤ one-ℤ
is-unit-one-ℤ = refl-div-ℤ one-ℤ

one-unit-ℤ : unit-ℤ
one-unit-ℤ = pair one-ℤ is-unit-one-ℤ

is-unit-is-one-ℤ :
  (x : ℤ) → is-one-ℤ x → is-unit-ℤ x
is-unit-is-one-ℤ .one-ℤ refl = is-unit-one-ℤ

is-unit-neg-one-ℤ : is-unit-ℤ neg-one-ℤ
is-unit-neg-one-ℤ = pair neg-one-ℤ refl

neg-one-unit-ℤ : unit-ℤ
neg-one-unit-ℤ = pair neg-one-ℤ is-unit-neg-one-ℤ

is-unit-is-neg-one-ℤ :
  (x : ℤ) → is-neg-one-ℤ x → is-unit-ℤ x
is-unit-is-neg-one-ℤ .neg-one-ℤ refl = is-unit-neg-one-ℤ

is-unit-is-one-or-neg-one-ℤ :
  (x : ℤ) → is-one-or-neg-one-ℤ x → is-unit-ℤ x
is-unit-is-one-or-neg-one-ℤ x (inl p) = is-unit-is-one-ℤ x p
is-unit-is-one-or-neg-one-ℤ x (inr p) = is-unit-is-neg-one-ℤ x p

is-one-or-neg-one-is-unit-ℤ :
  (x : ℤ) → is-unit-ℤ x → is-one-or-neg-one-ℤ x
is-one-or-neg-one-is-unit-ℤ (inl zero-ℕ) (pair d p) = inr refl
is-one-or-neg-one-is-unit-ℤ (inl (succ-ℕ x)) (pair (inl zero-ℕ) p) =
  ex-falso (Eq-eq-ℤ (inv (compute-mul-ℤ (inl (succ-ℕ x)) neg-one-ℤ) ∙ p))
is-one-or-neg-one-is-unit-ℤ (inl (succ-ℕ x)) (pair (inl (succ-ℕ d)) p) =
  ex-falso (Eq-eq-ℤ (inv (compute-mul-ℤ (inl (succ-ℕ x)) (inl (succ-ℕ d))) ∙ p))
is-one-or-neg-one-is-unit-ℤ (inl (succ-ℕ x)) (pair (inr (inl star)) p) =
  ex-falso (Eq-eq-ℤ (inv (compute-mul-ℤ (inl (succ-ℕ x)) zero-ℤ) ∙ p))
is-one-or-neg-one-is-unit-ℤ (inl (succ-ℕ x)) (pair (inr (inr zero-ℕ)) p) =
  ex-falso (Eq-eq-ℤ (inv (compute-mul-ℤ (inl (succ-ℕ x)) one-ℤ) ∙ p))
is-one-or-neg-one-is-unit-ℤ (inl (succ-ℕ x)) (pair (inr (inr (succ-ℕ d))) p) =
  ex-falso
    ( Eq-eq-ℤ (inv (compute-mul-ℤ (inl (succ-ℕ x)) (inr (inr (succ-ℕ d)))) ∙ p))
is-one-or-neg-one-is-unit-ℤ (inr (inl star)) (pair d p) =
  ex-falso (Eq-eq-ℤ p)
is-one-or-neg-one-is-unit-ℤ (inr (inr zero-ℕ)) (pair d p) = inl refl
is-one-or-neg-one-is-unit-ℤ (inr (inr (succ-ℕ x))) (pair (inl zero-ℕ) p) =
  ex-falso (Eq-eq-ℤ (inv (compute-mul-ℤ (inr (inr (succ-ℕ x))) neg-one-ℤ) ∙ p))
is-one-or-neg-one-is-unit-ℤ (inr (inr (succ-ℕ x))) (pair (inl (succ-ℕ d)) p) =
  ex-falso
    ( Eq-eq-ℤ (inv (compute-mul-ℤ (inr (inr (succ-ℕ x))) (inl (succ-ℕ d))) ∙ p))
is-one-or-neg-one-is-unit-ℤ (inr (inr (succ-ℕ x))) (pair (inr (inl star)) p) =
  ex-falso (Eq-eq-ℤ (inv (compute-mul-ℤ (inr (inr (succ-ℕ x))) zero-ℤ) ∙ p))
is-one-or-neg-one-is-unit-ℤ (inr (inr (succ-ℕ x))) (pair (inr (inr zero-ℕ)) p) =
  ex-falso (Eq-eq-ℤ (inv (compute-mul-ℤ (inr (inr (succ-ℕ x))) one-ℤ) ∙ p))
is-one-or-neg-one-is-unit-ℤ
  (inr (inr (succ-ℕ x))) (pair (inr (inr (succ-ℕ d))) p) =
  ex-falso
    ( Eq-eq-ℤ
      ( inv (compute-mul-ℤ (inr (inr (succ-ℕ x))) (inr (inr (succ-ℕ d)))) ∙ p))

sim-unit-ℤ : ℤ → ℤ → UU lzero
sim-unit-ℤ x y = Σ unit-ℤ (λ u → Id (mul-ℤ (pr1 u) x) y)

refl-sim-unit-ℤ : (x : ℤ) → sim-unit-ℤ x x
refl-sim-unit-ℤ x = pair one-unit-ℤ (left-unit-law-mul-ℤ x)

sim-unit-eq-ℤ : {x y : ℤ} → Id x y → sim-unit-ℤ x y
sim-unit-eq-ℤ {x} refl = refl-sim-unit-ℤ x

symm-sim-unit-ℤ : (x y : ℤ) → sim-unit-ℤ x y → sim-unit-ℤ y x
symm-sim-unit-ℤ x y (pair (pair u H) p) = f (is-one-or-neg-one-is-unit-ℤ u H)
  where
  f : is-one-or-neg-one-ℤ u → sim-unit-ℤ y x
  f (inl refl) = pair one-unit-ℤ (inv p)
  f (inr refl) =
    pair neg-one-unit-ℤ (inv (inv (neg-neg-ℤ x) ∙ ap (mul-ℤ neg-one-ℤ) p))

trans-sim-unit-ℤ :
  (x y z : ℤ) → sim-unit-ℤ x y → sim-unit-ℤ y z → sim-unit-ℤ x z
trans-sim-unit-ℤ x y z (pair (pair u H) p) (pair (pair v K) q) =
  f (is-one-or-neg-one-is-unit-ℤ u H) (is-one-or-neg-one-is-unit-ℤ v K)
  where
  f : is-one-or-neg-one-ℤ u → is-one-or-neg-one-ℤ v → sim-unit-ℤ x z
  f (inl refl) (inl refl) = pair one-unit-ℤ (p ∙ q)
  f (inl refl) (inr refl) = pair neg-one-unit-ℤ (ap neg-ℤ p ∙ q)
  f (inr refl) (inl refl) = pair neg-one-unit-ℤ (p ∙ q)
  f (inr refl) (inr refl) =
    pair one-unit-ℤ (inv (neg-neg-ℤ x) ∙ (ap neg-ℤ p ∙ q))

is-unit-mul-ℤ :
  (x y : ℤ) → is-unit-ℤ x → is-unit-ℤ y → is-unit-ℤ (mul-ℤ x y)
is-unit-mul-ℤ x y (pair d p) (pair e q) =
  pair
    ( mul-ℤ e d)
    ( ( associative-mul-ℤ x y (mul-ℤ e d)) ∙
      ( ( ap
          ( mul-ℤ x)
          ( ( inv (associative-mul-ℤ y e d)) ∙
            ( ( ap (mul-ℤ' d) q) ∙
              ( left-unit-law-mul-ℤ d)))) ∙
        ( p)))

mul-unit-ℤ : unit-ℤ → unit-ℤ → unit-ℤ
mul-unit-ℤ (pair x H) (pair y K) = pair (mul-ℤ x y) (is-unit-mul-ℤ x y H K)

is-unit-left-factor-ℤ :
  (x y : ℤ) → is-unit-ℤ (mul-ℤ x y) → is-unit-ℤ x
is-unit-left-factor-ℤ x y (pair d p) =
  pair (mul-ℤ y d) (inv (associative-mul-ℤ x y d) ∙ p)

is-unit-right-factor-ℤ :
  (x y : ℤ) → is-unit-ℤ (mul-ℤ x y) → is-unit-ℤ y
is-unit-right-factor-ℤ x y (pair d p) =
  is-unit-left-factor-ℤ y x (pair d (ap (mul-ℤ' d) (commutative-mul-ℤ y x) ∙ p))

is-decidable-is-zero-ℤ :
  (x : ℤ) → is-decidable (is-zero-ℤ x)
is-decidable-is-zero-ℤ x = has-decidable-equality-ℤ x zero-ℤ

antisymmetric-div-ℤ :
  (x y : ℤ) → div-ℤ x y → div-ℤ y x → sim-unit-ℤ x y
antisymmetric-div-ℤ x y (pair d p) (pair e q) =
  f (is-decidable-is-zero-ℤ x)
  where
  f : is-decidable (is-zero-ℤ x) → sim-unit-ℤ x y
  f (inl refl) = sim-unit-eq-ℤ p
  f (inr g) =
    pair
      ( pair d
        ( pair e
          ( is-injective-mul-ℤ x g
            { mul-ℤ d e}
            { one-ℤ}
            ( ( inv
                ( associative-mul-ℤ x d e)) ∙
              ( ( ap (mul-ℤ' e) p) ∙
                ( q ∙ inv (right-unit-law-mul-ℤ x)))))))
      ( commutative-mul-ℤ d x ∙ p)

is-common-divisor-ℤ : ℤ → ℤ → ℤ → UU lzero
is-common-divisor-ℤ d x y = (div-ℤ d x) × (div-ℤ d y)

is-gcd-ℤ : ℤ → ℤ → ℤ → UU lzero
is-gcd-ℤ x y d =
  is-nonnegative-ℤ d × ((k : ℤ) → is-common-divisor-ℤ k x y ↔ div-ℤ k d)
