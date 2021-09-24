{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module book.18-set-quotients where

open import book.17-univalence public

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

effective-quotient :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (x y : A) →
  Id (map-set-quotient R x) (map-set-quotient R y) ≃ type-Eq-Rel R x y
effective-quotient R x y =
  ( equiv-symm-Eq-Rel R y x) ∘e
  ( effective-quotient' R x (map-set-quotient R y))

--------------------------------------------------------------------------------

{- Section 18.2 The universal property of set quotients -}

-- Definition 18.2.1

identifies-Eq-Rel :
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  {B : UU l3} → (A → B) → UU (l1 ⊔ (l2 ⊔ l3))
identifies-Eq-Rel {A = A} R f =
  (x y : A) → type-Eq-Rel R x y → Id (f x) (f y)

precomp-map-universal-property-set-quotient :
  {l l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  {B : UU-Set l3} (f : A → type-Set B) (H : identifies-Eq-Rel R f) →
  (X : UU-Set l) → (type-hom-Set B X) → Σ (A → type-Set X) (identifies-Eq-Rel R)
precomp-map-universal-property-set-quotient R f H X g =
  pair (g ∘ f) (λ x y r → ap g (H x y r))

is-set-quotient :
  (l : Level) {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  {B : UU-Set l3} (f : A → type-Set B) (H : identifies-Eq-Rel R f) → UU _
is-set-quotient l R {B} f H =
  (X : UU-Set l) →
  is-equiv (precomp-map-universal-property-set-quotient R {B} f H X)

-- Remark 18.2.2

-- Theorem 18.2.3

-- Theorem 18.2.3 Condition (ii)

is-effective-Eq-Rel' :
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU-Set l3)
  (f : A → type-Set B) → UU (l1 ⊔ l2 ⊔ l3)
is-effective-Eq-Rel' {A = A} R B f =
  (x y : A) → (type-Eq-Rel R x y ≃ Id (f x) (f y))

is-effective-Eq-Rel :
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU-Set l3)
  (f : A → type-Set B) → UU (l1 ⊔ l2 ⊔ l3)
is-effective-Eq-Rel {A = A} R B f =
  is-surjective f × is-effective-Eq-Rel' R B f

module _
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU-Set l3)
  (q : A → type-Set B)
  where

  
  -- Theorem 18.2.3 (iii) implies (ii)
  
  is-effective-is-image' :
    (i : type-Set B ↪ (A → UU-Prop l2)) →
    (T : (prop-Eq-Rel R) ~ ((map-emb i) ∘ q)) →
    ({l : Level} → universal-property-image l (prop-Eq-Rel R) i (pair q T)) →
    is-effective-Eq-Rel' R B q
  is-effective-is-image' i T H x y =
    ( ( ( inv-equiv (equiv-ap-emb i)) ∘e
        ( convert-eq-values-htpy T x y)) ∘e
      ( equiv-ap-emb (emb-im (prop-Eq-Rel R)))) ∘e
    ( inv-equiv (effective-quotient R x y))

  is-effective-is-image :
    (i : type-Set B ↪ (A → UU-Prop l2)) → 
    (T : (prop-Eq-Rel R) ~ ((map-emb i) ∘ q)) →
    ({l : Level} → universal-property-image l (prop-Eq-Rel R) i (pair q T)) →
    is-effective-Eq-Rel R B q
  is-effective-is-image i T H =
    pair
      ( is-surjective-universal-property-image (prop-Eq-Rel R) i (pair q T) H)
      ( is-effective-is-image' i T H)

  -- Theorem 18.2.3 (ii) implies (iii)

  map-emb-is-effective :
    is-effective-Eq-Rel R B q → type-Set B → A → UU-Prop l3
  map-emb-is-effective H b a = Id-Prop B b (q a)

  is-emb-map-emb-is-effective :
    (e : is-effective-Eq-Rel R B q) → is-emb (map-emb-is-effective e)
  is-emb-map-emb-is-effective e =
    is-emb-is-injective
      ( is-set-function-type (is-set-UU-Prop l3))
      ( λ {x} {y} p →
        apply-universal-property-trunc-Prop
          ( pr1 e y)
          ( Id-Prop B x y)
          ( α p))
    where
    α : {x y : type-Set B}
        (p : Id (map-emb-is-effective e x) (map-emb-is-effective e y)) →
        fib q y → type-Prop (Id-Prop B x y)
    α p (pair a refl) = map-inv-equiv (equiv-eq (ap pr1 (htpy-eq p a))) refl

--------------------------------------------------------------------------------

-- Section 18.5 Resizing axioms

-- Definition 18.5.1

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

-- Example 18.5.2

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

-- Example 18.5.2 (i)

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

-- Example 18.5.2 (ii)

is-small-is-contr :
  (l : Level) {l1 : Level} {A : UU l1} → is-contr A → is-small l A
is-small-is-contr l H =
  pair (raise-unit l) (equiv-is-contr H is-contr-raise-unit)

is-small-is-prop :
  (l : Level) {l1 : Level} {A : UU l1} → is-prop A → is-locally-small l A
is-small-is-prop l H x y = is-small-is-contr l (H x y)

-- Example 18.5.2 (iii)

is-locally-small-UU :
  {l : Level} → is-locally-small l (UU l)
is-locally-small-UU X Y = pair (X ≃ Y) equiv-univalence

-- Example 18.5.2 (iv)

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

-- Example 18.5.2 (v)

UU-is-small : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
UU-is-small l1 l2 = Σ (UU l2) (is-small l1)

equiv-UU-is-small :
  (l1 l2 : Level) → UU-is-small l1 l2 ≃ UU-is-small l2 l1
equiv-UU-is-small l1 l2 =
  ( equiv-tot (λ X → equiv-tot (λ Y → equiv-inv-equiv))) ∘e
  ( equiv-Σ-swap (UU l2) (UU l1) _≃_)

-- Example 18.5.2 (vi)

is-small-decidable-Prop :
  (l1 l2 : Level) → is-small l2 (decidable-Prop l1)
is-small-decidable-Prop l1 l2 =
  pair ( raise-Fin l2 two-ℕ)
       ( equiv-raise l2 (Fin two-ℕ) ∘e equiv-Fin-two-ℕ-decidable-Prop)

-- Proposition 18.5.3

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

-- Corollary 18.5.4

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

-- Corollary 18.5.5

is-small-mere-equiv :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} → mere-equiv A B →
  is-small l B → is-small l A
is-small-mere-equiv l e H =
  apply-universal-property-trunc-Prop e
    ( is-small-Prop l _)
    ( λ e' → is-small-equiv l _ e' H)

--------------------------------------------------------------------------------

-- Section 18.4

--------------------------------------------------------------------------------

{- Set truncations -}

is-set-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) →
  ( A → type-Set B) → UU (lsuc l ⊔ l1 ⊔ l2)
is-set-truncation l B f =
  (C : UU-Set l) → is-equiv (precomp-Set f C)

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

map-trunc-Set :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) →
  type-trunc-Set A → type-trunc-Set B
map-trunc-Set {A = A} {B} f x =
  apply-universal-property-trunc-Set x (trunc-Set B) (unit-trunc-Set ∘ f)

id-map-trunc-Set :
  {l1 : Level} (A : UU l1) → map-trunc-Set (id {A = A}) ~ id
id-map-trunc-Set A x =
  {!dependent-universal-property-trunc-Set!}

is-equiv-map-trunc-Set :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} → is-equiv f →
  is-equiv (map-trunc-Set f)
is-equiv-map-trunc-Set {A = A} {B} {f} H =
  is-equiv-has-inverse
    {! !}
    {!!}
    {!!}
