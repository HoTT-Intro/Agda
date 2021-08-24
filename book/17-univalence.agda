{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module book.17-univalence where

open import book.16-finite-types public

--------------------------------------------------------------------------------

-- Section 17 The univalence axiom

--------------------------------------------------------------------------------

-- Section 17.1 Equivalent forms of the univalence axiom

-- Definition 17.1.1

equiv-eq : {i : Level} {A : UU i} {B : UU i} → Id A B → A ≃ B
equiv-eq refl = equiv-id

UNIVALENCE : {i : Level} (A B : UU i) → UU (lsuc i)
UNIVALENCE A B = is-equiv (equiv-eq {A = A} {B = B})

-- Theorem 17.1.2

is-contr-total-equiv-UNIVALENCE : {i : Level} (A : UU i) →
  ((B : UU i) → UNIVALENCE A B) → is-contr (Σ (UU i) (λ X → A ≃ X))
is-contr-total-equiv-UNIVALENCE A UA =
  fundamental-theorem-id' A equiv-id (λ B → equiv-eq) UA

UNIVALENCE-is-contr-total-equiv : {i : Level} (A : UU i) →
  is-contr (Σ (UU i) (λ X → A ≃ X)) → (B : UU i) → UNIVALENCE A B
UNIVALENCE-is-contr-total-equiv A c =
  fundamental-theorem-id A equiv-id c (λ B → equiv-eq)

ev-id : {i j : Level} {A : UU i} (P : (B : UU i) → (A ≃ B) → UU j) →
  ((B : UU i) (e : A ≃ B) → P B e) → P A equiv-id
ev-id {A = A} P f = f A equiv-id

IND-EQUIV : {i j : Level} {A : UU i} → ((B : UU i) (e : A ≃ B) → UU j) → UU _
IND-EQUIV P = sec (ev-id P)

triangle-ev-id : {i j : Level} {A : UU i}
  (P : (Σ (UU i) (λ X → A ≃ X)) → UU j) →
  (ev-pt (pair A equiv-id) P)
  ~ ((ev-id (λ X e → P (pair X e))) ∘ (ev-pair {A = UU i} {B = λ X → A ≃ X} {C = P}))
triangle-ev-id P f = refl

abstract
  IND-EQUIV-is-contr-total-equiv : {i j : Level} (A : UU i) →
    is-contr (Σ (UU i) (λ X → A ≃ X)) →
    (P : (Σ (UU i) (λ X → A ≃ X)) → UU j) → IND-EQUIV (λ B e → P (pair B e))
  IND-EQUIV-is-contr-total-equiv {i} {j} A c P =
    section-comp
      ( ev-pt (pair A equiv-id) P)
      ( ev-id (λ X e → P (pair X e)))
      ( ev-pair)
      ( triangle-ev-id P)
      ( pair ind-Σ refl-htpy)
      ( is-singleton-is-contr
        ( pair A equiv-id)
        ( pair
          ( pair A equiv-id)
          ( λ t →  ( inv (contraction c (pair A equiv-id))) ∙
                   ( contraction c t)))
        ( P))

abstract
  is-contr-total-equiv-IND-EQUIV : {i : Level} (A : UU i) →
    ( {j : Level} (P : (Σ (UU i) (λ X → A ≃ X)) → UU j) →
      IND-EQUIV (λ B e → P (pair B e))) →
    is-contr (Σ (UU i) (λ X → A ≃ X))
  is-contr-total-equiv-IND-EQUIV {i} A ind =
    is-contr-is-singleton
      ( Σ (UU i) (λ X → A ≃ X))
      ( pair A equiv-id)
      ( λ P → section-comp'
        ( ev-pt (pair A equiv-id) P)
        ( ev-id (λ X e → P (pair X e)))
        ( ev-pair {A = UU i} {B = λ X → A ≃ X} {C = P})
        ( triangle-ev-id P)
        ( pair ind-Σ refl-htpy)
        ( ind P))

-- The univalence axiom

postulate univalence : {i : Level} (A B : UU i) → UNIVALENCE A B

eq-equiv : {i : Level} (A B : UU i) → (A ≃ B) → Id A B
eq-equiv A B = map-inv-is-equiv (univalence A B)

equiv-univalence :
  {i : Level} {A B : UU i} → Id A B ≃ (A ≃ B)
equiv-univalence = pair equiv-eq (univalence _ _)

abstract
  is-contr-total-equiv : {i : Level} (A : UU i) →
    is-contr (Σ (UU i) (λ X → A ≃ X))
  is-contr-total-equiv A = is-contr-total-equiv-UNIVALENCE A (univalence A)

is-contr-total-equiv' : {i : Level} (A : UU i) →
  is-contr (Σ (UU i) (λ X → X ≃ A))
is-contr-total-equiv' A =
  is-contr-equiv
    ( Σ (UU _) (λ X → A ≃ X))
    ( equiv-tot (λ X → equiv-inv-equiv))
    ( is-contr-total-equiv A)

abstract
  Ind-equiv : {i j : Level} (A : UU i) (P : (B : UU i) (e : A ≃ B) → UU j) →
    sec (ev-id P)
  Ind-equiv A P =
    IND-EQUIV-is-contr-total-equiv A
    ( is-contr-total-equiv A)
    ( λ t → P (pr1 t) (pr2 t))

ind-equiv : {i j : Level} (A : UU i) (P : (B : UU i) (e : A ≃ B) → UU j) →
  P A equiv-id → {B : UU i} (e : A ≃ B) → P B e
ind-equiv A P p {B} = pr1 (Ind-equiv A P) p B

--------------------------------------------------------------------------------

-- Section 17.2 Univalence implies function extensionality

-- Lemma 17.2.1

is-equiv-postcomp-univalence :
  {l1 l2 : Level} {X Y : UU l1} (A : UU l2) (e : X ≃ Y) →
  is-equiv (postcomp A (map-equiv e))
is-equiv-postcomp-univalence {X = X} A =
  ind-equiv X (λ Y e → is-equiv (postcomp A (map-equiv e))) is-equiv-id

-- Theorem 17.2.2

weak-funext-univalence :
  {l : Level} {A : UU l} {B : A → UU l} → WEAK-FUNEXT A B
weak-funext-univalence {A = A} {B} is-contr-B =
  is-contr-retract-of
    ( fib (postcomp A (pr1 {B = B})) id)
    ( pair
      ( λ f → pair (λ x → pair x (f x)) refl)
      ( pair
        ( λ h x → tr B (htpy-eq (pr2 h) x) (pr2 (pr1 h x)))
        ( refl-htpy)))
    ( is-contr-map-is-equiv
      ( is-equiv-postcomp-univalence A (equiv-pr1 is-contr-B))
      ( id))

funext-univalence :
  {l : Level} {A : UU l} {B : A → UU l} (f : (x : A) → B x) → FUNEXT f
funext-univalence {A = A} {B} f =
  FUNEXT-WEAK-FUNEXT (λ A B → weak-funext-univalence) A B f

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------

-- Subuniverses

is-subuniverse :
  {l1 l2 : Level} (P : UU l1 → UU l2) → UU ((lsuc l1) ⊔ l2)
is-subuniverse P = is-subtype P

subuniverse :
  (l1 l2 : Level) → UU ((lsuc l1) ⊔ (lsuc l2))
subuniverse l1 l2 = Σ (UU l1 → UU l2) is-subuniverse

{- By univalence, subuniverses are closed under equivalences. -}
in-subuniverse-equiv :
  {l1 l2 : Level} (P : UU l1 → UU l2) {X Y : UU l1} → X ≃ Y → P X → P Y
in-subuniverse-equiv P e = tr P (eq-equiv _ _ e)

in-subuniverse-equiv' :
  {l1 l2 : Level} (P : UU l1 → UU l2) {X Y : UU l1} → X ≃ Y → P Y → P X
in-subuniverse-equiv' P e = tr P (inv (eq-equiv _ _ e))

total-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) → UU ((lsuc l1) ⊔ l2)
total-subuniverse {l1} P = Σ (UU l1) (pr1 P)

{- We also introduce the notion of 'global subuniverse'. The handling of 
   universe levels is a bit more complicated here, since (l : Level) → A l are 
   kinds but not types. -}
   
is-global-subuniverse :
  (α : Level → Level) (P : (l : Level) → subuniverse l (α l)) →
  (l1 l2 : Level) → UU _
is-global-subuniverse α P l1 l2 =
  (X : UU l1) (Y : UU l2) → X ≃ Y → (pr1 (P l1)) X → (pr1 (P l2)) Y

{- Next we characterize the identity type of a subuniverse. -}

Eq-total-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  (s t : total-subuniverse P) → UU l1
Eq-total-subuniverse (pair P H) (pair X p) t = X ≃ (pr1 t)

Eq-total-subuniverse-eq :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  (s t : total-subuniverse P) → Id s t → Eq-total-subuniverse P s t
Eq-total-subuniverse-eq (pair P H) (pair X p) .(pair X p) refl = equiv-id

abstract
  is-contr-total-Eq-total-subuniverse :
    {l1 l2 : Level} (P : subuniverse l1 l2)
    (s : total-subuniverse P) →
    is-contr (Σ (total-subuniverse P) (λ t → Eq-total-subuniverse P s t))
  is-contr-total-Eq-total-subuniverse (pair P H) (pair X p) =
    is-contr-total-Eq-substructure (is-contr-total-equiv X) H X equiv-id p

abstract
  is-equiv-Eq-total-subuniverse-eq :
    {l1 l2 : Level} (P : subuniverse l1 l2)
    (s t : total-subuniverse P) → is-equiv (Eq-total-subuniverse-eq P s t)
  is-equiv-Eq-total-subuniverse-eq (pair P H) (pair X p) =
    fundamental-theorem-id
      ( pair X p)
      ( equiv-id)
      ( is-contr-total-Eq-total-subuniverse (pair P H) (pair X p))
      ( Eq-total-subuniverse-eq (pair P H) (pair X p))

eq-Eq-total-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  {s t : total-subuniverse P} → Eq-total-subuniverse P s t → Id s t
eq-Eq-total-subuniverse P {s} {t} =
  map-inv-is-equiv (is-equiv-Eq-total-subuniverse-eq P s t)
    

-- Classical logic in univalent type theory

{- Recall that a proposition P is decidable if P + (¬ P) holds. -}

classical-Prop :
  (l : Level) → UU (lsuc l)
classical-Prop l = Σ (UU-Prop l) (λ P → is-decidable (pr1 P))

{- Not every type is decidable. -}

case-elim :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  ¬ B → coprod A B → A
case-elim nb (inl a) = a
case-elim nb (inr b) = ex-falso (nb b)

simplify-not-all-2-element-types-decidable :
  {l : Level} →
  ((X : UU l) (p : type-trunc-Prop (bool ≃ X)) → is-decidable X) →
  ((X : UU l) (p : type-trunc-Prop (bool ≃ X)) → X)
simplify-not-all-2-element-types-decidable d X p =
  case-elim
    ( apply-universal-property-trunc-Prop p
      ( dn-Prop' X)
      ( λ e → intro-dn (map-equiv e true)))
    ( d X p)

{-
not-all-2-element-types-decidable :
  {l : Level} → ¬ ((X : UU l) (p : type-trunc-Prop (bool ≃ X)) → is-decidable X)
not-all-2-element-types-decidable d = {!simplify-not-all-2-element-types-decidable d (raise _ bool) ?!}

not-all-types-decidable :
  {l : Level} → ¬ ((X : UU l) → is-decidable X)
not-all-types-decidable d =
  not-all-2-element-types-decidable (λ X p → d X)
-}

{- Decidable equality of Fin n. -}

has-decidable-equality-empty : has-decidable-equality empty
has-decidable-equality-empty ()

has-decidable-equality-unit :
  has-decidable-equality unit
has-decidable-equality-unit star star = inl refl

decidable-Eq-Fin :
  (n : ℕ) (i j : Fin n) → classical-Prop lzero
decidable-Eq-Fin n i j =
  pair
    ( pair (Id i j) (is-set-Fin n i j))
    ( has-decidable-equality-Fin i j)

{- Decidable equality of ℤ. -}

has-decidable-equality-ℤ : has-decidable-equality ℤ
has-decidable-equality-ℤ =
  has-decidable-equality-coprod
    has-decidable-equality-ℕ
    ( has-decidable-equality-coprod
      has-decidable-equality-unit
      has-decidable-equality-ℕ)

{- Closure of decidable types under retracts and equivalences. -}

has-decidable-equality-retract-of :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  A retract-of B → has-decidable-equality B → has-decidable-equality A
has-decidable-equality-retract-of (pair i (pair r H)) d x y =
  is-decidable-retract-of
    ( Id-retract-of-Id (pair i (pair r H)) x y)
    ( d (i x) (i y))

-- Exercises

-- Exercise 17.1

tr-equiv-eq-ap : {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {x y : A}
  (p : Id x y) → (map-equiv (equiv-eq (ap B p))) ~ tr B p
tr-equiv-eq-ap refl = refl-htpy

-- Exercise 17.2

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

-- Closure properties of small types

is-small-equiv :
  (l : Level) {l1 l2 : Level} {A : UU l1} (B : UU l2) →
  A ≃ B → is-small l B → is-small l A
is-small-equiv l B e (pair X h) = pair X (h ∘e e)

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

--

total-subtype :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) → UU (l1 ⊔ l2)
total-subtype {A = A} P = Σ A (λ x → pr1 (P x))

equiv-subtype-equiv :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} (e : A ≃ B)
  (C : A → UU-Prop l3) (D : B → UU-Prop l4) →
  ((x : A) → (C x) ⇔ (D (map-equiv e x))) →
  total-subtype C ≃ total-subtype D
equiv-subtype-equiv e C D H =
  equiv-Σ (λ y → type-Prop (D y)) e
    ( λ x → equiv-iff (C x) (D (map-equiv e x)) (H x))

equiv-comp-equiv' :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → (C : UU l3) → (B ≃ C) ≃ (A ≃ C)
equiv-comp-equiv' e C =
  equiv-subtype-equiv
    ( equiv-precomp-equiv e C)
    ( is-equiv-Prop)
    ( is-equiv-Prop)
    ( λ g →
      pair
        ( is-equiv-comp' g (map-equiv e) (is-equiv-map-equiv e))
        ( λ is-equiv-eg →
          is-equiv-left-factor'
            g (map-equiv e) is-equiv-eg (is-equiv-map-equiv e)))

{-
equiv-comp-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → (C : UU l3) → (C ≃ A) ≃ (C ≃ B)
equiv-comp-equiv e C =
  equiv-subtype-equiv
    ( equiv-postcomp C e)
    ( is-equiv-Prop)
    ( is-equiv-Prop)
    ( λ g →
      pair
        ( λ H → is-equiv-comp' (map-equiv e) g H (is-equiv-map-equiv e))
        ( λ H →
          is-equiv-right-factor' (map-equiv e) g (is-equiv-map-equiv e) H))
-}

is-prop-is-small :
  (l : Level) {l1 : Level} (A : UU l1) → is-prop (is-small l A)
is-prop-is-small l A =
  is-prop-is-proof-irrelevant
    ( λ Xe →
      is-contr-equiv'
        ( Σ (UU l) (λ Y → (pr1 Xe) ≃ Y))
        ( equiv-tot ((λ Y → equiv-comp-equiv' (pr2 Xe) Y)))
        ( is-contr-total-equiv (pr1 Xe)))

is-prop-is-locally-small :
  (l : Level) {l1 : Level} (A : UU l1) → is-prop (is-locally-small l A)
is-prop-is-locally-small l A =
  is-prop-Π (λ x → is-prop-Π (λ y → is-prop-is-small l (Id x y)))

{-
is-emb-raise :
  (l1 l2 : Level) → is-emb (raise l2 {l1})
is-emb-raise l1 l2 =
  is-emb-is-prop-map (λ X → is-prop-equiv (is-small l1 X) (equiv-tot (λ Y → (equiv-inv-equiv ∘e {!equiv-precomp-equiv (equiv-raise l2 Y) X!}) ∘e equiv-univalence)) {!!})
-}
-- Exercise 17.3

subuniverse-is-contr :
  {i : Level} → subuniverse i i
subuniverse-is-contr {i} = pair is-contr is-subtype-is-contr

unit' :
  (i : Level) → UU i
unit' i = pr1 (Raise i unit)

abstract
  is-contr-unit' :
    (i : Level) → is-contr (unit' i)
  is-contr-unit' i =
    is-contr-equiv' unit (pr2 (Raise i unit)) is-contr-unit

abstract
  center-UU-contr :
    (i : Level) → total-subuniverse (subuniverse-is-contr {i})
  center-UU-contr i =
    pair (unit' i) (is-contr-unit' i)
  
  contraction-UU-contr :
    {i : Level} (A : Σ (UU i) is-contr) →
    Id (center-UU-contr i) A
  contraction-UU-contr (pair A is-contr-A) =
    eq-Eq-total-subuniverse subuniverse-is-contr
      ( equiv-is-contr (is-contr-unit' _) is-contr-A)

abstract
  is-contr-UU-contr : (i : Level) → is-contr (Σ (UU i) is-contr)
  is-contr-UU-contr i =
    pair (center-UU-contr i) (contraction-UU-contr)

is-trunc-UU-trunc :
  (k : 𝕋) (i : Level) → is-trunc (succ-𝕋 k) (Σ (UU i) (is-trunc k))
is-trunc-UU-trunc k i X Y =
  is-trunc-is-equiv k
    ( Id (pr1 X) (pr1 Y))
    ( ap pr1)
    ( is-emb-pr1-is-subtype
      ( is-prop-is-trunc k) X Y)
    ( is-trunc-is-equiv k
      ( (pr1 X) ≃ (pr1 Y))
      ( equiv-eq)
      ( univalence (pr1 X) (pr1 Y))
      ( is-trunc-equiv-is-trunc k (pr2 X) (pr2 Y)))

is-set-UU-Prop :
  (l : Level) → is-set (UU-Prop l)
is-set-UU-Prop l = is-trunc-UU-trunc (neg-one-𝕋) l

ev-true-false :
  {l : Level} (A : UU l) → (f : bool → A) → A × A
ev-true-false A f = pair (f true) (f false)

map-universal-property-bool :
  {l : Level} {A : UU l} →
  A × A → (bool → A)
map-universal-property-bool (pair x y) true = x
map-universal-property-bool (pair x y) false = y

issec-map-universal-property-bool :
  {l : Level} {A : UU l} →
  ((ev-true-false A) ∘ map-universal-property-bool) ~ id
issec-map-universal-property-bool (pair x y) =
  eq-pair refl refl

isretr-map-universal-property-bool' :
  {l : Level} {A : UU l} (f : bool → A) →
  (map-universal-property-bool (ev-true-false A f)) ~ f
isretr-map-universal-property-bool' f true = refl
isretr-map-universal-property-bool' f false = refl

isretr-map-universal-property-bool :
  {l : Level} {A : UU l} →
  (map-universal-property-bool ∘ (ev-true-false A)) ~ id
isretr-map-universal-property-bool f =
  eq-htpy (isretr-map-universal-property-bool' f)

universal-property-bool :
  {l : Level} (A : UU l) →
  is-equiv (λ (f : bool → A) → pair (f true) (f false))
universal-property-bool A =
  is-equiv-has-inverse
    map-universal-property-bool
    issec-map-universal-property-bool
    isretr-map-universal-property-bool

ev-true :
  {l : Level} {A : UU l} → (bool → A) → A
ev-true f = f true

triangle-ev-true :
  {l : Level} (A : UU l) →
  (ev-true) ~ (pr1 ∘ (ev-true-false A))
triangle-ev-true A = refl-htpy

aut-bool-bool :
  bool → (bool ≃ bool)
aut-bool-bool true = equiv-id
aut-bool-bool false = equiv-neg-𝟚

bool-aut-bool :
  (bool ≃ bool) → bool
bool-aut-bool e = map-equiv e true

decide-true-false :
  (b : bool) → coprod (Id b true) (Id b false)
decide-true-false true = inl refl
decide-true-false false = inr refl

eq-false :
  (b : bool) → (¬ (Id b true)) → (Id b false)
eq-false true p = ind-empty (p refl)
eq-false false p = refl

eq-true :
  (b : bool) → (¬ (Id b false)) → Id b true
eq-true true p = refl
eq-true false p = ind-empty (p refl)

Eq-𝟚-eq : (x y : bool) → Id x y → Eq-𝟚 x y
Eq-𝟚-eq x .x refl = reflexive-Eq-𝟚 x

eq-false-equiv' :
  (e : bool ≃ bool) → Id (map-equiv e true) true →
  is-decidable (Id (map-equiv e false) false) → Id (map-equiv e false) false
eq-false-equiv' e p (inl q) = q
eq-false-equiv' e p (inr x) =
  ind-empty
    ( Eq-𝟚-eq true false
      ( ap pr1
        ( eq-is-contr'
          ( is-contr-map-is-equiv (is-equiv-map-equiv e) true)
          ( pair true p)
          ( pair false (eq-true (map-equiv e false) x)))))

-- Exercise 14.11

square-htpy-eq :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B) →
  ( g h : B → C) →
  ( (λ (p : (y : B) → Id (g y) (h y)) (x : A) → p (f x)) ∘ htpy-eq) ~
  ( htpy-eq ∘ (ap (precomp f C)))
square-htpy-eq f g .g refl = refl

is-emb-precomp-is-surjective :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-surjective f → (C : UU-Set l3) → is-emb (precomp f (type-Set C))
is-emb-precomp-is-surjective {f = f} is-surj-f C g h =
  is-equiv-top-is-equiv-bottom-square
    ( htpy-eq)
    ( htpy-eq)
    ( ap (precomp f (type-Set C)))
    ( λ p a → p (f a))
    ( square-htpy-eq f g h)
    ( funext g h)
    ( funext (g ∘ f) (h ∘ f))
    ( dependent-universal-property-surj-is-surjective f is-surj-f
      ( λ a → Id-Prop C (g a) (h a)))

{-
eq-false-equiv :
  (e : bool ≃ bool) → Id (map-equiv e true) true → Id (map-equiv e false) false
eq-false-equiv e p =
  eq-false-equiv' e p (has-decidable-equality-𝟚 (map-equiv e false) false)
-}

{-
eq-true-equiv :
  (e : bool ≃ bool) →
  ¬ (Id (map-equiv e true) true) → Id (map-equiv e false) true
eq-true-equiv e f = {!!}

issec-bool-aut-bool' :
  ( e : bool ≃ bool) (d : is-decidable (Id (map-equiv e true) true)) →
  htpy-equiv (aut-bool-bool (bool-aut-bool e)) e
issec-bool-aut-bool' e (inl p) true =
  ( htpy-equiv-eq (ap aut-bool-bool p) true) ∙ (inv p)
issec-bool-aut-bool' e (inl p) false =
  ( htpy-equiv-eq (ap aut-bool-bool p) false) ∙
  ( inv (eq-false-equiv e p))
issec-bool-aut-bool' e (inr f) true =
  ( htpy-equiv-eq
    ( ap aut-bool-bool (eq-false (map-equiv e true) f)) true) ∙
  ( inv (eq-false (map-equiv e true) f))
issec-bool-aut-bool' e (inr f) false =
  ( htpy-equiv-eq (ap aut-bool-bool {!eq-true-equiv e ?!}) {!!}) ∙
  ( inv {!!})

issec-bool-aut-bool :
  (aut-bool-bool ∘ bool-aut-bool) ~ id
issec-bool-aut-bool e =
  eq-htpy-equiv
    ( issec-bool-aut-bool' e
      ( has-decidable-equality-𝟚 (map-equiv e true) true))
-}

--------------------------------------------------------------------------------

add-free-point-UU-Fin-Level :
  {l1 : Level} {k : ℕ} → UU-Fin-Level l1 k → UU-Fin-Level l1 (succ-ℕ k)
add-free-point-UU-Fin-Level X = coprod-UU-Fin-Level X unit-UU-Fin

add-free-point-UU-Fin : {k : ℕ} → UU-Fin k → UU-Fin (succ-ℕ k)
add-free-point-UU-Fin X = add-free-point-UU-Fin-Level X

maybe-structure :
  {l1 : Level} (X : UU l1) → UU (lsuc l1)
maybe-structure {l1} X = Σ (UU l1) (λ Y → Maybe Y ≃ X)

is-isolated-point :
  {l1 : Level} {X : UU l1} (x : X) → UU l1
is-isolated-point {l1} {X} x = (y : X) → is-decidable (Id x y)

cases-Eq-isolated-point :
  {l1 : Level} {X : UU l1} (x : X) → is-isolated-point x →
  (y : X) → is-decidable (Id x y) → UU lzero
cases-Eq-isolated-point x H y (inl p) = unit
cases-Eq-isolated-point x H y (inr f) = empty

is-prop-cases-Eq-isolated-point :
  {l1 : Level} {X : UU l1} (x : X) (d : is-isolated-point x) (y : X)
  (dy : is-decidable (Id x y)) → is-prop (cases-Eq-isolated-point x d y dy)
is-prop-cases-Eq-isolated-point x d y (inl p) = is-prop-unit
is-prop-cases-Eq-isolated-point x d y (inr f) = is-prop-empty

Eq-isolated-point :
  {l1 : Level} {X : UU l1} (x : X) → is-isolated-point x → X → UU lzero
Eq-isolated-point x d y =
  cases-Eq-isolated-point x d y (d y)

is-prop-Eq-isolated-point :
  {l1 : Level} {X : UU l1} (x : X) (d : is-isolated-point x) (y : X) →
  is-prop (Eq-isolated-point x d y)
is-prop-Eq-isolated-point x d y =
  is-prop-cases-Eq-isolated-point x d y (d y)

decide-reflexivity :
  {l1 : Level} {X : UU l1} (x : X) (d : is-decidable (Id x x)) →
  Σ (Id x x) (λ p → Id (inl p) d)
decide-reflexivity x (inl p) = pair p refl
decide-reflexivity x (inr f) = ex-falso (f refl)

refl-Eq-isolated-point :
  {l1 : Level} {X : UU l1} (x : X) (d : is-isolated-point x) →
  Eq-isolated-point x d x
refl-Eq-isolated-point x d =
  tr ( cases-Eq-isolated-point x d x)
     ( pr2 (decide-reflexivity x (d x)))
     ( star)

Eq-eq-isolated-point :
  {l1 : Level} {X : UU l1} (x : X) (d : is-isolated-point x) {y : X} →
  Id x y → Eq-isolated-point x d y
Eq-eq-isolated-point x d refl = refl-Eq-isolated-point x d

center-total-Eq-isolated-point :
  {l1 : Level} {X : UU l1} (x : X) (d : is-isolated-point x) →
  Σ X (Eq-isolated-point x d)
center-total-Eq-isolated-point x d =
  pair x (refl-Eq-isolated-point x d)

cases-contraction-total-Eq-isolated-point :
  {l1 : Level} {X : UU l1} (x : X) (d : is-isolated-point x) →
  (y : X) (dy : is-decidable (Id x y)) (e : cases-Eq-isolated-point x d y dy) →
  Id x y
cases-contraction-total-Eq-isolated-point x d y (inl p) e = p

contraction-total-Eq-isolated-point :
  {l1 : Level} {X : UU l1} (x : X) (d : is-isolated-point x) →
  (t : Σ X (Eq-isolated-point x d)) → Id (center-total-Eq-isolated-point x d) t
contraction-total-Eq-isolated-point x d (pair y e) =
  eq-subtype
    ( is-prop-Eq-isolated-point x d)
    ( cases-contraction-total-Eq-isolated-point x d y (d y) e)

is-contr-total-Eq-isolated-point :
  {l1 : Level} {X : UU l1} (x : X) (d : is-isolated-point x) →
  is-contr (Σ X (Eq-isolated-point x d))
is-contr-total-Eq-isolated-point x d =
  pair ( center-total-Eq-isolated-point x d)
       ( contraction-total-Eq-isolated-point x d)

is-equiv-Eq-eq-isolated-point :
  {l1 : Level} {X : UU l1} (x : X) (d : is-isolated-point x) (y : X) →
  is-equiv (Eq-eq-isolated-point x d {y})
is-equiv-Eq-eq-isolated-point x d =
  fundamental-theorem-id x
    ( refl-Eq-isolated-point x d)
    ( is-contr-total-Eq-isolated-point x d)
    ( λ y → Eq-eq-isolated-point x d {y})

equiv-Eq-eq-isolated-point :
  {l1 : Level} {X : UU l1} (x : X) (d : is-isolated-point x) (y : X) →
  Id x y ≃ Eq-isolated-point x d y
equiv-Eq-eq-isolated-point x d y =
  pair (Eq-eq-isolated-point x d) (is-equiv-Eq-eq-isolated-point x d y)

is-prop-eq-isolated-point :
  {l1 : Level} {X : UU l1} (x : X) (d : is-isolated-point x) (y : X) →
  is-prop (Id x y)
is-prop-eq-isolated-point x d y =
  is-prop-equiv
    ( Eq-isolated-point x d y)
    ( equiv-Eq-eq-isolated-point x d y)
    ( is-prop-Eq-isolated-point x d y)

isolated-point :
  {l1 : Level} (X : UU l1) → UU l1
isolated-point X = Σ X is-isolated-point

complement-isolated-point :
  {l1 : Level} (X : UU l1) → isolated-point X → UU l1
complement-isolated-point X x =
  Σ X (λ y → ¬ (Id (pr1 x) y))

map-maybe-structure-isolated-point :
  {l1 : Level} (X : UU l1) (x : isolated-point X) →
  Maybe (complement-isolated-point X x) → X
map-maybe-structure-isolated-point X (pair x d) (inl (pair y f)) = y
map-maybe-structure-isolated-point X (pair x d) (inr star) = x

cases-map-inv-maybe-structure-isolated-point :
  {l1 : Level} (X : UU l1) (x : isolated-point X) →
  (y : X) → is-decidable (Id (pr1 x) y) → Maybe (complement-isolated-point X x)
cases-map-inv-maybe-structure-isolated-point X (pair x dx) y (inl p) =
  inr star
cases-map-inv-maybe-structure-isolated-point X (pair x dx) y (inr f) =
  inl (pair y f)

map-inv-maybe-structure-isolated-point :
  {l1 : Level} (X : UU l1) (x : isolated-point X) →
  X → Maybe (complement-isolated-point X x)
map-inv-maybe-structure-isolated-point X (pair x d) y =
  cases-map-inv-maybe-structure-isolated-point X (pair x d) y (d y)

cases-issec-map-inv-maybe-structure-isolated-point :
  {l1 : Level} (X : UU l1) (x : isolated-point X) →
  (y : X) (d : is-decidable (Id (pr1 x) y)) →
  Id ( map-maybe-structure-isolated-point X x
       ( cases-map-inv-maybe-structure-isolated-point X x y d))
     ( y)
cases-issec-map-inv-maybe-structure-isolated-point X (pair x dx) .x (inl refl) =
  refl
cases-issec-map-inv-maybe-structure-isolated-point X (pair x dx) y (inr f) =
  refl

issec-map-inv-maybe-structure-isolated-point :
  {l1 : Level} (X : UU l1) (x : isolated-point X) →
  ( map-maybe-structure-isolated-point X x ∘
    map-inv-maybe-structure-isolated-point X x) ~ id
issec-map-inv-maybe-structure-isolated-point X (pair x d) y =
  cases-issec-map-inv-maybe-structure-isolated-point X (pair x d) y (d y)

isretr-map-inv-maybe-structure-isolated-point :
  {l1 : Level} (X : UU l1) (x : isolated-point X) →
  ( map-inv-maybe-structure-isolated-point X x ∘
    map-maybe-structure-isolated-point X x) ~ id
isretr-map-inv-maybe-structure-isolated-point X (pair x dx) (inl (pair y f)) =
  ap ( cases-map-inv-maybe-structure-isolated-point X (pair x dx) y)
     ( eq-is-prop (is-prop-is-decidable (is-prop-eq-isolated-point x dx y)))
isretr-map-inv-maybe-structure-isolated-point X (pair x dx) (inr star) =
  ap ( cases-map-inv-maybe-structure-isolated-point X (pair x dx) x)
     { x = dx (map-maybe-structure-isolated-point X (pair x dx) (inr star))}
     { y = inl refl}
     ( eq-is-prop (is-prop-is-decidable (is-prop-eq-isolated-point x dx x)))

is-equiv-map-maybe-structure-isolated-point :
  {l1 : Level} (X : UU l1) (x : isolated-point X) →
  is-equiv (map-maybe-structure-isolated-point X x)
is-equiv-map-maybe-structure-isolated-point X x =
  is-equiv-has-inverse
    ( map-inv-maybe-structure-isolated-point X x)
    ( issec-map-inv-maybe-structure-isolated-point X x)
    ( isretr-map-inv-maybe-structure-isolated-point X x)

equiv-maybe-structure-isolated-point :
  {l1 : Level} (X : UU l1) (x : isolated-point X) →
  Maybe (complement-isolated-point X x) ≃ X
equiv-maybe-structure-isolated-point X x =
  pair ( map-maybe-structure-isolated-point X x)
       ( is-equiv-map-maybe-structure-isolated-point X x)

maybe-structure-isolated-point :
  {l1 : Level} {X : UU l1} → isolated-point X → maybe-structure X
maybe-structure-isolated-point {l1} {X} x =
  pair ( complement-isolated-point X x)
       ( equiv-maybe-structure-isolated-point X x)

equiv-neg :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  (X ≃ Y) → (¬ X ≃ ¬ Y)
equiv-neg {l1} {l2} {X} {Y} e =
  equiv-iff
    ( neg-Prop' X)
    ( neg-Prop' Y)
    ( pair (functor-neg (map-inv-equiv e)) (functor-neg (map-equiv e)))

equiv-complement-isolated-point :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) (x : isolated-point X)
  (y : isolated-point Y) (p : Id (map-equiv e (pr1 x)) (pr1 y)) →
  complement-isolated-point X x ≃ complement-isolated-point Y y
equiv-complement-isolated-point e x y p =
  equiv-Σ
    ( λ z → ¬ (Id (pr1 y) z))
    ( e)
    ( λ z →
      equiv-neg
        ( equiv-concat (inv p) (map-equiv e z) ∘e (equiv-ap e (pr1 x) z)))

complement-point-UU-Fin-Level :
  {l1 : Level} {k : ℕ} →
  Σ (UU-Fin-Level l1 (succ-ℕ k)) type-UU-Fin-Level → UU-Fin-Level l1 k
complement-point-UU-Fin-Level {l1} {k} T =
  pair
    ( X')
    ( apply-universal-property-trunc-Prop H (mere-equiv-Prop (Fin k) X')
      ( λ e →
        unit-trunc-Prop
          ( equiv-equiv-Maybe
            { X = Fin k}
            { Y = X'}
            ( ( inv-equiv
                ( equiv-maybe-structure-isolated-point X isolated-x)) ∘e
              ( e)))))
  where
  X = pr1 (pr1 T)
  H = pr2 (pr1 T)
  x = pr2 T
  isolated-x : isolated-point X
  isolated-x = pair x (λ y → has-decidable-equality-has-cardinality H x y)
  X' : UU l1
  X' = complement-isolated-point X isolated-x

complement-point-UU-Fin :
  {k : ℕ} → Σ (UU-Fin (succ-ℕ k)) type-UU-Fin → UU-Fin k
complement-point-UU-Fin X = complement-point-UU-Fin-Level X

type-complement-point-UU-Fin-Level :
  {l1 : Level} {k : ℕ} →
  Σ (UU-Fin-Level l1 (succ-ℕ k)) type-UU-Fin-Level → UU l1
type-complement-point-UU-Fin-Level X =
  type-UU-Fin-Level (complement-point-UU-Fin-Level X)

type-complement-point-UU-Fin :
  {k : ℕ} → Σ (UU-Fin (succ-ℕ k)) type-UU-Fin → UU lzero
type-complement-point-UU-Fin X =
  type-complement-point-UU-Fin-Level X

inclusion-complement-isolated-point :
  {l1 : Level} {X : UU l1} (x : isolated-point X) →
  complement-isolated-point X x → X
inclusion-complement-isolated-point x = pr1

natural-inclusion-equiv-complement-isolated-point :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) (x : isolated-point X)
  (y : isolated-point Y) (p : Id (map-equiv e (pr1 x)) (pr1 y)) →
  ( inclusion-complement-isolated-point y ∘
    map-equiv (equiv-complement-isolated-point e x y p)) ~
  ( map-equiv e ∘ inclusion-complement-isolated-point x)
natural-inclusion-equiv-complement-isolated-point e x y p (pair x' f) = refl

inclusion-complement-point-UU-Fin-Level :
  {l1 : Level} {k : ℕ} (X : Σ (UU-Fin-Level l1 (succ-ℕ k)) type-UU-Fin-Level) →
  type-complement-point-UU-Fin-Level X → type-UU-Fin-Level (pr1 X)
inclusion-complement-point-UU-Fin-Level X = pr1

inclusion-complement-point-UU-Fin :
  {k : ℕ} (X : Σ (UU-Fin (succ-ℕ k)) type-UU-Fin) →
  type-complement-point-UU-Fin X → type-UU-Fin (pr1 X)
inclusion-complement-point-UU-Fin X =
  inclusion-complement-point-UU-Fin-Level X

--------------------------------------------------------------------------------

-- Connected components of the universe

component-UU-Level :
  (l1 : Level) {l2 : Level} (A : UU l2) → UU (lsuc l1 ⊔ l2)
component-UU-Level l1 A = Σ (UU l1) (mere-equiv A)

type-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} → component-UU-Level l1 A → UU l1
type-component-UU-Level X = pr1 X

mere-equiv-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} (X : component-UU-Level l1 A) →
  mere-equiv A (type-component-UU-Level X)
mere-equiv-component-UU-Level X = pr2 X

component-UU :
  {l1 : Level} (A : UU l1) → UU (lsuc l1)
component-UU {l1} A = component-UU-Level l1 A

type-component-UU : {l1 : Level} {A : UU l1} (X : component-UU A) → UU l1
type-component-UU X = type-component-UU-Level X

mere-equiv-component-UU :
  {l1 : Level} {A : UU l1} (X : component-UU A) →
  mere-equiv A (type-component-UU X)
mere-equiv-component-UU X = mere-equiv-component-UU-Level X

-- We characterize the identity types of connected components of the universe

equiv-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} (X Y : component-UU-Level l1 A) → UU l1
equiv-component-UU-Level X Y =
  type-component-UU-Level X ≃ type-component-UU-Level Y

id-equiv-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} (X : component-UU-Level l1 A) →
  equiv-component-UU-Level X X
id-equiv-component-UU-Level X = equiv-id

equiv-eq-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} {X Y : component-UU-Level l1 A} →
  Id X Y → equiv-component-UU-Level X Y
equiv-eq-component-UU-Level {X = X} refl =
  id-equiv-component-UU-Level X

is-contr-total-equiv-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} (X : component-UU-Level l1 A) →
  is-contr (Σ (component-UU-Level l1 A) (equiv-component-UU-Level X))
is-contr-total-equiv-component-UU-Level X =
  is-contr-total-Eq-substructure
    ( is-contr-total-equiv (type-component-UU-Level X))
    ( λ Y → is-prop-mere-equiv _ Y)
    ( type-component-UU-Level X)
    ( equiv-id)
    ( mere-equiv-component-UU-Level X)

is-equiv-equiv-eq-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} (X Y : component-UU-Level l1 A) →
  is-equiv (equiv-eq-component-UU-Level {X = X} {Y})
is-equiv-equiv-eq-component-UU-Level X =
  fundamental-theorem-id X
    ( id-equiv-component-UU-Level X)
    ( is-contr-total-equiv-component-UU-Level X)
    ( λ Y → equiv-eq-component-UU-Level {X = X} {Y})

eq-equiv-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} (X Y : component-UU-Level l1 A) →
  equiv-component-UU-Level X Y → Id X Y
eq-equiv-component-UU-Level X Y =
  map-inv-is-equiv (is-equiv-equiv-eq-component-UU-Level X Y)

equiv-component-UU :
  {l1 : Level} {A : UU l1} (X Y : component-UU A) → UU l1
equiv-component-UU X Y = equiv-component-UU-Level X Y

id-equiv-component-UU :
  {l1 : Level} {A : UU l1} (X : component-UU A) → equiv-component-UU X X
id-equiv-component-UU X = id-equiv-component-UU-Level X

equiv-eq-component-UU :
  {l1 : Level} {A : UU l1} {X Y : component-UU A} →
  Id X Y → equiv-component-UU X Y
equiv-eq-component-UU p = equiv-eq-component-UU-Level p

is-contr-total-equiv-component-UU :
  {l1 : Level} {A : UU l1} (X : component-UU A) →
  is-contr (Σ (component-UU A) (equiv-component-UU X))
is-contr-total-equiv-component-UU X =
  is-contr-total-equiv-component-UU-Level X

is-equiv-equiv-eq-component-UU :
  {l1 : Level} {A : UU l1} (X Y : component-UU A) →
  is-equiv (equiv-eq-component-UU {X = X} {Y})
is-equiv-equiv-eq-component-UU X Y =
  is-equiv-equiv-eq-component-UU-Level X Y

eq-equiv-component-UU :
  {l1 : Level} {A : UU l1} (X Y : component-UU A) →
  equiv-component-UU X Y → Id X Y
eq-equiv-component-UU X Y =
  eq-equiv-component-UU-Level X Y

--------------------------------------------------------------------------------

equiv-UU-Fin-Level : {l : Level} {k : ℕ} → (X Y : UU-Fin-Level l k) → UU l
equiv-UU-Fin-Level X Y = equiv-component-UU-Level X Y

equiv-UU-Fin : {k : ℕ} (X Y : UU-Fin k) → UU lzero
equiv-UU-Fin X Y = equiv-component-UU X Y

id-equiv-UU-Fin-Level :
  {l : Level} {k : ℕ} (X : UU-Fin-Level l k) → equiv-UU-Fin-Level X X
id-equiv-UU-Fin-Level X = id-equiv-component-UU-Level X

id-equiv-UU-Fin :
  {k : ℕ} (X : UU-Fin k) → equiv-UU-Fin X X
id-equiv-UU-Fin X = id-equiv-component-UU X

equiv-eq-UU-Fin-Level :
  {l : Level} {k : ℕ} {X Y : UU-Fin-Level l k} → Id X Y → equiv-UU-Fin-Level X Y
equiv-eq-UU-Fin-Level p = equiv-eq-component-UU-Level p

equiv-eq-UU-Fin :
  {k : ℕ} {X Y : UU-Fin k} → Id X Y → equiv-UU-Fin X Y
equiv-eq-UU-Fin p = equiv-eq-component-UU p

is-contr-total-equiv-UU-Fin-Level :
  {l : Level} {k : ℕ} (X : UU-Fin-Level l k) →
  is-contr (Σ (UU-Fin-Level l k) (equiv-UU-Fin-Level X))
is-contr-total-equiv-UU-Fin-Level {l} {k} X =
  is-contr-total-equiv-component-UU-Level X

is-contr-total-equiv-UU-Fin :
  {k : ℕ} (X : UU-Fin k) → is-contr (Σ (UU-Fin k) (equiv-UU-Fin X))
is-contr-total-equiv-UU-Fin X =
  is-contr-total-equiv-component-UU X

is-equiv-equiv-eq-UU-Fin-Level :
  {l : Level} {k : ℕ} (X Y : UU-Fin-Level l k) →
  is-equiv (equiv-eq-UU-Fin-Level {X = X} {Y})
is-equiv-equiv-eq-UU-Fin-Level X =
  is-equiv-equiv-eq-component-UU-Level X

is-equiv-equiv-eq-UU-Fin :
  {k : ℕ} (X Y : UU-Fin k) → is-equiv (equiv-eq-UU-Fin {X = X} {Y})
is-equiv-equiv-eq-UU-Fin X =
  is-equiv-equiv-eq-component-UU X

eq-equiv-UU-Fin-Level :
  {l : Level} {k : ℕ} (X Y : UU-Fin-Level l k) →
  equiv-UU-Fin-Level X Y → Id X Y
eq-equiv-UU-Fin-Level X Y =
  eq-equiv-component-UU-Level X Y

eq-equiv-UU-Fin :
  {k : ℕ} (X Y : UU-Fin k) → equiv-UU-Fin X Y → Id X Y
eq-equiv-UU-Fin X Y = eq-equiv-component-UU X Y

equiv-complement-point-UU-Fin-Level :
  {l1 : Level} {k : ℕ}
  (X Y : Σ (UU-Fin-Level l1 (succ-ℕ k)) type-UU-Fin-Level) →
  (e : equiv-UU-Fin-Level (pr1 X) (pr1 Y))
  (p : Id (map-equiv e (pr2 X)) (pr2 Y)) →
  equiv-UU-Fin-Level
    ( complement-point-UU-Fin-Level X)
    ( complement-point-UU-Fin-Level Y)
equiv-complement-point-UU-Fin-Level
  S T e p =
  equiv-complement-isolated-point e
    ( pair x (λ x' → has-decidable-equality-has-cardinality H x x'))
    ( pair y (λ y' → has-decidable-equality-has-cardinality K y y'))
    ( p)
  where
  H = pr2 (pr1 S)
  x = pr2 S
  K = pr2 (pr1 T)
  y = pr2 T

equiv-complement-point-UU-Fin :
  {k : ℕ} (X Y : Σ (UU-Fin (succ-ℕ k)) type-UU-Fin) →
  (e : equiv-UU-Fin (pr1 X) (pr1 Y)) (p : Id (map-equiv e (pr2 X)) (pr2 Y)) →
  equiv-UU-Fin (complement-point-UU-Fin X) (complement-point-UU-Fin Y)
equiv-complement-point-UU-Fin X Y e p =
  equiv-complement-point-UU-Fin-Level X Y e p

--------------------------------------------------------------------------------

-- The binomial theorem for types

is-decidable-prop : {l : Level} → UU l → UU l
is-decidable-prop X = is-prop X × (is-decidable X)

is-prop-is-decidable-prop :
  {l : Level} (X : UU l) → is-prop (is-decidable-prop X)
is-prop-is-decidable-prop X =
  is-prop-is-inhabited
    ( λ H →
      is-prop-prod
        ( is-prop-is-prop X)
        ( is-prop-is-decidable (pr1 H)))

is-decidable-map :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (X → Y) → UU (l1 ⊔ l2)
is-decidable-map {Y = Y} f = (y : Y) → is-decidable (fib f y)

is-decidable-prop-map :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (X → Y) → UU (l1 ⊔ l2)
is-decidable-prop-map {Y = Y} f = (y : Y) → is-decidable-prop (fib f y)

is-prop-map-is-decidable-prop-map :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y} →
  is-decidable-prop-map f → is-prop-map f
is-prop-map-is-decidable-prop-map H y = pr1 (H y)

is-decidable-map-is-decidable-prop-map :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y} →
  is-decidable-prop-map f → is-decidable-map f
is-decidable-map-is-decidable-prop-map H y = pr2 (H y)

is-prop-is-decidable-prop-map :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) →
  is-prop (is-decidable-prop-map f)
is-prop-is-decidable-prop-map f =
  is-prop-Π (λ y → is-prop-is-decidable-prop (fib f y))

is-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (X → Y) → UU (l1 ⊔ l2)
is-decidable-emb {Y = Y} f = is-emb f × is-decidable-map f

is-emb-is-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y} →
  is-decidable-emb f → is-emb f
is-emb-is-decidable-emb H = pr1 H

is-decidable-map-is-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y} →
  is-decidable-emb f → is-decidable-map f
is-decidable-map-is-decidable-emb H = pr2 H

is-decidable-emb-is-decidable-prop-map :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) →
  is-decidable-prop-map f → is-decidable-emb f
is-decidable-emb-is-decidable-prop-map f H =
  pair
    ( is-emb-is-prop-map (is-prop-map-is-decidable-prop-map H))
    ( is-decidable-map-is-decidable-prop-map H)

_↪d_ :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (l1 ⊔ l2)
X ↪d Y = Σ (X → Y) is-decidable-emb

map-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → X ↪d Y → X → Y
map-decidable-emb e = pr1 e

is-decidable-emb-map-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ↪d Y) →
  is-decidable-emb (map-decidable-emb e)
is-decidable-emb-map-decidable-emb e = pr2 e

emb-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → X ↪d Y → X ↪ Y
emb-decidable-emb f = {!!}

choose-UU-Level :
  (l : Level) {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (lsuc l ⊔ l1 ⊔ l2)
choose-UU-Level l X Y =
  Σ (component-UU-Level l Y) (λ Z → type-component-UU-Level Z ↪ X)

type-choose-UU-Level :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} → choose-UU-Level l3 X Y → UU l3
type-choose-UU-Level Z = type-component-UU-Level (pr1 Z)

mere-equiv-choose-UU-Level :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (Z : choose-UU-Level l3 X Y) →
  mere-equiv Y (type-choose-UU-Level Z)
mere-equiv-choose-UU-Level Z = mere-equiv-component-UU-Level (pr1 Z)

emb-choose-UU-Level :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (Z : choose-UU-Level l3 X Y) →
  type-choose-UU-Level Z ↪ X
emb-choose-UU-Level Z = pr2 Z

map-emb-choose-UU-Level :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (Z : choose-UU-Level l3 X Y) →
  type-choose-UU-Level Z → X
map-emb-choose-UU-Level Z = map-emb (emb-choose-UU-Level Z)

is-emb-map-emb-choose-UU-Level :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (Z : choose-UU-Level l3 X Y) →
  is-emb (map-emb-choose-UU-Level Z)
is-emb-map-emb-choose-UU-Level Z = is-emb-map-emb (emb-choose-UU-Level Z)

_choose-UU_ : {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (lsuc (l1 ⊔ l2))
_choose-UU_ {l1} {l2} X Y = choose-UU-Level (l1 ⊔ l2) X Y

