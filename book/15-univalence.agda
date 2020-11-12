{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module book.15-univalence where

import book.14-propositional-truncation-solutions
import book.counting
open book.14-propositional-truncation-solutions public
open book.counting public

--------------------------------------------------------------------------------

-- Section 15 The univalence axiom

--------------------------------------------------------------------------------

-- Section 15.1 Equivalent forms of the univalence axiom

-- Definition 15.1.1

equiv-eq : {i : Level} {A : UU i} {B : UU i} → Id A B → A ≃ B
equiv-eq refl = equiv-id

UNIVALENCE : {i : Level} (A B : UU i) → UU (lsuc i)
UNIVALENCE A B = is-equiv (equiv-eq {A = A} {B = B})

-- Theorem 15.1.2

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

abstract
  is-contr-total-equiv : {i : Level} (A : UU i) →
    is-contr (Σ (UU i) (λ X → A ≃ X))
  is-contr-total-equiv A = is-contr-total-equiv-UNIVALENCE A (univalence A)

inv-inv-equiv :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) →
  Id (inv-equiv (inv-equiv e)) e
inv-inv-equiv (pair f (pair (pair g G) (pair h H))) = eq-htpy-equiv refl-htpy

is-equiv-inv-equiv :
  {i j : Level} {A : UU i} {B : UU j} → is-equiv (inv-equiv {A = A} {B = B})
is-equiv-inv-equiv =
  is-equiv-has-inverse
    ( inv-equiv)
    ( inv-inv-equiv)
    ( inv-inv-equiv)

equiv-inv-equiv :
  {i j : Level} {A : UU i} {B : UU j} → (A ≃ B) ≃ (B ≃ A)
equiv-inv-equiv = pair inv-equiv is-equiv-inv-equiv

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

-- Section 15.2 Univalence implies function extensionality

-- Lemma 15.2.1

is-equiv-postcomp-univalence :
  {l1 l2 : Level} {X Y : UU l1} (A : UU l2) (e : X ≃ Y) →
  is-equiv (postcomp A (map-equiv e))
is-equiv-postcomp-univalence {X = X} A =
  ind-equiv X (λ Y e → is-equiv (postcomp A (map-equiv e))) is-equiv-id

-- Theorem 15.2.2

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

mere-equiv :
  {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
mere-equiv X Y = type-trunc-Prop (X ≃ Y)

has-finite-cardinality :
  {l : Level} → UU l → UU l
has-finite-cardinality X = Σ ℕ (λ k → mere-equiv (Fin k) X)

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
        map-universal-property-trunc-Prop
          ( pair (Id k l) (is-set-ℕ k l))
          ( λ (f : Fin l ≃ X) →
            is-injective-Fin ((inv-equiv f) ∘e e))
          ( L)))

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
        ( eq-is-prop is-prop-has-finite-cardinality
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

is-finite-is-contr :
  {l1 : Level} {X : UU l1} → is-contr X → is-finite X
is-finite-is-contr H = is-finite-count (count-is-contr H) 

is-finite-Fin : {k : ℕ} → is-finite (Fin k)
is-finite-Fin {k} = is-finite-count (count-Fin k)

{- Finiteness and coproducts -}

is-finite-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  is-finite X → is-finite Y → is-finite (coprod X Y)
is-finite-coprod {X = X} {Y} is-finite-X is-finite-Y =
  apply-universal-property-trunc-Prop is-finite-X
    ( is-finite-Prop (coprod X Y))
    ( λ (e : count X) →
      map-universal-property-trunc-Prop
        ( is-finite-Prop (coprod X Y))
        ( is-finite-count ∘ (count-coprod e))
        ( is-finite-Y))

is-finite-left-summand :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → is-finite (coprod X Y) → is-finite X
is-finite-left-summand =
  functor-trunc-Prop count-left-summand

is-finite-right-summand :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → is-finite (coprod X Y) → is-finite Y
is-finite-right-summand =
  functor-trunc-Prop count-right-summand

{- Finiteness and products -}

is-finite-prod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  is-finite X → is-finite Y → is-finite (X × Y)
is-finite-prod {X = X} {Y} is-finite-X is-finite-Y =
  apply-universal-property-trunc-Prop is-finite-X
    ( is-finite-Prop (X × Y))
    ( λ (e : count X) →
      map-universal-property-trunc-Prop
        ( is-finite-Prop (X × Y))
        ( is-finite-count ∘ (count-prod e))
        ( is-finite-Y))

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
      map-universal-property-trunc-Prop
        ( is-finite-Prop (Σ X Y))
        ( is-finite-count ∘ (count-Σ e))
        ( finite-choice is-finite-X is-finite-Y))

is-finite-fiber-is-finite-Σ :
  {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} →
  is-finite X → is-finite (Σ X Y) → (x : X) → is-finite (Y x)
is-finite-fiber-is-finite-Σ {l1} {l2} {X} {Y} f g x =
  apply-universal-property-trunc-Prop f
    ( is-finite-Prop (Y x))
    ( λ e → functor-trunc-Prop (λ h → count-fiber-count-Σ e h x) g)

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

is-finite-Eq-has-decidable-equality :
  {l1 : Level} {X : UU l1} (d : has-decidable-equality X) →
  {x y : X} → is-finite (Eq-has-decidable-equality d x y)
is-finite-Eq-has-decidable-equality d =
  is-finite-count (count-Eq-has-decidable-equality d)

is-finite-eq :
  {l1 : Level} {X : UU l1} →
  has-decidable-equality X → {x y : X} → is-finite (Id x y)
is-finite-eq d {x} {y} =
  is-finite-equiv
    ( equiv-prop
      ( is-prop-Eq-has-decidable-equality d)
      ( is-set-has-decidable-equality d x y)
      ( eq-Eq-has-decidable-equality d)
      ( Eq-has-decidable-equality-eq d))
    ( is-finite-Eq-has-decidable-equality d)

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
            ( λ t → count-eq (has-decidable-equality-is-finite (g (pr1 t)))))))

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

choice-count-Σ-is-finite-fiber :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count (Σ A B) → ((x : A) → is-finite (B x)) →
  ((x : A) → type-trunc-Prop (B x)) → (x : A) → B x
choice-count-Σ-is-finite-fiber e g H x =
  {!!}

choice-is-finite-Σ-is-finite-fiber :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-finite (Σ A B) → ((x : A) → is-finite (B x)) →
  ((x : A) → type-trunc-Prop (B x)) → type-trunc-Prop ((x : A) → B x)
choice-is-finite-Σ-is-finite-fiber {l1} {l2} {A} {B} f g H =
  apply-universal-property-trunc-Prop f
    ( trunc-Prop ((x : A) → B x))
    ( λ e →
      unit-trunc-Prop
        ( λ x →
          map-fib-pr1 B x
            {!map-Σ!}))

is-finite-base-is-finite-Σ-merely-inhabited :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  ( b : (x : A) → type-trunc-Prop (B x)) →
  is-finite (Σ A B) → ((x : A) → is-finite (B x)) → is-finite A
is-finite-base-is-finite-Σ-merely-inhabited {l1} {l2} {A} {B} b f g =
  is-finite-base-is-finite-Σ-mere-section
    ( choice-is-finite-Σ-is-finite-fiber f g b)
    ( f)
    ( g)

section-is-finite-base-is-finite-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-finite (Σ A B) →
  (g : (x : A) → is-finite (B x)) →
  is-finite (Σ A (λ x → is-zero-ℕ (number-of-elements-is-finite (g x)))) →
  (x : A) → coprod (B x) (is-zero-ℕ (number-of-elements-is-finite (g x)))
section-is-finite-base-is-finite-Σ f g h x with
  is-decidable-is-zero-ℕ (number-of-elements-is-finite (g x))
... | inl p = inr p
... | inr H with is-successor-is-nonzero-ℕ H
... | (pair k p) = inl {!!}

{-
section-count-base-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count (Σ A B) →
  (f : (x : A) → count (B x)) →
  count (Σ A (λ x → is-zero-ℕ (number-of-elements (f x)))) →
  (x : A) → coprod (B x) (is-zero-ℕ (number-of-elements (f x)))
section-count-base-count-Σ' e f g x with
  is-decidable-is-zero-ℕ (number-of-elements (f x))
... | inl p = inr p
... | inr H with is-successor-is-nonzero-ℕ H
... | (pair k p) = inl (map-equiv-count (f x) (tr Fin (inv p) zero-Fin))

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
-}

is-finite-base-is-finite-Σ' :
  {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} →
  is-finite (Σ X Y) → (g : (x : X) → is-finite (Y x)) →
  is-finite (Σ X (λ x → is-zero-ℕ (number-of-elements-is-finite (g x)))) →
  is-finite X
is-finite-base-is-finite-Σ' {l1} {l2} {X} {Y} f g h =
  apply-universal-property-trunc-Prop f
    ( is-finite-Prop X)
    ( λ eΣ →
      apply-universal-property-trunc-Prop h
        ( is-finite-Prop X)
        ( λ ec →
          {!!}))
  

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

-- Exercise 15.1

tr-equiv-eq-ap : {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {x y : A}
  (p : Id x y) → (map-equiv (equiv-eq (ap B p))) ~ tr B p
tr-equiv-eq-ap refl = refl-htpy

-- Exercise 15.2

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
        ( eq-is-contr
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
