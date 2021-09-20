{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module book.17-univalence where

open import book.16-finite-types public

--------------------------------------------------------------------------------

-- Section 17 The univalence axiom

--------------------------------------------------------------------------------

-- Section 17.1 Equivalent forms of the univalence axiom

-- Theorem 17.1.1

-- Theorem 17.1.1 Condition (i)

equiv-eq : {i : Level} {A : UU i} {B : UU i} → Id A B → A ≃ B
equiv-eq refl = equiv-id

UNIVALENCE : {i : Level} (A B : UU i) → UU (lsuc i)
UNIVALENCE A B = is-equiv (equiv-eq {A = A} {B = B})

-- Theorem 17.1.1 (i) implies (ii)

is-contr-total-equiv-UNIVALENCE : {i : Level} (A : UU i) →
  ((B : UU i) → UNIVALENCE A B) → is-contr (Σ (UU i) (λ X → A ≃ X))
is-contr-total-equiv-UNIVALENCE A UA =
  fundamental-theorem-id' A equiv-id (λ B → equiv-eq) UA

-- Theorem 17.1.1 (ii) implies (i)

UNIVALENCE-is-contr-total-equiv : {i : Level} (A : UU i) →
  is-contr (Σ (UU i) (λ X → A ≃ X)) → (B : UU i) → UNIVALENCE A B
UNIVALENCE-is-contr-total-equiv A c =
  fundamental-theorem-id A equiv-id c (λ B → equiv-eq)

-- Theorem 17.1.1 Condition (iii)

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

-- Theorem 17.1.1 (ii) implies (iii)

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

-- Theorem 17.1.1 (iii) implies (ii)

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

-- Some immediate consequences of the univalence axiom

equiv-fam :
  {l1 l2 l3 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3) →
  UU (l1 ⊔ l2 ⊔ l3)
equiv-fam {A = A} B C = (a : A) → B a ≃ C a

equiv-id-fam :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → equiv-fam B B
equiv-id-fam B a = equiv-id

equiv-eq-fam :
  {l1 l2 : Level} {A : UU l1} (B C : A → UU l2) → Id B C → equiv-fam B C
equiv-eq-fam B .B refl = equiv-id-fam B

is-contr-total-equiv-fam :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
  is-contr (Σ (A → UU l2) (equiv-fam B))
is-contr-total-equiv-fam B =
  is-contr-total-Eq-Π
    ( λ x X → (B x) ≃ X)
    ( λ x → is-contr-total-equiv (B x))

is-equiv-equiv-eq-fam :
  {l1 l2 : Level} {A : UU l1} (B C : A → UU l2) → is-equiv (equiv-eq-fam B C)
is-equiv-equiv-eq-fam B =
  fundamental-theorem-id B
    ( equiv-id-fam B)
    ( is-contr-total-equiv-fam B)
    ( equiv-eq-fam B)

eq-equiv-fam :
  {l1 l2 : Level} {A : UU l1} {B C : A → UU l2} → equiv-fam B C → Id B C
eq-equiv-fam {B = B} {C} = map-inv-is-equiv (is-equiv-equiv-eq-fam B C)

-- Theorem 17.1.3

is-contr-total-iff :
  {l1 : Level} (P : UU-Prop l1) → is-contr (Σ (UU-Prop l1) (λ Q → P ⇔ Q))
is-contr-total-iff {l1} P =
  is-contr-equiv
    ( Σ (UU-Prop l1) (λ Q → type-Prop P ≃ type-Prop Q))
    ( equiv-tot (equiv-equiv-iff P))
    ( is-contr-total-Eq-substructure
      ( is-contr-total-equiv (type-Prop P))
      ( is-prop-is-prop)
      ( type-Prop P)
      ( equiv-id)
      ( is-prop-type-Prop P))

is-equiv-iff-eq :
  {l1 : Level} (P Q : UU-Prop l1) → is-equiv (iff-eq {l1} {P} {Q})
is-equiv-iff-eq P =
  fundamental-theorem-id P
    ( pair id id)
    ( is-contr-total-iff P)
    ( λ Q → iff-eq {P = P} {Q})

-- Corollary 17.1.4

is-decidable-prop : {l : Level} → UU l → UU l
is-decidable-prop A = is-prop A × is-decidable A

decidable-Prop :
  (l : Level) → UU (lsuc l)
decidable-Prop l = Σ (UU l) is-decidable-prop

prop-decidable-Prop :
  {l : Level} → decidable-Prop l → UU-Prop l
prop-decidable-Prop P = pair (pr1 P) (pr1 (pr2 P))

type-decidable-Prop :
  {l : Level} → decidable-Prop l → UU l
type-decidable-Prop P = type-Prop (prop-decidable-Prop P)

is-prop-type-decidable-Prop :
  {l : Level} (P : decidable-Prop l) → is-prop (type-decidable-Prop P)
is-prop-type-decidable-Prop P = is-prop-type-Prop (prop-decidable-Prop P)

is-decidable-type-decidable-Prop :
  {l : Level} (P : decidable-Prop l) → is-decidable (type-decidable-Prop P)
is-decidable-type-decidable-Prop P = pr2 (pr2 P)

is-decidable-prop-decidable-Prop :
  {l : Level} (P : decidable-Prop l) → UU-Prop l
is-decidable-prop-decidable-Prop P =
  pair ( is-decidable (type-decidable-Prop P))
       ( is-prop-is-decidable (is-prop-type-decidable-Prop P))

is-contr-raise-unit :
  {l1 : Level} → is-contr (raise-unit l1)
is-contr-raise-unit {l1} =
  is-contr-equiv' unit (equiv-raise l1 unit) is-contr-unit

is-prop-raise-unit :
  {l1 : Level} → is-prop (raise-unit l1)
is-prop-raise-unit {l1} =
  is-prop-equiv' unit (equiv-raise l1 unit) is-prop-unit

raise-unit-Prop :
  (l1 : Level) → UU-Prop l1
raise-unit-Prop l1 = pair (raise-unit l1) is-prop-raise-unit

is-contr-total-true-Prop :
  {l1 : Level} → is-contr (Σ (UU-Prop l1) (λ P → type-Prop P))
is-contr-total-true-Prop {l1} =
  is-contr-equiv
    ( Σ (UU-Prop l1) (λ P → raise-unit-Prop l1 ⇔ P))
    ( equiv-tot
      ( λ P →
        inv-equiv
          ( ( equiv-universal-property-contr
              ( raise-star)
              ( is-contr-raise-unit)
              ( type-Prop P)) ∘e
            ( right-unit-law-prod-is-contr
              ( is-contr-Π
                ( λ x →
                  is-proof-irrelevant-is-prop
                    ( is-prop-raise-unit)
                    ( raise-star)))))))
    ( is-contr-total-iff (raise-unit-Prop l1))

is-prop-raise-empty :
  {l1 : Level} → is-prop (raise-empty l1)
is-prop-raise-empty {l1} =
  is-prop-equiv'
    ( empty)
    ( equiv-raise l1 empty)
    ( is-prop-empty)

raise-empty-Prop :
  (l1 : Level) → UU-Prop l1
raise-empty-Prop l1 = pair (raise-empty l1) is-prop-raise-empty

is-empty-raise-empty :
  {l1 : Level} → is-empty (raise-empty l1)
is-empty-raise-empty {l1} = map-inv-equiv (equiv-raise-empty l1)

is-contr-total-false-Prop :
  {l1 : Level} → is-contr (Σ (UU-Prop l1) (λ P → type-Prop (neg-Prop P)))
is-contr-total-false-Prop {l1} =
  is-contr-equiv
    ( Σ (UU-Prop l1) (λ P → raise-empty-Prop l1 ⇔ P))
    ( equiv-tot
      ( λ P →
        inv-equiv
          ( ( inv-equiv (equiv-postcomp (type-Prop P) (equiv-raise l1 empty))) ∘e
            ( left-unit-law-prod-is-contr
              ( universal-property-empty-is-empty
                ( raise-empty l1)
                ( is-empty-raise-empty)
                ( type-Prop P))))))
    ( is-contr-total-iff (raise-empty-Prop l1))

equiv-Fin-two-ℕ-decidable-Prop :
  {l1 : Level} → decidable-Prop l1 ≃ Fin two-ℕ
equiv-Fin-two-ℕ-decidable-Prop {l1} =
  ( ( equiv-coprod
      ( equiv-is-contr
        ( is-contr-total-true-Prop)
        ( is-contr-Fin-one-ℕ))
      ( equiv-is-contr
        ( is-contr-total-false-Prop)
        ( is-contr-unit))) ∘e
    ( left-distributive-Σ-coprod
      ( UU-Prop l1)
      ( λ P → type-Prop P)
      ( λ P → type-Prop (neg-Prop P)))) ∘e
  ( inv-assoc-Σ (UU l1) is-prop (λ X → is-decidable (pr1 X)))

bool-Fin-two-ℕ : Fin two-ℕ → bool
bool-Fin-two-ℕ (inl (inr star)) = false
bool-Fin-two-ℕ (inr star) = true

Fin-two-ℕ-bool : bool → Fin two-ℕ
Fin-two-ℕ-bool true = inr star
Fin-two-ℕ-bool false = inl (inr star)

isretr-Fin-two-ℕ-bool : (Fin-two-ℕ-bool ∘ bool-Fin-two-ℕ) ~ id
isretr-Fin-two-ℕ-bool (inl (inr star)) = refl
isretr-Fin-two-ℕ-bool (inr star) = refl

issec-Fin-two-ℕ-bool : (bool-Fin-two-ℕ ∘ Fin-two-ℕ-bool) ~ id
issec-Fin-two-ℕ-bool true = refl
issec-Fin-two-ℕ-bool false = refl

equiv-bool-Fin-two-ℕ : Fin two-ℕ ≃ bool
equiv-bool-Fin-two-ℕ =
  pair
    ( bool-Fin-two-ℕ)
    ( is-equiv-has-inverse
      ( Fin-two-ℕ-bool)
      ( issec-Fin-two-ℕ-bool)
      ( isretr-Fin-two-ℕ-bool))

equiv-bool-decidable-Prop : {l : Level} → decidable-Prop l ≃ bool
equiv-bool-decidable-Prop {l} =
  equiv-bool-Fin-two-ℕ ∘e equiv-Fin-two-ℕ-decidable-Prop

-- Bureaucracy

decidable-Eq-Fin :
  (n : ℕ) (i j : Fin n) → decidable-Prop lzero
decidable-Eq-Fin n i j =
  pair (Id i j) (pair (is-set-Fin n i j) ( has-decidable-equality-Fin i j))

is-prop-is-decidable-prop :
  {l : Level} (X : UU l) → is-prop (is-decidable-prop X)
is-prop-is-decidable-prop X =
  is-prop-is-inhabited
    ( λ H →
      is-prop-prod
        ( is-prop-is-prop X)
        ( is-prop-is-decidable (pr1 H)))

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

-- Subuniverses

is-subuniverse :
  {l1 l2 : Level} (P : UU l1 → UU l2) → UU ((lsuc l1) ⊔ l2)
is-subuniverse P = is-subtype P

subuniverse :
  (l1 l2 : Level) → UU ((lsuc l1) ⊔ (lsuc l2))
subuniverse l1 l2 = UU l1 → UU-Prop l2

is-subtype-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  is-prop (type-Prop (P X))
is-subtype-subuniverse P X = is-prop-type-Prop (P X)

{- By univalence, subuniverses are closed under equivalences. -}
in-subuniverse-equiv :
  {l1 l2 : Level} (P : UU l1 → UU l2) {X Y : UU l1} → X ≃ Y → P X → P Y
in-subuniverse-equiv P e = tr P (eq-equiv _ _ e)

in-subuniverse-equiv' :
  {l1 l2 : Level} (P : UU l1 → UU l2) {X Y : UU l1} → X ≃ Y → P Y → P X
in-subuniverse-equiv' P e = tr P (inv (eq-equiv _ _ e))

total-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) → UU ((lsuc l1) ⊔ l2)
total-subuniverse {l1} P = Σ (UU l1) (λ X → type-Prop (P X))

{- We also introduce the notion of 'global subuniverse'. The handling of 
   universe levels is a bit more complicated here, since (l : Level) → A l are 
   kinds but not types. -}
   
is-global-subuniverse :
  (α : Level → Level) (P : (l : Level) → subuniverse l (α l)) →
  (l1 l2 : Level) → UU _
is-global-subuniverse α P l1 l2 =
  (X : UU l1) (Y : UU l2) → X ≃ Y → type-Prop (P l1 X) → type-Prop (P l2 Y)

{- Next we characterize the identity type of a subuniverse. -}

equiv-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  (s t : total-subuniverse P) → UU l1
equiv-subuniverse P (pair X p) t = X ≃ (pr1 t)

equiv-subuniverse-eq :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  (s t : total-subuniverse P) → Id s t → equiv-subuniverse P s t
equiv-subuniverse-eq P (pair X p) .(pair X p) refl = equiv-id

abstract
  is-contr-total-equiv-subuniverse :
    {l1 l2 : Level} (P : subuniverse l1 l2)
    (s : total-subuniverse P) →
    is-contr (Σ (total-subuniverse P) (λ t → equiv-subuniverse P s t))
  is-contr-total-equiv-subuniverse P (pair X p) =
    is-contr-total-Eq-substructure
      ( is-contr-total-equiv X)
      ( is-subtype-subuniverse P)
      ( X)
      ( equiv-id)
      ( p)

abstract
  is-equiv-equiv-subuniverse-eq :
    {l1 l2 : Level} (P : subuniverse l1 l2)
    (s t : total-subuniverse P) → is-equiv (equiv-subuniverse-eq P s t)
  is-equiv-equiv-subuniverse-eq P (pair X p) =
    fundamental-theorem-id
      ( pair X p)
      ( equiv-id)
      ( is-contr-total-equiv-subuniverse P (pair X p))
      ( equiv-subuniverse-eq P (pair X p))

eq-equiv-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  {s t : total-subuniverse P} → equiv-subuniverse P s t → Id s t
eq-equiv-subuniverse P {s} {t} =
  map-inv-is-equiv (is-equiv-equiv-subuniverse-eq P s t)

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

add-free-point-UU-Fin-Level :
  {l1 : Level} {k : ℕ} → UU-Fin-Level l1 k → UU-Fin-Level l1 (succ-ℕ k)
add-free-point-UU-Fin-Level X = coprod-UU-Fin-Level X unit-UU-Fin

add-free-point-UU-Fin : {k : ℕ} → UU-Fin k → UU-Fin (succ-ℕ k)
add-free-point-UU-Fin X = add-free-point-UU-Fin-Level X

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

--------------------------------------------------------------------------------

-- Section 17.3 Maps and families of types

-- Theorem 17.3.1

slice-UU : (l : Level) {l1 : Level} (A : UU l1) → UU (l1 ⊔ lsuc l)
slice-UU l A = Σ (UU l) (λ X → X → A)

Fib : {l l1 : Level} (A : UU l1) → slice-UU l A → A → UU (l1 ⊔ l)
Fib A f = fib (pr2 f)

Pr1 : {l l1 : Level} (A : UU l1) → (A → UU l) → slice-UU (l1 ⊔ l) A
Pr1 A B = pair (Σ A B) pr1

module _
  {l1 l2 : Level} {A : UU l1}
  where

  equiv-slice' : (f g : slice-UU l2 A) → UU (l1 ⊔ l2)
  equiv-slice' f g = equiv-slice A (pr2 f) (pr2 g)
  
  equiv-id-slice-UU : (f : slice-UU l2 A) → equiv-slice' f f
  equiv-id-slice-UU f = pair equiv-id refl-htpy

  equiv-eq-slice-UU : (f g : slice-UU l2 A) → Id f g → equiv-slice' f g
  equiv-eq-slice-UU f .f refl = equiv-id-slice-UU f

  is-contr-total-equiv-slice' :
    (f : slice-UU l2 A) → is-contr (Σ (slice-UU l2 A) (equiv-slice' f))
  is-contr-total-equiv-slice' (pair X f) =
    is-contr-total-Eq-structure
      ( λ Y g e → f ~ (g ∘ map-equiv e))
      ( is-contr-total-equiv X)
      ( pair X equiv-id)
      ( is-contr-total-htpy f)

  is-equiv-equiv-eq-slice-UU :
    (f g : slice-UU l2 A) → is-equiv (equiv-eq-slice-UU f g)
  is-equiv-equiv-eq-slice-UU f =
    fundamental-theorem-id f
      ( equiv-id-slice-UU f)
      ( is-contr-total-equiv-slice' f)
      ( equiv-eq-slice-UU f)

  eq-equiv-slice :
    (f g : slice-UU l2 A) → equiv-slice' f g → Id f g
  eq-equiv-slice f g =
    map-inv-is-equiv (is-equiv-equiv-eq-slice-UU f g)

issec-Pr1 :
  {l1 l2 : Level} {A : UU l1} → (Fib {l1 ⊔ l2} A ∘ Pr1 {l1 ⊔ l2} A) ~ id
issec-Pr1 B = eq-equiv-fam equiv-fib-pr1
                           
isretr-Pr1 :
  {l1 l2 : Level} {A : UU l1} → (Pr1 {l1 ⊔ l2} A ∘ Fib {l1 ⊔ l2} A) ~ id
isretr-Pr1 {A = A} (pair X f) =
  eq-equiv-slice
    ( Pr1 A (Fib A (pair X f)))
    ( pair X f)
    ( pair (equiv-total-fib f) (triangle-map-equiv-total-fib f))

is-equiv-Fib :
  {l1 : Level} (l2 : Level) (A : UU l1) → is-equiv (Fib {l1 ⊔ l2} A)
is-equiv-Fib l2 A =
  is-equiv-has-inverse (Pr1 A) (issec-Pr1 {l2 = l2}) (isretr-Pr1 {l2 = l2})

equiv-Fib :
  {l1 : Level} (l2 : Level) (A : UU l1) → slice-UU (l1 ⊔ l2) A ≃ (A → UU (l1 ⊔ l2))
equiv-Fib l2 A = pair (Fib A) (is-equiv-Fib l2 A)

is-equiv-Pr1 :
  {l1 : Level} (l2 : Level) (A : UU l1) → is-equiv (Pr1 {l1 ⊔ l2} A)
is-equiv-Pr1 {l1} l2 A =
  is-equiv-has-inverse (Fib A) (isretr-Pr1 {l2 = l2}) (issec-Pr1 {l2 = l2})

equiv-Pr1 :
  {l1 : Level} (l2 : Level) (A : UU l1) → (A → UU (l1 ⊔ l2)) ≃ slice-UU (l1 ⊔ l2) A
equiv-Pr1 l2 A = pair (Pr1 A) (is-equiv-Pr1 l2 A)

-- Theorem 17.3.2

structure : {l1 l2 : Level} (P : UU l1 → UU l2) → UU (lsuc l1 ⊔ l2)
structure {l1} P = Σ (UU l1) P

fam-structure :
  {l1 l2 l3 : Level} (P : UU l1 → UU l2) (A : UU l3) → UU (lsuc l1 ⊔ l2 ⊔ l3)
fam-structure P A = A → structure P

structure-map :
  {l1 l2 l3 : Level} (P : UU (l1 ⊔ l2) → UU l3) {A : UU l1} {B : UU l2}
  (f : A → B) → UU (l2 ⊔ l3)
structure-map P {A} {B} f = (b : B) → P (fib f b)

hom-structure :
  {l1 l2 l3 : Level} (P : UU (l1 ⊔ l2) → UU l3) →
  UU l1 → UU l2 → UU (l1 ⊔ l2 ⊔ l3)
hom-structure P A B = Σ (A → B) (structure-map P)

slice-UU-structure :
  {l1 l2 : Level} (l : Level) (P : UU (l1 ⊔ l) → UU l2) (B : UU l1) →
  UU (l1 ⊔ l2 ⊔ lsuc l)
slice-UU-structure l P B = Σ (UU l) (λ A → hom-structure P A B)

equiv-Fib-structure :
  {l1 l3 : Level} (l : Level) (P : UU (l1 ⊔ l) → UU l3) (B : UU l1) →
  slice-UU-structure (l1 ⊔ l) P B ≃ fam-structure P B
equiv-Fib-structure {l1} {l3} l P B =
  ( ( equiv-inv-choice-∞ (λ x → P)) ∘e
    ( equiv-Σ
      ( λ C → (b : B) → P (C b))
      ( equiv-Fib l B)
      ( λ f → equiv-map-Π (λ b → equiv-id)))) ∘e
  ( inv-assoc-Σ (UU (l1 ⊔ l)) (λ A → A → B) (λ f → structure-map P (pr2 f)))

-- Corollary 17.3.3

slice-UU-emb : (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
slice-UU-emb l A = Σ (UU l) (λ X → X ↪ A)

equiv-Fib-Prop :
  (l : Level) {l1 : Level} (A : UU l1) →
  slice-UU-emb (l1 ⊔ l) A ≃ (A → UU-Prop (l1 ⊔ l))
equiv-Fib-Prop l A =
  ( equiv-Fib-structure l is-prop A) ∘e
  ( equiv-tot (λ X → equiv-tot equiv-is-prop-map-is-emb))

-- Remark 17.3.4

--------------------------------------------------------------------------------

-- Section 17.4 Classical mathematics with the univalence axiom

-- Proposition 17.4.1

ev-zero-equiv-Fin-two-ℕ :
  {l1 : Level} {X : UU l1} → (Fin two-ℕ ≃ X) → X
ev-zero-equiv-Fin-two-ℕ e = map-equiv e zero-Fin

inv-ev-zero-equiv-Fin-two-ℕ' :
  Fin two-ℕ → (Fin two-ℕ ≃ Fin two-ℕ)
inv-ev-zero-equiv-Fin-two-ℕ' (inl (inr star)) = equiv-id
inv-ev-zero-equiv-Fin-two-ℕ' (inr star) = equiv-succ-Fin

issec-inv-ev-zero-equiv-Fin-two-ℕ' :
  (ev-zero-equiv-Fin-two-ℕ ∘ inv-ev-zero-equiv-Fin-two-ℕ') ~ id
issec-inv-ev-zero-equiv-Fin-two-ℕ' (inl (inr star)) = refl
issec-inv-ev-zero-equiv-Fin-two-ℕ' (inr star) = refl

aux-isretr-inv-ev-zero-equiv-Fin-two-ℕ' :
  (e : Fin two-ℕ ≃ Fin two-ℕ) (x y : Fin two-ℕ) → Id (map-equiv e zero-Fin) x →
  Id (map-equiv e one-Fin) y → htpy-equiv (inv-ev-zero-equiv-Fin-two-ℕ' x) e
aux-isretr-inv-ev-zero-equiv-Fin-two-ℕ' e
  (inl (inr star)) (inl (inr star)) p q (inl (inr star)) = inv p
aux-isretr-inv-ev-zero-equiv-Fin-two-ℕ' e
  (inl (inr star)) (inl (inr star)) p q (inr star) =
  ex-falso (Eq-Fin-eq (is-injective-map-equiv e (p ∙ inv q)))
aux-isretr-inv-ev-zero-equiv-Fin-two-ℕ' e
  (inl (inr star)) (inr star) p q (inl (inr star)) = inv p
aux-isretr-inv-ev-zero-equiv-Fin-two-ℕ' e
  (inl (inr star)) (inr star) p q (inr star) = inv q
aux-isretr-inv-ev-zero-equiv-Fin-two-ℕ' e
  (inr star) (inl (inr star)) p q (inl (inr star)) = inv p
aux-isretr-inv-ev-zero-equiv-Fin-two-ℕ' e
  (inr star) (inl (inr star)) p q (inr star) = inv q
aux-isretr-inv-ev-zero-equiv-Fin-two-ℕ' e
  (inr star) (inr star) p q (inl (inr star)) =
  ex-falso (Eq-Fin-eq (is-injective-map-equiv e (p ∙ inv q)))
aux-isretr-inv-ev-zero-equiv-Fin-two-ℕ' e
  (inr star) (inr star) p q (inr star) =
  ex-falso (Eq-Fin-eq (is-injective-map-equiv e (p ∙ inv q)))

isretr-inv-ev-zero-equiv-Fin-two-ℕ' :
  (inv-ev-zero-equiv-Fin-two-ℕ' ∘ ev-zero-equiv-Fin-two-ℕ) ~ id
isretr-inv-ev-zero-equiv-Fin-two-ℕ' e =
  eq-htpy-equiv
    ( aux-isretr-inv-ev-zero-equiv-Fin-two-ℕ' e
      ( map-equiv e zero-Fin)
      ( map-equiv e one-Fin)
      ( refl)
      ( refl))

is-equiv-ev-zero-equiv-Fin-two-ℕ' :
  is-equiv (ev-zero-equiv-Fin-two-ℕ {lzero} {Fin two-ℕ})
is-equiv-ev-zero-equiv-Fin-two-ℕ' =
  is-equiv-has-inverse
    inv-ev-zero-equiv-Fin-two-ℕ'
    issec-inv-ev-zero-equiv-Fin-two-ℕ'
    isretr-inv-ev-zero-equiv-Fin-two-ℕ'

is-equiv-ev-zero-equiv-Fin-two-ℕ :
  {l1 : Level} {X : UU l1} → mere-equiv (Fin two-ℕ) X →
  is-equiv (ev-zero-equiv-Fin-two-ℕ {l1} {X})
is-equiv-ev-zero-equiv-Fin-two-ℕ {l1} {X} H =
  apply-universal-property-trunc-Prop H
    ( is-equiv-Prop (ev-zero-equiv-Fin-two-ℕ))
    ( λ α →
      is-equiv-left-factor'
        ( ev-zero-equiv-Fin-two-ℕ)
        ( map-equiv (equiv-postcomp-equiv α (Fin two-ℕ)))
        ( is-equiv-comp
          ( ( ev-zero-equiv-Fin-two-ℕ) ∘
            ( map-equiv (equiv-postcomp-equiv α (Fin two-ℕ))))
          ( map-equiv α)
          ( ev-zero-equiv-Fin-two-ℕ)
          ( refl-htpy)
          ( is-equiv-ev-zero-equiv-Fin-two-ℕ')
          ( is-equiv-map-equiv α))
        ( is-equiv-comp-equiv α (Fin two-ℕ)))

equiv-ev-zero-equiv-Fin-two-ℕ :
  {l1 : Level} {X : UU l1} → mere-equiv (Fin two-ℕ) X →
  (Fin two-ℕ ≃ X) ≃ X
equiv-ev-zero-equiv-Fin-two-ℕ e =
  pair ev-zero-equiv-Fin-two-ℕ (is-equiv-ev-zero-equiv-Fin-two-ℕ e)

is-contr-total-UU-Fin-Level-two-ℕ :
  {l : Level} → is-contr (Σ (UU-Fin-Level l two-ℕ) type-UU-Fin-Level)
is-contr-total-UU-Fin-Level-two-ℕ {l} =
  is-contr-equiv'
    ( Σ (UU-Fin-Level l two-ℕ) (λ X → raise-Fin l two-ℕ ≃ type-UU-Fin-Level X))
    ( equiv-tot
      ( λ X →
        ( equiv-ev-zero-equiv-Fin-two-ℕ (pr2 X)) ∘e
        ( equiv-precomp-equiv (equiv-raise-Fin l two-ℕ) (pr1 X))))
    ( is-contr-total-equiv-subuniverse
      ( mere-equiv-Prop (Fin two-ℕ))
      ( Fin-UU-Fin-Level l two-ℕ))

is-contr-total-UU-Fin-two-ℕ :
  is-contr (Σ (UU-Fin two-ℕ) (λ X → type-UU-Fin X))
is-contr-total-UU-Fin-two-ℕ = is-contr-total-UU-Fin-Level-two-ℕ

point-eq-UU-Fin-Level-two-ℕ :
  {l : Level} {X : UU-Fin-Level l two-ℕ} →
  Id (Fin-UU-Fin-Level l two-ℕ) X → type-UU-Fin-Level X
point-eq-UU-Fin-Level-two-ℕ refl = map-raise zero-Fin

is-equiv-point-eq-UU-Fin-Level-two-ℕ :
  {l : Level} (X : UU-Fin-Level l two-ℕ) →
  is-equiv (point-eq-UU-Fin-Level-two-ℕ {l} {X})
is-equiv-point-eq-UU-Fin-Level-two-ℕ {l} =
  fundamental-theorem-id
    ( Fin-UU-Fin-Level l two-ℕ)
    ( map-raise zero-Fin)
    ( is-contr-total-UU-Fin-Level-two-ℕ)
    ( λ X → point-eq-UU-Fin-Level-two-ℕ {l} {X})

equiv-point-eq-UU-Fin-Level-two-ℕ :
  {l : Level} {X : UU-Fin-Level l two-ℕ} →
  Id (Fin-UU-Fin-Level l two-ℕ) X ≃ type-UU-Fin-Level X
equiv-point-eq-UU-Fin-Level-two-ℕ {l} {X} =
  pair point-eq-UU-Fin-Level-two-ℕ (is-equiv-point-eq-UU-Fin-Level-two-ℕ X)

eq-point-UU-Fin-Level-two-ℕ :
  {l : Level} {X : UU-Fin-Level l two-ℕ} →
  type-UU-Fin-Level X → Id (Fin-UU-Fin-Level l two-ℕ) X
eq-point-UU-Fin-Level-two-ℕ =
  map-inv-equiv equiv-point-eq-UU-Fin-Level-two-ℕ

point-eq-UU-Fin-two-ℕ :
  {X : UU-Fin two-ℕ} → Id (Fin-UU-Fin two-ℕ) X → type-UU-Fin X
point-eq-UU-Fin-two-ℕ refl = zero-Fin

is-equiv-point-eq-UU-Fin-two-ℕ :
  (X : UU-Fin two-ℕ) → is-equiv (point-eq-UU-Fin-two-ℕ {X})
is-equiv-point-eq-UU-Fin-two-ℕ =
  fundamental-theorem-id
    ( Fin-UU-Fin two-ℕ)
    ( zero-Fin)
    ( is-contr-total-UU-Fin-two-ℕ)
    ( λ X → point-eq-UU-Fin-two-ℕ {X})

equiv-point-eq-UU-Fin-two-ℕ :
  {X : UU-Fin two-ℕ} → Id (Fin-UU-Fin two-ℕ) X ≃ type-UU-Fin X
equiv-point-eq-UU-Fin-two-ℕ {X} =
  pair point-eq-UU-Fin-two-ℕ (is-equiv-point-eq-UU-Fin-two-ℕ X)

eq-point-UU-Fin-two-ℕ :
  {X : UU-Fin two-ℕ} → type-UU-Fin X → Id (Fin-UU-Fin two-ℕ) X
eq-point-UU-Fin-two-ℕ {X} =
  map-inv-equiv equiv-point-eq-UU-Fin-two-ℕ

-- Corollary 17.4.2

no-section-type-UU-Fin-Level-two-ℕ :
  {l : Level} → ¬ ((X : UU-Fin-Level l two-ℕ) → type-UU-Fin-Level X)
no-section-type-UU-Fin-Level-two-ℕ {l} f =
  is-not-contractible-Fin two-ℕ
    ( Eq-ℕ-eq)
    ( is-contr-equiv
      ( Id (Fin-UU-Fin-Level l two-ℕ) (Fin-UU-Fin-Level l two-ℕ))
      ( ( inv-equiv equiv-point-eq-UU-Fin-Level-two-ℕ) ∘e
        ( equiv-raise-Fin l two-ℕ))
      ( is-prop-is-contr
        ( pair
          ( Fin-UU-Fin-Level l two-ℕ)
          ( λ X → eq-point-UU-Fin-Level-two-ℕ (f X)))
        ( Fin-UU-Fin-Level l two-ℕ)
        ( Fin-UU-Fin-Level l two-ℕ)))

no-section-type-UU-Fin-two-ℕ :
  ¬ ((X : UU-Fin two-ℕ) → type-UU-Fin X)
no-section-type-UU-Fin-two-ℕ f =
  no-section-type-UU-Fin-Level-two-ℕ f

-- Corollary 17.4.3

no-global-section :
  {l : Level} → ¬ ((X : UU l) → type-trunc-Prop X → X)
no-global-section f =
  no-section-type-UU-Fin-Level-two-ℕ
    ( λ X →
      f (pr1 X) (functor-trunc-Prop (λ e → map-equiv e zero-Fin) (pr2 X)))

-- Definition 17.4.4

AC : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
AC l1 l2 =
  (A : UU-Set l1) (B : type-Set A → UU-Set l2) →
  ((x : type-Set A) → type-trunc-Prop (type-Set (B x))) →
  type-trunc-Prop ((x : type-Set A) → type-Set (B x))

-- Theorem 17.4.5

is-not-decidable-type-UU-Fin-Level-two-ℕ :
  {l : Level} →
  ¬ ((X : UU-Fin-Level l two-ℕ) → is-decidable (type-UU-Fin-Level X))
is-not-decidable-type-UU-Fin-Level-two-ℕ {l} d =
  no-section-type-UU-Fin-Level-two-ℕ
    ( λ X →
      map-right-unit-law-coprod-is-empty
        ( pr1 X)
        ( ¬ (pr1 X))
        ( apply-universal-property-trunc-Prop
          ( pr2 X)
          ( dn-Prop' (pr1 X))
          ( λ e → intro-dn {l} (map-equiv e zero-Fin)))
        ( d X))

no-global-decidability :
  {l : Level} → ¬ ((X : UU l) → is-decidable X)
no-global-decidability {l} d =
  is-not-decidable-type-UU-Fin-Level-two-ℕ (λ X → d (pr1 X))

-- Definition 17.4.6

LEM : (l : Level) → UU (lsuc l)
LEM l = (P : UU-Prop l) → is-decidable (type-Prop P)

--------------------------------------------------------------------------------

-- Section 17.5 The binomial types

-- Definition 17.5.1

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

is-emb-map-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ↪d Y) →
  is-emb (map-decidable-emb e)
is-emb-map-decidable-emb e =
  is-emb-is-decidable-emb (is-decidable-emb-map-decidable-emb e)

is-decidable-map-map-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ↪d Y) →
  is-decidable-map (map-decidable-emb e)
is-decidable-map-map-decidable-emb e =
  is-decidable-map-is-decidable-emb (is-decidable-emb-map-decidable-emb e)

emb-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → X ↪d Y → X ↪ Y
emb-decidable-emb e = pair (map-decidable-emb e) (is-emb-map-decidable-emb e)

-- Bureaucracy

equiv-Fib-decidable-Prop :
  (l : Level) {l1 : Level} (A : UU l1) →
  Σ (UU (l1 ⊔ l)) (λ X → X ↪d A) ≃ (A → decidable-Prop (l1 ⊔ l))
equiv-Fib-decidable-Prop l A =
  ( equiv-Fib-structure l is-decidable-prop A) ∘e
  ( equiv-tot
    ( λ X →
      equiv-tot
        ( λ f →
          ( inv-equiv equiv-choice-∞) ∘e
          ( equiv-prod (equiv-is-prop-map-is-emb f) equiv-id))))

is-decidable-emb-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-equiv f → is-decidable-emb f
is-decidable-emb-is-equiv H =
  pair (is-emb-is-equiv H) (λ x → inl (center (is-contr-map-is-equiv H x)))

is-decidable-emb-id :
  {l1 : Level} {A : UU l1} → is-decidable-emb (id {A = A})
is-decidable-emb-id {l1} {A} = pair is-emb-id (λ x → inl (pair x refl))

decidable-emb-id :
  {l1 : Level} {A : UU l1} → A ↪d A
decidable-emb-id {l1} {A} = pair id is-decidable-emb-id

is-prop-is-decidable-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-prop (is-decidable-emb f)
is-prop-is-decidable-emb f =
  is-prop-is-inhabited
    ( λ H →
      is-prop-prod
        ( is-prop-is-emb f)
        ( is-prop-Π
          ( λ y → is-prop-is-decidable (is-prop-map-is-emb (pr1 H) y))))

fib-comp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (g : B → C) (f : A → B)
  (c : C) → fib (g ∘ f) c ≃ Σ (fib g c) (λ t → fib f (pr1 t))
fib-comp {A = A} {B} {C} g f c =
  ( equiv-Σ-swap A (fib g c) (λ a u → Id (f a) (pr1 u))) ∘e
  ( equiv-tot
    ( λ a →
      ( inv-assoc-Σ B (λ b → Id (g b) c) (λ u → Id (f a) (pr1 u))) ∘e
      ( ( equiv-tot (λ b → commutative-prod)) ∘e
        ( ( assoc-Σ B (Id (f a)) ( λ u → Id (g (pr1 u)) c)) ∘e
          ( inv-equiv
            ( left-unit-law-Σ-is-contr
              ( is-contr-total-path (f a))
              ( pair (f a) refl)))))))

is-decidable-emb-comp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {g : B → C}
  {f : A → B} →
  is-decidable-emb f → is-decidable-emb g → is-decidable-emb (g ∘ f)
is-decidable-emb-comp {g = g} {f} H K =
  pair
    ( is-emb-comp' _ _ (pr1 K) (pr1 H))
    ( λ x →
      ind-coprod
        ( λ t → is-decidable (fib (g ∘ f) x))
        ( λ u →
          is-decidable-equiv
            ( fib-comp g f x)
            ( is-decidable-equiv
              ( left-unit-law-Σ-is-contr
                ( is-proof-irrelevant-is-prop
                  ( is-prop-map-is-emb (is-emb-is-decidable-emb K) x)
                  ( u))
                ( u))
              ( is-decidable-map-is-decidable-emb H (pr1 u))))
        ( λ α → inr (λ t → α (pair (f (pr1 t)) (pr2 t))))
        ( pr2 K x))

is-decidable-emb-htpy :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} →
  f ~ g → is-decidable-emb g → is-decidable-emb f
is-decidable-emb-htpy {f = f} {g} H K =
  pair ( is-emb-htpy f g H (is-emb-is-decidable-emb K))
       ( λ b →
         is-decidable-equiv
           ( equiv-tot (λ a → equiv-concat (inv (H a)) b))
           ( is-decidable-map-is-decidable-emb K b))

htpy-decidable-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A ↪d B) → UU (l1 ⊔ l2)
htpy-decidable-emb f g = map-decidable-emb f ~ map-decidable-emb g

refl-htpy-decidable-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↪d B) → htpy-decidable-emb f f
refl-htpy-decidable-emb f = refl-htpy

htpy-eq-decidable-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A ↪d B) →
  Id f g → htpy-decidable-emb f g
htpy-eq-decidable-emb f .f refl = refl-htpy-decidable-emb f

is-contr-total-htpy-decidable-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↪d B) →
  is-contr (Σ (A ↪d B) (htpy-decidable-emb f))
is-contr-total-htpy-decidable-emb f =
  is-contr-total-Eq-substructure
    ( is-contr-total-htpy (map-decidable-emb f))
    ( is-prop-is-decidable-emb)
    ( map-decidable-emb f)
    ( refl-htpy)
    ( is-decidable-emb-map-decidable-emb f)

is-equiv-htpy-eq-decidable-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A ↪d B) →
  is-equiv (htpy-eq-decidable-emb f g)
is-equiv-htpy-eq-decidable-emb f =
  fundamental-theorem-id f
    ( refl-htpy-decidable-emb f)
    ( is-contr-total-htpy-decidable-emb f)
    ( htpy-eq-decidable-emb f)

eq-htpy-decidable-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A ↪d B} →
  htpy-decidable-emb f g → Id f g
eq-htpy-decidable-emb {f = f} {g} =
  map-inv-is-equiv (is-equiv-htpy-eq-decidable-emb f g)

equiv-precomp-decidable-emb-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  (C : UU l3) → (B ↪d C) ≃ (A ↪d C)
equiv-precomp-decidable-emb-equiv e C =
  equiv-Σ
    ( is-decidable-emb)
    ( equiv-precomp e C)
    ( λ g →
      equiv-prop
        ( is-prop-is-decidable-emb g)
        ( is-prop-is-decidable-emb (g ∘ map-equiv e))
        ( is-decidable-emb-comp (is-decidable-emb-is-equiv (pr2 e)))
        ( λ d →
          is-decidable-emb-htpy
            ( λ b → ap g (inv (issec-map-inv-equiv e b)))
            ( is-decidable-emb-comp
              ( is-decidable-emb-is-equiv (is-equiv-map-inv-equiv e))
              ( d)))) 

-- Definition 17.5.2

-- We first define more general binomial types with an extra universe level.

binomial-type-Level :
  (l : Level) {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (lsuc l ⊔ l1 ⊔ l2)
binomial-type-Level l X Y =
  Σ (component-UU-Level l Y) (λ Z → type-component-UU-Level Z ↪d X)

type-binomial-type-Level :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} → binomial-type-Level l3 X Y → UU l3
type-binomial-type-Level Z = type-component-UU-Level (pr1 Z)

mere-equiv-binomial-type-Level :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (Z : binomial-type-Level l3 X Y) →
  mere-equiv Y (type-binomial-type-Level Z)
mere-equiv-binomial-type-Level Z = mere-equiv-component-UU-Level (pr1 Z)

decidable-emb-binomial-type-Level :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (Z : binomial-type-Level l3 X Y) →
  type-binomial-type-Level Z ↪d X
decidable-emb-binomial-type-Level Z = pr2 Z

map-decidable-emb-binomial-type-Level :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (Z : binomial-type-Level l3 X Y) →
  type-binomial-type-Level Z → X
map-decidable-emb-binomial-type-Level Z =
  map-decidable-emb (decidable-emb-binomial-type-Level Z)

is-emb-map-emb-binomial-type-Level :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (Z : binomial-type-Level l3 X Y) →
  is-emb (map-decidable-emb-binomial-type-Level Z)
is-emb-map-emb-binomial-type-Level Z =
  is-emb-map-decidable-emb (decidable-emb-binomial-type-Level Z)

-- We now define the standard binomial types

binomial-type : {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (lsuc (l1 ⊔ l2))
binomial-type {l1} {l2} X Y = binomial-type-Level (l1 ⊔ l2) X Y

type-binomial-type :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → binomial-type X Y → UU (l1 ⊔ l2)
type-binomial-type Z = type-component-UU-Level (pr1 Z)

mere-equiv-binomial-type :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (Z : binomial-type X Y) →
  mere-equiv Y (type-binomial-type Z)
mere-equiv-binomial-type Z = mere-equiv-component-UU-Level (pr1 Z)

decidable-emb-binomial-type :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (Z : binomial-type X Y) →
  type-binomial-type Z ↪d X
decidable-emb-binomial-type Z = pr2 Z

map-decidable-emb-binomial-type :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (Z : binomial-type X Y) →
  type-binomial-type Z → X
map-decidable-emb-binomial-type Z =
  map-decidable-emb (decidable-emb-binomial-type Z)

is-emb-map-emb-binomial-type :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (Z : binomial-type X Y) →
  is-emb (map-decidable-emb-binomial-type Z)
is-emb-map-emb-binomial-type Z =
  is-emb-map-decidable-emb (decidable-emb-binomial-type Z)

-- Remark 17.5.4

binomial-type-Level' :
  (l : Level) {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (lsuc l ⊔ l1 ⊔ l2)
binomial-type-Level' l A B =
  Σ ( A → decidable-Prop l)
    ( λ P → mere-equiv B (Σ A (λ x → type-decidable-Prop (P x))))

equiv-binomial-type-Level :
  (l : Level) {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  binomial-type-Level (l1 ⊔ l) A B ≃ binomial-type-Level' (l1 ⊔ l) A B
equiv-binomial-type-Level l {l1} {l2} A B =
  ( ( ( equiv-Σ
        ( λ P → mere-equiv B (Σ A (λ x → type-decidable-Prop (P x))))
        ( equiv-Fib-decidable-Prop l A)
        ( λ e →
          equiv-trunc-Prop
            ( equiv-postcomp-equiv
              ( inv-equiv (equiv-total-fib (pr1 (pr2 e)))) B))) ∘e
      ( inv-assoc-Σ
        ( UU (l1 ⊔ l))
        ( λ X → X ↪d A)
        ( λ X → mere-equiv B (pr1 X)))) ∘e
    ( equiv-tot (λ X → commutative-prod))) ∘e
  ( assoc-Σ (UU (l1 ⊔ l)) (λ X → mere-equiv B X) (λ X → (pr1 X) ↪d A))

binomial-type' :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (lsuc (l1 ⊔ l2))
binomial-type' {l1} {l2} A B = binomial-type-Level' (l1 ⊔ l2) A B

equiv-binomial-type :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  binomial-type A B ≃ binomial-type' A B
equiv-binomial-type {l1} {l2} A B =
  equiv-binomial-type-Level (l1 ⊔ l2) A B

-- Proposition 17.5.7

is-contr-component-UU-Level-empty :
  (l : Level) → is-contr (component-UU-Level l empty)
is-contr-component-UU-Level-empty l =
  pair
    ( Fin-UU-Fin-Level l zero-ℕ)
    ( λ X →
      eq-equiv-subuniverse
        ( mere-equiv-Prop empty)
        ( equiv-is-empty
          ( map-inv-equiv (equiv-raise l empty))
          ( λ x →
            apply-universal-property-trunc-Prop
              ( pr2 X)
              ( empty-Prop)
              ( λ e → map-inv-equiv e x))))

is-contr-component-UU-empty : is-contr (component-UU empty)
is-contr-component-UU-empty =
  is-contr-component-UU-Level-empty lzero

is-decidable-emb-ex-falso :
  {l : Level} {X : UU l} → is-decidable-emb (ex-falso {l} {X})
is-decidable-emb-ex-falso {l} {X} =
  pair (is-emb-ex-falso X) (λ x → inr pr1)

binomial-type-over-empty :
  {l : Level} {X : UU l} → is-contr (binomial-type X empty)
binomial-type-over-empty {l} {X} =
  is-contr-equiv
    ( raise-empty l ↪d X)
    ( left-unit-law-Σ-is-contr
      ( is-contr-component-UU-Level-empty l)
      ( Fin-UU-Fin-Level l zero-ℕ))
    ( is-contr-equiv
      ( empty ↪d X)
      ( equiv-precomp-decidable-emb-equiv (equiv-raise-empty l) X)
      ( is-contr-equiv
        ( is-decidable-emb ex-falso)
        ( left-unit-law-Σ-is-contr (universal-property-empty' X) ex-falso)
        ( is-proof-irrelevant-is-prop
          ( is-prop-is-decidable-emb ex-falso)
          ( is-decidable-emb-ex-falso))))

--------------------------------------------------------------------------------

-- Exercises

-- Exercise 17.1

tr-equiv-eq-ap : {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {x y : A}
  (p : Id x y) → (map-equiv (equiv-eq (ap B p))) ~ tr B p
tr-equiv-eq-ap refl = refl-htpy

-- Exercise 17.2

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

{-
is-emb-raise :
  (l1 l2 : Level) → is-emb (raise l2 {l1})
is-emb-raise l1 l2 =
  is-emb-is-prop-map (λ X → is-prop-equiv (is-small l1 X) (equiv-tot (λ Y → (equiv-inv-equiv ∘e {!equiv-precomp-equiv (equiv-raise l2 Y) X!}) ∘e equiv-univalence)) {!!})
-}
-- Exercise 17.3

subuniverse-is-contr :
  {i : Level} → subuniverse i i
subuniverse-is-contr {i} = is-contr-Prop

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
    eq-equiv-subuniverse subuniverse-is-contr
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

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------

