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

decidable-Prop :
  (l : Level) → UU (lsuc l)
decidable-Prop l = Σ (UU-Prop l) (λ P → is-decidable (pr1 P))

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
  ( equiv-coprod
    ( equiv-is-contr
      ( is-contr-total-true-Prop)
      ( is-contr-Fin-one-ℕ))
    ( equiv-is-contr
      ( is-contr-total-false-Prop)
      ( is-contr-unit))) ∘e
  ( left-distributive-Σ-coprod
    ( UU-Prop l1)
    ( λ P → type-Prop P)
    ( λ P → type-Prop (neg-Prop P)))

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
  pair
    ( pair (Id i j) (is-set-Fin n i j))
    ( has-decidable-equality-Fin i j)

-- Subuniverses

is-subuniverse :
  {l1 l2 : Level} (P : UU l1 → UU l2) → UU ((lsuc l1) ⊔ l2)
is-subuniverse P = is-subtype P

subuniverse :
  (l1 l2 : Level) → UU ((lsuc l1) ⊔ (lsuc l2))
subuniverse l1 l2 = UU l1 → UU-Prop l2

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
    is-contr-total-Eq-substructure (is-contr-total-equiv X) {!!} X equiv-id p

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

center-total-UU-Fin-two-ℕ : Σ (UU-Fin two-ℕ) type-UU-Fin
center-total-UU-Fin-two-ℕ =
  pair (Fin-UU-Fin two-ℕ) zero-Fin

ev-zero-equiv-Fin-two-ℕ :
  {l1 : Level} {X : UU l1} → (Fin two-ℕ ≃ X) → X
ev-zero-equiv-Fin-two-ℕ e = map-equiv e zero-Fin

is-equiv-ev-equiv-Fin-two-ℕ' :
  is-equiv (ev-zero-equiv-Fin-two-ℕ {lzero} {Fin two-ℕ})
is-equiv-ev-equiv-Fin-two-ℕ' = {!!}

is-equiv-ev-zero-Fin-two-ℕ :
  {l1 : Level} {X : UU l1} → mere-equiv (Fin two-ℕ) X →
  is-equiv (ev-zero-equiv-Fin-two-ℕ {l1} {X})
is-equiv-ev-zero-Fin-two-ℕ {l1} {X} H =
  apply-universal-property-trunc-Prop H
    ( is-equiv-Prop (ev-zero-equiv-Fin-two-ℕ))
    ( λ α →
      is-equiv-left-factor'
        ( ev-zero-equiv-Fin-two-ℕ)
        {! map-equiv (equiv-postcomp-equiv (Fin two-ℕ) α)!}
        {! !}
        {!!})

is-contr-total-UU-Fin-two-ℕ :
  is-contr (Σ (UU-Fin two-ℕ) (λ X → type-UU-Fin X))
is-contr-total-UU-Fin-two-ℕ =
  is-contr-equiv
    ( Σ (UU-Fin two-ℕ) (λ X → Fin two-ℕ ≃ type-UU-Fin X))
    ( equiv-tot
      ( λ X → {!!}))
    ( is-contr-total-equiv-subuniverse
      ( mere-equiv-Prop (Fin two-ℕ))
      ( Fin-UU-Fin two-ℕ))

{- Not every type is decidable. -}

simplify-not-all-2-element-types-decidable :
  {l : Level} →
  ((X : UU l) (p : type-trunc-Prop (bool ≃ X)) → is-decidable X) →
  ((X : UU l) (p : type-trunc-Prop (bool ≃ X)) → X)
simplify-not-all-2-element-types-decidable d X p =
  map-right-unit-law-coprod-is-empty X (¬ X)
    ( apply-universal-property-trunc-Prop p
      ( dn-Prop' X)
      ( λ e → intro-dn (map-equiv e true)))
    ( d X p)

--------------------------------------------------------------------------------

-- Section 17.5 Resizing axioms

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

choose-UU-Level :
  (l : Level) {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (lsuc l ⊔ l1 ⊔ l2)
choose-UU-Level l X Y =
  Σ (component-UU-Level l Y) (λ Z → type-component-UU-Level Z ↪d X)

type-choose-UU-Level :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} → choose-UU-Level l3 X Y → UU l3
type-choose-UU-Level Z = type-component-UU-Level (pr1 Z)

mere-equiv-choose-UU-Level :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (Z : choose-UU-Level l3 X Y) →
  mere-equiv Y (type-choose-UU-Level Z)
mere-equiv-choose-UU-Level Z = mere-equiv-component-UU-Level (pr1 Z)

decidable-emb-choose-UU-Level :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (Z : choose-UU-Level l3 X Y) →
  type-choose-UU-Level Z ↪d X
decidable-emb-choose-UU-Level Z = pr2 Z

map-decidable-emb-choose-UU-Level :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (Z : choose-UU-Level l3 X Y) →
  type-choose-UU-Level Z → X
map-decidable-emb-choose-UU-Level Z =
  map-decidable-emb (decidable-emb-choose-UU-Level Z)

is-emb-map-emb-choose-UU-Level :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (Z : choose-UU-Level l3 X Y) →
  is-emb (map-decidable-emb-choose-UU-Level Z)
is-emb-map-emb-choose-UU-Level Z =
  is-emb-map-decidable-emb (decidable-emb-choose-UU-Level Z)

_choose-UU_ : {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (l1 ⊔ lsuc l2)
_choose-UU_ {l1} {l2} X Y = choose-UU-Level l2 X Y

