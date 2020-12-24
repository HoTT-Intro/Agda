{-# OPTIONS --without-K --exact-split #-}

module book.14-propositional-truncation where

import book.13-function-extensionality-solutions
open book.13-function-extensionality-solutions public

--------------------------------------------------------------------------------

-- Section 14 Propositional truncations and the image of a map

--------------------------------------------------------------------------------

-- Section 14.1 Propositional truncations

-- Definition 14.1.1

precomp-Prop :
  { l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) →
  (A → type-Prop P) → (Q : UU-Prop l3) →
  (type-hom-Prop P Q) → (A → type-Prop Q)
precomp-Prop P f Q g = g ∘ f

is-propositional-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1} (P : UU-Prop l2) →
  ( A → type-Prop P) → UU (lsuc l ⊔ l1 ⊔ l2)
is-propositional-truncation l P f =
  (Q : UU-Prop l) → is-equiv (precomp-Prop P f Q)

universal-property-propositional-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1}
  (P : UU-Prop l2) (f : A → type-Prop P) → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-propositional-truncation l {A = A} P f =
  (Q : UU-Prop l) (g : A → type-Prop Q) →
  is-contr (Σ (type-hom-Prop P Q) (λ h → (h ∘ f) ~  g))

-- Some unnumbered remarks after Definition 14.1.1

universal-property-is-propositional-truncation :
  (l : Level) {l1 l2 : Level} {A : UU l1}
  (P : UU-Prop l2) (f : A → type-Prop P) →
  is-propositional-truncation l P f →
  universal-property-propositional-truncation l P f
universal-property-is-propositional-truncation l P f is-ptr-f Q g =
  is-contr-equiv'
    ( Σ (type-hom-Prop P Q) (λ h → Id (h ∘ f) g))
    ( equiv-tot (λ h → equiv-funext))
    ( is-contr-map-is-equiv (is-ptr-f Q) g)

map-is-propositional-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (f : A → type-Prop P) →
  ({l : Level} → is-propositional-truncation l P f) →
  (Q : UU-Prop l3) (g : A → type-Prop Q) → type-hom-Prop P Q
map-is-propositional-truncation P f is-ptr-f Q g =
  pr1
    ( center
      ( universal-property-is-propositional-truncation _ P f is-ptr-f Q g))

htpy-is-propositional-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (f : A → type-Prop P) →
  (is-ptr-f : {l : Level} → is-propositional-truncation l P f) →
  (Q : UU-Prop l3) (g : A → type-Prop Q) →
  ((map-is-propositional-truncation P f is-ptr-f Q g) ∘ f) ~ g
htpy-is-propositional-truncation P f is-ptr-f Q g =
  pr2
    ( center
      ( universal-property-is-propositional-truncation _ P f is-ptr-f Q g))

is-propositional-truncation-universal-property :
  (l : Level) {l1 l2 : Level} {A : UU l1}
  (P : UU-Prop l2) (f : A → type-Prop P) →
  universal-property-propositional-truncation l P f →
  is-propositional-truncation l P f
is-propositional-truncation-universal-property l P f up-f Q =
  is-equiv-is-contr-map
    ( λ g → is-contr-equiv
      ( Σ (type-hom-Prop P Q) (λ h → (h ∘ f) ~ g))
      ( equiv-tot (λ h → equiv-funext))
      ( up-f Q g))

-- Remark 14.1.2

extension-property-propositional-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1} (P : UU-Prop l2) →
  ( A → type-Prop P) → UU (lsuc l ⊔ l1 ⊔ l2)
extension-property-propositional-truncation l {A = A} P f =
  (Q : UU-Prop l) → (A → type-Prop Q) → (type-hom-Prop P Q)

is-propositional-truncation-extension-property :
  { l1 l2 : Level} {A : UU l1} (P : UU-Prop l2)
  ( f : A → type-Prop P) →
  ( (l : Level) → extension-property-propositional-truncation l P f) →
  ( (l : Level) → is-propositional-truncation l P f)
is-propositional-truncation-extension-property P f up-P l Q =
  is-equiv-is-prop
    ( is-prop-Π (λ x → is-prop-type-Prop Q))
    ( is-prop-Π (λ x → is-prop-type-Prop Q))
    ( up-P l Q)

-- Example 14.1.3

is-propositional-truncation-terminal-map :
  { l1 : Level} (A : UU l1) (a : A)
  ( l : Level) → is-propositional-truncation l unit-Prop (terminal-map {A = A})
is-propositional-truncation-terminal-map A a =
  is-propositional-truncation-extension-property
    ( unit-Prop)
    ( terminal-map)
    ( λ l P f → const unit (type-Prop P) (f a))

-- Example 14.1.4

is-propositional-truncation-id :
  { l1 : Level} (P : UU-Prop l1) →
  ( l : Level) → is-propositional-truncation l P id
is-propositional-truncation-id P l Q = is-equiv-id

is-propositional-truncation-map-equiv :
  { l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) (e : equiv-Prop P Q) →
  ( l : Level) → is-propositional-truncation l Q (map-equiv e)
is-propositional-truncation-map-equiv P Q e l R =
  is-equiv-precomp-is-equiv (map-equiv e) (is-equiv-map-equiv e) (type-Prop R)

-- Proposition 14.1.5

abstract
  is-equiv-is-equiv-precomp-Prop :
    {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) (f : type-hom-Prop P Q) →
    ((l : Level) (R : UU-Prop l) →
    is-equiv (precomp-Prop Q f R)) → is-equiv f
  is-equiv-is-equiv-precomp-Prop P Q f is-equiv-precomp-f =
    is-equiv-is-equiv-precomp-subuniverse id (λ l → is-prop) P Q f
      is-equiv-precomp-f

triangle-3-for-2-is-ptruncation :
  {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (P' : UU-Prop l3)
  (f : A → type-Prop P) (f' : A → type-Prop P')
  (h : type-hom-Prop P P') (H : (h ∘ f) ~ f') →
  {l : Level} (Q : UU-Prop l) →
  ( precomp-Prop P' f' Q) ~
  ( (precomp-Prop P f Q) ∘ (precomp h (type-Prop Q)))
triangle-3-for-2-is-ptruncation P P' f f' h H Q g =
  eq-htpy (λ p → inv (ap g (H p)))

is-equiv-is-ptruncation-is-ptruncation :
  {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (P' : UU-Prop l3)
  (f : A → type-Prop P) (f' : A → type-Prop P')
  (h : type-hom-Prop P P') (H : (h ∘ f) ~ f') →
  ((l : Level) → is-propositional-truncation l P f) →
  ((l : Level) → is-propositional-truncation l P' f') →
  is-equiv h
is-equiv-is-ptruncation-is-ptruncation P P' f f' h H is-ptr-P is-ptr-P' =
  is-equiv-is-equiv-precomp-Prop P P' h
    ( λ l Q →
      is-equiv-right-factor
        ( precomp-Prop P' f' Q)
        ( precomp-Prop P f Q)
        ( precomp h (type-Prop Q))
        ( triangle-3-for-2-is-ptruncation P P' f f' h H Q)
        ( is-ptr-P l Q)
        ( is-ptr-P' l Q))

is-ptruncation-is-ptruncation-is-equiv :
  {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (P' : UU-Prop l3)
  (f : A → type-Prop P) (f' : A → type-Prop P')
  (h : type-hom-Prop P P') (H : (h ∘ f) ~ f') →
  is-equiv h →
  ((l : Level) → is-propositional-truncation l P f) →
  ((l : Level) → is-propositional-truncation l P' f')
is-ptruncation-is-ptruncation-is-equiv P P' f f' h H is-equiv-h is-ptr-f l Q =
  is-equiv-comp
    ( precomp-Prop P' f' Q)
    ( precomp-Prop P f Q)
    ( precomp h (type-Prop Q))
    ( triangle-3-for-2-is-ptruncation P P' f f' h H Q)
    ( is-equiv-precomp-is-equiv h is-equiv-h (type-Prop Q))
    ( is-ptr-f l Q)

is-ptruncation-is-equiv-is-ptruncation :
  {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (P' : UU-Prop l3)
  (f : A → type-Prop P) (f' : A → type-Prop P')
  (h : type-hom-Prop P P') (H : (h ∘ f) ~ f') →
  ((l : Level) → is-propositional-truncation l P' f') →
  is-equiv h →
  ((l : Level) → is-propositional-truncation l P f)
is-ptruncation-is-equiv-is-ptruncation P P' f f' h H is-ptr-f' is-equiv-h l Q =
  is-equiv-left-factor
    ( precomp-Prop P' f' Q)
    ( precomp-Prop P f Q)
    ( precomp h (type-Prop Q))
    ( triangle-3-for-2-is-ptruncation P P' f f' h H Q)
    ( is-ptr-f' l Q)
    ( is-equiv-precomp-is-equiv h is-equiv-h (type-Prop Q))

-- Corollary 14.1.6

is-uniquely-unique-propositional-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (P' : UU-Prop l3)
  (f : A → type-Prop P) (f' : A → type-Prop P') →
  ({l : Level} → is-propositional-truncation l P f) →
  ({l : Level} → is-propositional-truncation l P' f') →
  is-contr (Σ (equiv-Prop P P') (λ e → (map-equiv e ∘ f) ~ f'))
is-uniquely-unique-propositional-truncation P P' f f' is-ptr-f is-ptr-f' =
  is-contr-total-Eq-substructure
    ( universal-property-is-propositional-truncation _ P f is-ptr-f P' f')
    ( is-subtype-is-equiv)
    ( map-is-propositional-truncation P f is-ptr-f P' f')
    ( htpy-is-propositional-truncation P f is-ptr-f P' f')
    ( is-equiv-is-ptruncation-is-ptruncation  P P' f f'
      ( map-is-propositional-truncation P f is-ptr-f P' f')
      ( htpy-is-propositional-truncation P f is-ptr-f P' f')
      ( λ l → is-ptr-f)
      ( λ l → is-ptr-f'))

-- Axiom 14.1.8

postulate type-trunc-Prop : {l : Level} → UU l → UU l

postulate is-prop-type-trunc-Prop : {l : Level} {A : UU l} → is-prop (type-trunc-Prop A)

trunc-Prop : {l : Level} → UU l → UU-Prop l
trunc-Prop A = pair (type-trunc-Prop A) is-prop-type-trunc-Prop

postulate unit-trunc-Prop : {l : Level} {A : UU l} → A → type-Prop (trunc-Prop A)

postulate is-propositional-truncation-trunc-Prop : {l1 l2 : Level} (A : UU l1) → is-propositional-truncation l2 (trunc-Prop A) unit-trunc-Prop

universal-property-trunc-Prop : {l1 l2 : Level} (A : UU l1) →
  universal-property-propositional-truncation l2
    ( trunc-Prop A)
    ( unit-trunc-Prop)
universal-property-trunc-Prop A =
  universal-property-is-propositional-truncation _
    ( trunc-Prop A)
    ( unit-trunc-Prop)
    ( is-propositional-truncation-trunc-Prop A)

map-universal-property-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} (P : UU-Prop l2) →
  (A → type-Prop P) → type-hom-Prop (trunc-Prop A) P
map-universal-property-trunc-Prop {A = A} P f =
  map-is-propositional-truncation
    ( trunc-Prop A)
    ( unit-trunc-Prop)
    ( is-propositional-truncation-trunc-Prop A)
    ( P)
    ( f)

apply-universal-property-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} (t : type-trunc-Prop A) (P : UU-Prop l2) →
  (A → type-Prop P) → type-Prop P
apply-universal-property-trunc-Prop t P f =
  map-universal-property-trunc-Prop P f t

-- Proposition 14.1.9

unique-functor-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-contr
    ( Σ ( type-hom-Prop (trunc-Prop A) (trunc-Prop B))
        ( λ h → (h ∘ unit-trunc-Prop) ~ (unit-trunc-Prop ∘ f)))
unique-functor-trunc-Prop {l1} {l2} {A} {B} f =
  universal-property-trunc-Prop A (trunc-Prop B) (unit-trunc-Prop ∘ f)

functor-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A → B) → type-hom-Prop (trunc-Prop A) (trunc-Prop B)
functor-trunc-Prop f =
  pr1 (center (unique-functor-trunc-Prop f))

htpy-functor-trunc-Prop :
  { l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  ( (functor-trunc-Prop f) ∘ unit-trunc-Prop) ~ (unit-trunc-Prop ∘ f)
htpy-functor-trunc-Prop f =
  pr2 (center (unique-functor-trunc-Prop f))

htpy-uniqueness-functor-trunc-Prop :
  { l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  ( h : type-hom-Prop (trunc-Prop A) (trunc-Prop B)) →
  ( ( h ∘ unit-trunc-Prop) ~ (unit-trunc-Prop ∘ f)) →
  (functor-trunc-Prop f) ~ h
htpy-uniqueness-functor-trunc-Prop f h H =
  htpy-eq (ap pr1 (contraction (unique-functor-trunc-Prop f) (pair h H)))

id-functor-trunc-Prop :
  { l1 : Level} {A : UU l1} → functor-trunc-Prop (id {A = A}) ~ id
id-functor-trunc-Prop {l1} {A} =
  htpy-uniqueness-functor-trunc-Prop id id refl-htpy

comp-functor-trunc-Prop :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  ( g : B → C) (f : A → B) →
  ( functor-trunc-Prop (g ∘ f)) ~
  ( (functor-trunc-Prop g) ∘ (functor-trunc-Prop f))
comp-functor-trunc-Prop g f =
  htpy-uniqueness-functor-trunc-Prop
    ( g ∘ f)
    ( (functor-trunc-Prop g) ∘ (functor-trunc-Prop f))
    ( ( (functor-trunc-Prop g) ·l (htpy-functor-trunc-Prop f)) ∙h
      ( ( htpy-functor-trunc-Prop g) ·r f))

map-equiv-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → type-trunc-Prop A → type-trunc-Prop B
map-equiv-trunc-Prop e = functor-trunc-Prop (map-equiv e)

map-inv-equiv-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → type-trunc-Prop B → type-trunc-Prop A
map-inv-equiv-trunc-Prop e = map-equiv-trunc-Prop (inv-equiv e)

equiv-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → (type-trunc-Prop A ≃ type-trunc-Prop B)
equiv-trunc-Prop e =
  pair
    ( map-equiv-trunc-Prop e)
    ( is-equiv-is-prop
      ( is-prop-type-trunc-Prop)
      ( is-prop-type-trunc-Prop)
      ( map-inv-equiv-trunc-Prop e))

-- Definition 14.1.9

dependent-universal-property-propositional-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1}
  ( P : UU-Prop l2) (f : A → type-Prop P) → UU (lsuc l ⊔ l1 ⊔ l2)
dependent-universal-property-propositional-truncation l {l1} {l2} {A} P f =
  ( Q : type-Prop P → UU-Prop l) → is-equiv (precomp-Π f (type-Prop ∘ Q))

-- Theorem 14.2.2

abstract
  dependent-universal-property-is-propositional-truncation :
    { l1 l2 : Level} {A : UU l1} (P : UU-Prop l2) (f : A → type-Prop P) →
    ( {l : Level} → is-propositional-truncation l P f) →
    ( {l : Level} → dependent-universal-property-propositional-truncation l P f)
  dependent-universal-property-is-propositional-truncation
    {l1} {l2} {A} P f is-ptr-f Q =
    is-fiberwise-equiv-is-equiv-map-Σ
      ( λ (g : A → type-Prop P) → (x : A) → type-Prop (Q (g x)))
      ( precomp f (type-Prop P))
      ( λ h → precomp-Π f (λ p → type-Prop (Q (h p))))
      ( is-ptr-f P)
      ( is-equiv-top-is-equiv-bottom-square
        ( inv-choice-∞
          { C = λ (x : type-Prop P) (p : type-Prop P) → type-Prop (Q p)})
        ( inv-choice-∞
          { C = λ (x : A) (p : type-Prop P) → type-Prop (Q p)})
        ( map-Σ
          ( λ (g : A → type-Prop P) → (x : A) → type-Prop (Q (g x)))
          ( precomp f (type-Prop P))
          ( λ h → precomp-Π f (λ p → type-Prop (Q (h p)))))
        ( precomp f (Σ (type-Prop P) (λ p → type-Prop (Q p))))
        ( ind-Σ (λ h h' → refl))
        ( is-equiv-inv-choice-∞)
        ( is-equiv-inv-choice-∞)
        ( is-ptr-f (Σ-Prop P Q)))
      ( id {A = type-Prop P})

dependent-universal-property-trunc-Prop :
  {l l1 : Level} {A : UU l1} →
  dependent-universal-property-propositional-truncation l
    ( trunc-Prop A)
    ( unit-trunc-Prop)
dependent-universal-property-trunc-Prop {A = A} =
  dependent-universal-property-is-propositional-truncation
    ( trunc-Prop A)
    ( unit-trunc-Prop)
    ( is-propositional-truncation-trunc-Prop A)

equiv-dependent-universal-property-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} (P : type-trunc-Prop A → UU-Prop l2) →
  (((y : type-trunc-Prop A) → type-Prop (P y)) ≃
  ((x : A) → type-Prop (P (unit-trunc-Prop x))))
equiv-dependent-universal-property-trunc-Prop P =
  pair
    ( precomp-Π unit-trunc-Prop (type-Prop ∘ P))
    ( dependent-universal-property-trunc-Prop P)

ind-trunc-Prop :
  {l l1 : Level} {A : UU l1} (P : type-trunc-Prop A → UU-Prop l) →
  (( x : A) → type-Prop (P (unit-trunc-Prop x))) →
  (( y : type-trunc-Prop A) → type-Prop (P y))
ind-trunc-Prop {l} {l1} {A} P =
  map-inv-is-equiv (dependent-universal-property-trunc-Prop P)

comp-trunc-Prop :
  {l l1 : Level} {A : UU l1} (P : type-trunc-Prop A → UU-Prop l) →
  ((precomp-Π unit-trunc-Prop (type-Prop ∘ P)) ∘ ind-trunc-Prop P) ~ id
comp-trunc-Prop P =
  issec-map-inv-is-equiv (dependent-universal-property-trunc-Prop P)

abstract
  is-propositional-truncation-dependent-universal-property :
    { l1 l2 : Level} {A : UU l1} (P : UU-Prop l2) (f : A → type-Prop P) →
    ( {l : Level} →
      dependent-universal-property-propositional-truncation l P f) →
    ( {l : Level} → is-propositional-truncation l P f)
  is-propositional-truncation-dependent-universal-property P f dup-f Q =
    dup-f (λ p → Q)

--------------------------------------------------------------------------------

-- Section 14.3 Propositional truncations as higher inductive types

-- Definition 14.3.1

case-paths-induction-principle-propositional-truncation :
  { l : Level} {l1 l2 : Level} {A : UU l1}
  ( P : UU-Prop l2) (α : (p q : type-Prop P) → Id p q) (f : A → type-Prop P) →
  ( B : type-Prop P → UU l) → UU (l ⊔ l2)
case-paths-induction-principle-propositional-truncation P α f B =
  (p q : type-Prop P) (x : B p) (y : B q) → Id (tr B (α p q) x) y
  
induction-principle-propositional-truncation :
  (l : Level) {l1 l2 : Level} {A : UU l1}
  (P : UU-Prop l2) (α : (p q : type-Prop P) → Id p q) (f : A → type-Prop P) →
  UU (lsuc l ⊔ l1 ⊔ l2)
induction-principle-propositional-truncation l {l1} {l2} {A} P α f =
  ( B : type-Prop P → UU l) →
  ( g : (x : A) → (B (f x))) →
  ( β : case-paths-induction-principle-propositional-truncation P α f B) →
  Σ ((p : type-Prop P) → B p) (λ h → (x : A) → Id (h (f x)) (g x))

-- Lemma 14.3.2

is-prop-case-paths-induction-principle-propositional-truncation :
  { l : Level} {l1 l2 : Level} {A : UU l1}
  ( P : UU-Prop l2) (α : (p q : type-Prop P) → Id p q) (f : A → type-Prop P) →
  ( B : type-Prop P → UU l) →
  case-paths-induction-principle-propositional-truncation P α f B →
  ( p : type-Prop P) → is-prop (B p)
is-prop-case-paths-induction-principle-propositional-truncation P α f B β p =
  is-prop-is-proof-irrelevant (λ x → pair (tr B (α p p) x) (β p p x))

case-paths-induction-principle-propositional-truncation-is-prop :
  { l : Level} {l1 l2 : Level} {A : UU l1}
  ( P : UU-Prop l2) (α : (p q : type-Prop P) → Id p q) (f : A → type-Prop P) →
  ( B : type-Prop P → UU l) →
  ( (p : type-Prop P) → is-prop (B p)) →
  case-paths-induction-principle-propositional-truncation P α f B
case-paths-induction-principle-propositional-truncation-is-prop
  P α f B is-prop-B p q x y =
  eq-is-prop (is-prop-B q) (tr B (α p q) x) y

-- Theorem 14.2.3

abstract
  induction-principle-dependent-universal-property-propositional-truncation :
    { l1 l2 : Level} {A : UU l1} (P : UU-Prop l2) (f : A → type-Prop P) →
    ( {l : Level} →
      dependent-universal-property-propositional-truncation l P f) →
    ( {l : Level} → induction-principle-propositional-truncation l P
      ( eq-is-prop (is-prop-type-Prop P)) f)
  induction-principle-dependent-universal-property-propositional-truncation
    P f dup-f B g α =
    tot
      ( λ h → htpy-eq)
      ( center
        ( is-contr-map-is-equiv
          ( dup-f
            ( λ p →
              pair
                ( B p)
                ( is-prop-case-paths-induction-principle-propositional-truncation
                  ( P)
                  ( eq-is-prop (is-prop-type-Prop P))
                  f B α p)))
          ( g)))

{-
induction-principle-trunc-Prop :
  {l1 l2 : Level} (A : UU l1) →
  induction-principle-propositional-truncation l2
induction-principle-trunc-Prop A = ?
-}

abstract
  dependent-universal-property-induction-principle-propositional-truncation :
    { l1 l2 : Level} {A : UU l1} (P : UU-Prop l2) (f : A → type-Prop P) →
    ( {l : Level} → induction-principle-propositional-truncation l P
      ( eq-is-prop (is-prop-type-Prop P)) f) →
    ( {l : Level} → dependent-universal-property-propositional-truncation l P f)
  dependent-universal-property-induction-principle-propositional-truncation
    P f ind-f Q =
    is-equiv-is-prop
      ( is-prop-Π (λ p → is-prop-type-Prop (Q p)))
      ( is-prop-Π (λ a → is-prop-type-Prop (Q (f a))))
      ( λ g →
        pr1
          ( ind-f
            ( λ p → type-Prop (Q p))
            ( g)
            ( case-paths-induction-principle-propositional-truncation-is-prop
              ( P)
              ( eq-is-prop (is-prop-type-Prop P))
              ( f)
              ( λ p → type-Prop (Q p))
              ( λ p → is-prop-type-Prop (Q p)))))

--------------------------------------------------------------------------------

-- Section 14.7 Logic in type theory

-- Definition

conj-Prop = prod-Prop

type-conj-Prop :
  {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU (l1 ⊔ l2)
type-conj-Prop P Q = type-Prop (conj-Prop P Q)

disj-Prop :
  {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU-Prop (l1 ⊔ l2)
disj-Prop P Q = trunc-Prop (coprod (type-Prop P) (type-Prop Q))

type-disj-Prop :
  {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU (l1 ⊔ l2)
type-disj-Prop P Q = type-Prop (disj-Prop P Q)

inl-disj-Prop :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  type-hom-Prop P (disj-Prop P Q)
inl-disj-Prop P Q = unit-trunc-Prop ∘ inl

inr-disj-Prop :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  type-hom-Prop Q (disj-Prop P Q)
inr-disj-Prop P Q = unit-trunc-Prop ∘ inr

-- Proposition

ev-disj-Prop :
  {l1 l2 l3 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) (R : UU-Prop l3) →
  type-hom-Prop
    ( hom-Prop (disj-Prop P Q) R)
    ( conj-Prop (hom-Prop P R) (hom-Prop Q R))
ev-disj-Prop P Q R h =
  pair (h ∘ (inl-disj-Prop P Q)) (h ∘ (inr-disj-Prop P Q))

inv-ev-disj-Prop :
  {l1 l2 l3 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) (R : UU-Prop l3) →
  type-hom-Prop
    ( conj-Prop (hom-Prop P R) (hom-Prop Q R))
    ( hom-Prop (disj-Prop P Q) R)
inv-ev-disj-Prop P Q R (pair f g) =
  map-universal-property-trunc-Prop R (ind-coprod (λ t → type-Prop R) f g)

is-equiv-ev-disj-Prop :
  {l1 l2 l3 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) (R : UU-Prop l3) →
  is-equiv (ev-disj-Prop P Q R)
is-equiv-ev-disj-Prop P Q R =
  is-equiv-is-prop
    ( is-prop-type-Prop (hom-Prop (disj-Prop P Q) R))
    ( is-prop-type-Prop (conj-Prop (hom-Prop P R) (hom-Prop Q R)))
    ( inv-ev-disj-Prop P Q R)

-- Definition

exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) → UU-Prop (l1 ⊔ l2)
exists-Prop {l1} {l2} {A} P = trunc-Prop (Σ A (λ x → type-Prop (P x)))

exists :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) → UU (l1 ⊔ l2)
exists P = type-Prop (exists-Prop P)

is-prop-exists :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) → is-prop (exists P)
is-prop-exists P = is-prop-type-Prop (exists-Prop P)

intro-exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) →
  (x : A) → type-Prop (P x) → exists P
intro-exists-Prop {A = A} P x p = unit-trunc-Prop (pair x p)

-- Proposition

ev-intro-exists-Prop :
  {l1 l2 l3 : Level} {A : UU l1} (P : A → UU-Prop l2) (Q : UU-Prop l3) →
  type-hom-Prop (exists-Prop P) Q → (x : A) → type-hom-Prop (P x) Q
ev-intro-exists-Prop P Q H x p = H (intro-exists-Prop P x p)

elim-exists-Prop :
  {l1 l2 l3 : Level} {A : UU l1} (P : A → UU-Prop l2) (Q : UU-Prop l3) →
  ((x : A) → type-hom-Prop (P x) Q) → type-hom-Prop (exists-Prop P) Q
elim-exists-Prop {A = A} P Q f =
  map-universal-property-trunc-Prop Q (ind-Σ f)

is-equiv-ev-intro-exists-Prop :
  {l1 l2 l3 : Level} {A : UU l1} (P : A → UU-Prop l2) (Q : UU-Prop l3) →
  is-equiv (ev-intro-exists-Prop P Q)
is-equiv-ev-intro-exists-Prop P Q =
  is-equiv-is-prop
    ( is-prop-type-hom-Prop (exists-Prop P) Q)
    ( is-prop-Π ((λ x → is-prop-type-hom-Prop (P x) Q)))
    ( elim-exists-Prop P Q)

--------------------------------------------------------------------------------

map-distributive-trunc-prod-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  type-trunc-Prop (A × B) → type-trunc-Prop A × type-trunc-Prop B
map-distributive-trunc-prod-Prop {l1} {l2} {A} {B} =
  map-universal-property-trunc-Prop
    ( pair
      ( type-trunc-Prop A × type-trunc-Prop B)
      ( is-prop-prod is-prop-type-trunc-Prop is-prop-type-trunc-Prop))
    ( map-prod unit-trunc-Prop unit-trunc-Prop)

map-inv-distributive-trunc-prod-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  type-trunc-Prop A × type-trunc-Prop B → type-trunc-Prop (A × B)
map-inv-distributive-trunc-prod-Prop {l1} {l2} {A} {B} t =
  map-universal-property-trunc-Prop
    ( trunc-Prop (A × B))
    ( λ x →
      map-universal-property-trunc-Prop
        ( trunc-Prop (A × B))
        ( unit-trunc-Prop ∘ (pair x))
        ( pr2 t))
    ( pr1 t)

is-equiv-map-distributive-trunc-prod-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-equiv (map-distributive-trunc-prod-Prop {A = A} {B = B})
is-equiv-map-distributive-trunc-prod-Prop {l1} {l2} {A} {B} =
  is-equiv-is-prop
    ( is-prop-type-trunc-Prop)
    ( is-prop-prod is-prop-type-trunc-Prop is-prop-type-trunc-Prop)
    ( map-inv-distributive-trunc-prod-Prop)

distributive-trunc-prod-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  type-trunc-Prop (A × B) ≃ (type-trunc-Prop A × type-trunc-Prop B)
distributive-trunc-prod-Prop =
  pair map-distributive-trunc-prod-Prop
       is-equiv-map-distributive-trunc-prod-Prop

is-equiv-map-inv-distributive-trunc-prod-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-equiv (map-inv-distributive-trunc-prod-Prop {A = A} {B = B})
is-equiv-map-inv-distributive-trunc-prod-Prop {l1} {l2} {A} {B} =
  is-equiv-is-prop
    ( is-prop-prod is-prop-type-trunc-Prop is-prop-type-trunc-Prop)
    ( is-prop-type-trunc-Prop)
    ( map-distributive-trunc-prod-Prop)

inv-distributive-trunc-prod-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  ( type-trunc-Prop A × type-trunc-Prop B) ≃ type-trunc-Prop (A × B)
inv-distributive-trunc-prod-Prop =
  pair map-inv-distributive-trunc-prod-Prop
       is-equiv-map-inv-distributive-trunc-prod-Prop
