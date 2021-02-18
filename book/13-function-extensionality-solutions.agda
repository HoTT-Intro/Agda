{-# OPTIONS --without-K --exact-split #-}

module book.13-function-extensionality-solutions where

import book.13-function-extensionality
open book.13-function-extensionality public

--------------------------------------------------------------------------------

-- Exercises

-- Exercise 13.1

abstract
  is-equiv-inv-htpy :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
    (f g : (x : A) → B x) → is-equiv (inv-htpy {f = f} {g = g})
  is-equiv-inv-htpy f g =
    is-equiv-has-inverse
      ( inv-htpy)
      ( λ H → eq-htpy (λ x → inv-inv (H x)))
      ( λ H → eq-htpy (λ x → inv-inv (H x)))

equiv-inv-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f g : (x : A) → B x) → (f ~ g) ≃ (g ~ f)
equiv-inv-htpy f g = pair inv-htpy (is-equiv-inv-htpy f g)

abstract
  is-equiv-concat-htpy :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
    {f g : (x : A) → B x} (H : f ~ g) →
    (h : (x : A) → B x) → is-equiv (concat-htpy H h)
  is-equiv-concat-htpy {A = A} {B = B} {f} =
    ind-htpy f
      ( λ g H → (h : (x : A) → B x) → is-equiv (concat-htpy H h))
      ( λ h → is-equiv-id)

equiv-concat-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g : (x : A) → B x} (H : f ~ g) (h : (x : A) → B x) →
  (g ~ h) ≃ (f ~ h)
equiv-concat-htpy H h =
  pair (concat-htpy H h) (is-equiv-concat-htpy H h)

inv-concat-htpy' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x} →
  (g ~ h) → (f ~ h) → (f ~ g)
inv-concat-htpy' f K = concat-htpy' f (inv-htpy K)

issec-inv-concat-htpy' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x}
  (K : g ~ h) → ((concat-htpy' f K) ∘ (inv-concat-htpy' f K)) ~ id
issec-inv-concat-htpy' f K L =
  eq-htpy (λ x → issec-inv-concat' (f x) (K x) (L x))

isretr-inv-concat-htpy' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x}
  (K : g ~ h) → ((inv-concat-htpy' f K) ∘ (concat-htpy' f K)) ~ id
isretr-inv-concat-htpy' f K L =
  eq-htpy (λ x → isretr-inv-concat' (f x) (K x) (L x))

is-equiv-concat-htpy' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x} (K : g ~ h) →
  is-equiv (concat-htpy' f K)
is-equiv-concat-htpy' f K =
  is-equiv-has-inverse
    ( inv-concat-htpy' f K)
    ( issec-inv-concat-htpy' f K)
    ( isretr-inv-concat-htpy' f K)

equiv-concat-htpy' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x} (K : g ~ h) →
  (f ~ g) ≃ (f ~ h)
equiv-concat-htpy' f K =
  pair (concat-htpy' f K) (is-equiv-concat-htpy' f K)

-- Exercise 13.2

-- Exercise 13.2 (a)

abstract
  is-subtype-is-contr :
    {l : Level} → is-subtype {lsuc l} {A = UU l} is-contr
  is-subtype-is-contr A =
    is-prop-is-proof-irrelevant
      ( λ is-contr-A →
        is-contr-Σ
          ( is-contr-A)
          ( λ x → is-contr-Π (is-prop-is-contr is-contr-A x)))

is-contr-Prop : {l : Level} → UU l → UU-Prop l
is-contr-Prop A = pair (is-contr A) (is-subtype-is-contr A)

-- Exercise 13.2 (b)

abstract
  is-prop-is-trunc :
    {l : Level} (k : 𝕋) (A : UU l) → is-prop (is-trunc k A)
  is-prop-is-trunc neg-two-𝕋 = is-subtype-is-contr
  is-prop-is-trunc (succ-𝕋 k) A =
    is-prop-Π (λ x → is-prop-Π (λ y → is-prop-is-trunc k (Id x y)))

is-trunc-Prop : {l : Level} (k : 𝕋) (A : UU l) → UU-Prop l
is-trunc-Prop k A = pair (is-trunc k A) (is-prop-is-trunc k A)

abstract
  is-prop-is-prop :
    {l : Level} (A : UU l) → is-prop (is-prop A)
  is-prop-is-prop = is-prop-is-trunc neg-one-𝕋

is-prop-Prop : {l : Level} (A : UU l) → UU-Prop l
is-prop-Prop A = pair (is-prop A) (is-prop-is-prop A)

abstract
  is-prop-is-set :
    {l : Level} (A : UU l) → is-prop (is-set A)
  is-prop-is-set = is-prop-is-trunc zero-𝕋

is-set-Prop : {l : Level} → UU l → UU-Prop l
is-set-Prop A = pair (is-set A) (is-prop-is-set A)

abstract
  is-prop-is-1-type :
    {l : Level} (A : UU l) → is-prop (is-1-type A)
  is-prop-is-1-type A = is-prop-is-trunc one-𝕋 A

is-1-type-Prop :
  {l : Level} → UU l → UU-Prop l
is-1-type-Prop A = pair (is-1-type A) (is-prop-is-1-type A)

-- Later exercise

successor-preserving-map-ℕ : UU lzero
successor-preserving-map-ℕ = 
  Σ (ℕ → ℕ) (λ f → (f ∘ succ-ℕ) ~ (succ-ℕ ∘ f))

-- We characterize the identity type of successor-preserving-map-ℕ

htpy-successor-preserving-map-ℕ :
  (f g : successor-preserving-map-ℕ) → UU lzero
htpy-successor-preserving-map-ℕ f g = pr1 f ~ pr1 g

refl-htpy-successor-preserving-map-ℕ :
  (f : successor-preserving-map-ℕ) → htpy-successor-preserving-map-ℕ f f
refl-htpy-successor-preserving-map-ℕ f = refl-htpy

is-contr-total-htpy-successor-preserving-map-ℕ :
  (f : successor-preserving-map-ℕ) →
  is-contr (Σ successor-preserving-map-ℕ (htpy-successor-preserving-map-ℕ f))
is-contr-total-htpy-successor-preserving-map-ℕ f =
  is-contr-total-Eq-substructure
    ( is-contr-total-htpy (pr1 f))
    ( λ g → is-prop-Π (λ n → is-set-ℕ (g (succ-ℕ n)) (succ-ℕ (g n))))
    ( pr1 f)
    ( refl-htpy)
    ( pr2 f) 

htpy-successor-preserving-map-ℕ-eq :
  (f g : successor-preserving-map-ℕ) →
  Id f g → htpy-successor-preserving-map-ℕ f g
htpy-successor-preserving-map-ℕ-eq f .f refl =
  refl-htpy-successor-preserving-map-ℕ f

is-equiv-htpy-successor-preserving-map-ℕ-eq :
  (f g : successor-preserving-map-ℕ) →
  is-equiv (htpy-successor-preserving-map-ℕ-eq f g)
is-equiv-htpy-successor-preserving-map-ℕ-eq f =
  fundamental-theorem-id f
    ( refl-htpy-successor-preserving-map-ℕ f)
    ( is-contr-total-htpy-successor-preserving-map-ℕ f)
    ( htpy-successor-preserving-map-ℕ-eq f)

eq-htpy-successor-preserving-map-ℕ :
  {f g : successor-preserving-map-ℕ} →
  htpy-successor-preserving-map-ℕ f g → Id f g
eq-htpy-successor-preserving-map-ℕ {f} {g} =
  map-inv-is-equiv (is-equiv-htpy-successor-preserving-map-ℕ-eq f g)

-- We solve the exercise now

ev-zero-successor-preserving-map-ℕ :
  successor-preserving-map-ℕ → ℕ
ev-zero-successor-preserving-map-ℕ (pair f H) = f zero-ℕ

inv-ev-zero-successor-preserving-map-ℕ :
  ℕ → successor-preserving-map-ℕ
inv-ev-zero-successor-preserving-map-ℕ n =
  pair (add-ℕ n) refl-htpy

issec-inv-ev-zero-successor-preserving-map-ℕ :
  ( ev-zero-successor-preserving-map-ℕ ∘
    inv-ev-zero-successor-preserving-map-ℕ) ~ id
issec-inv-ev-zero-successor-preserving-map-ℕ n = refl

htpy-isretr-inv-ev-zero-successor-preserving-map-ℕ :
  ( f : ℕ → ℕ) (H : (f ∘ succ-ℕ) ~ (succ-ℕ ∘ f)) →
  ( add-ℕ (f zero-ℕ)) ~ f
htpy-isretr-inv-ev-zero-successor-preserving-map-ℕ f H zero-ℕ =
  refl
htpy-isretr-inv-ev-zero-successor-preserving-map-ℕ f H (succ-ℕ n) =
  ( ap succ-ℕ (htpy-isretr-inv-ev-zero-successor-preserving-map-ℕ f H n)) ∙
  ( inv (H n))

isretr-inv-ev-zero-successor-preserving-map-ℕ :
  ( inv-ev-zero-successor-preserving-map-ℕ ∘
    ev-zero-successor-preserving-map-ℕ) ~ id
isretr-inv-ev-zero-successor-preserving-map-ℕ (pair f H) =
  eq-htpy-successor-preserving-map-ℕ
    ( htpy-isretr-inv-ev-zero-successor-preserving-map-ℕ f H)

is-equiv-ev-zero-successor-preserving-map-ℕ :
  is-equiv ev-zero-successor-preserving-map-ℕ
is-equiv-ev-zero-successor-preserving-map-ℕ =
  is-equiv-has-inverse
    inv-ev-zero-successor-preserving-map-ℕ
    issec-inv-ev-zero-successor-preserving-map-ℕ
    isretr-inv-ev-zero-successor-preserving-map-ℕ

-- Exercise 13.3

-- Exercise 13.3 (a)

is-contr-sec-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-equiv f → is-contr (sec f)
is-contr-sec-is-equiv {A = A} {B = B} {f = f} is-equiv-f =
  is-contr-equiv'
    ( (b : B) → fib f b)
    ( equiv-choice-∞) 
    ( is-contr-Π (is-contr-map-is-equiv is-equiv-f))

-- Exercise 13.3 (b)

is-contr-retr-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-equiv f → is-contr (retr f)
is-contr-retr-is-equiv {A = A} {B = B} {f = f} is-equiv-f =
  is-contr-is-equiv'
    ( Σ (B → A) (λ h → Id (h ∘ f) id))
    ( tot (λ h → htpy-eq))
    ( is-equiv-tot-is-fiberwise-equiv
      ( λ h → funext (h ∘ f) id))
    ( is-contr-map-is-equiv (is-equiv-precomp-is-equiv f is-equiv-f A) id)

-- Exercise 13.3 (c)

is-contr-is-equiv-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f : A → B} → is-equiv f → is-contr (is-equiv f)
is-contr-is-equiv-is-equiv is-equiv-f =
  is-contr-prod
    ( is-contr-sec-is-equiv is-equiv-f)
    ( is-contr-retr-is-equiv is-equiv-f)

abstract
  is-subtype-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-subtype (is-equiv {A = A} {B = B})
  is-subtype-is-equiv f = is-prop-is-proof-irrelevant
    ( λ is-equiv-f → is-contr-prod
      ( is-contr-sec-is-equiv is-equiv-f)
      ( is-contr-retr-is-equiv is-equiv-f))

is-equiv-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → UU-Prop (l1 ⊔ l2)
is-equiv-Prop f =
  pair (is-equiv f) (is-subtype-is-equiv f)

abstract
  is-emb-map-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-emb (map-equiv {A = A} {B = B})
  is-emb-map-equiv = is-emb-pr1-is-subtype is-subtype-is-equiv

-- Exercise 13.3 (d)

htpy-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → A ≃ B → A ≃ B → UU (l1 ⊔ l2)
htpy-equiv e e' = (map-equiv e) ~ (map-equiv e')

refl-htpy-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) → htpy-equiv e e
refl-htpy-equiv e = refl-htpy

htpy-equiv-eq :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {e e' : A ≃ B} (p : Id e e') → htpy-equiv e e'
htpy-equiv-eq {e = e} {.e} refl =
  refl-htpy-equiv e

abstract
  is-contr-total-htpy-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    is-contr (Σ (A ≃ B) (λ e' → htpy-equiv e e'))
  is-contr-total-htpy-equiv (pair f is-equiv-f) =
    is-contr-total-Eq-substructure
      ( is-contr-total-htpy f)
      ( is-subtype-is-equiv)
      ( f)
      ( refl-htpy)
      ( is-equiv-f)

  is-equiv-htpy-equiv-eq :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e e' : A ≃ B) →
    is-equiv (htpy-equiv-eq {e = e} {e'})
  is-equiv-htpy-equiv-eq e =
    fundamental-theorem-id e
      ( refl-htpy-equiv e)
      ( is-contr-total-htpy-equiv e)
      ( λ e' → htpy-equiv-eq {e = e} {e'})

eq-htpy-equiv :
  { l1 l2 : Level} {A : UU l1} {B : UU l2} {e e' : A ≃ B} →
  ( htpy-equiv e e') → Id e e'
eq-htpy-equiv {e = e} {e'} = map-inv-is-equiv (is-equiv-htpy-equiv-eq e e')

abstract
  Ind-htpy-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    (P : (e' : A ≃ B) (H : htpy-equiv e e') → UU l3) →
    sec
      ( λ (h : (e' : A ≃ B) (H : htpy-equiv e e') → P e' H) →
        h e (refl-htpy-equiv e))
  Ind-htpy-equiv {l3 = l3} e =
    Ind-identity-system l3 e
      ( refl-htpy-equiv e)
      ( is-contr-total-htpy-equiv e)
  
  ind-htpy-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    (P : (e' : A ≃ B) (H : htpy-equiv e e') → UU l3) →
    P e (refl-htpy-equiv e) → (e' : A ≃ B) (H : htpy-equiv e e') → P e' H
  ind-htpy-equiv e P = pr1 (Ind-htpy-equiv e P)
  
  comp-htpy-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    (P : (e' : A ≃ B) (H : htpy-equiv e e') → UU l3)
    (p : P e (refl-htpy-equiv e)) →
    Id (ind-htpy-equiv e P p e (refl-htpy-equiv e)) p
  comp-htpy-equiv e P = pr2 (Ind-htpy-equiv e P)

-- Exercise 13.3 (e)
   
is-contr-equiv-is-contr :
  { l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-contr A → is-contr B → is-contr (A ≃ B)
is-contr-equiv-is-contr is-contr-A is-contr-B =
  pair
    ( equiv-is-contr is-contr-A is-contr-B)
    ( λ e → eq-htpy-equiv (λ x → eq-is-contr is-contr-B))

is-trunc-is-contr :
  { l : Level} (k : 𝕋) {A : UU l} → is-contr A → is-trunc k A
is-trunc-is-contr neg-two-𝕋 is-contr-A = is-contr-A
is-trunc-is-contr (succ-𝕋 k) is-contr-A x y =
  is-trunc-is-contr k (is-prop-is-contr is-contr-A x y)

is-trunc-is-prop :
  { l : Level} (k : 𝕋) {A : UU l} → is-prop A → is-trunc (succ-𝕋 k) A
is-trunc-is-prop k is-prop-A x y = is-trunc-is-contr k (is-prop-A x y)

is-trunc-equiv-is-trunc :
  { l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-trunc k A → is-trunc k B → is-trunc k (A ≃ B)
is-trunc-equiv-is-trunc neg-two-𝕋 is-trunc-A is-trunc-B =
  is-contr-equiv-is-contr is-trunc-A is-trunc-B
is-trunc-equiv-is-trunc (succ-𝕋 k) is-trunc-A is-trunc-B = 
  is-trunc-Σ (succ-𝕋 k)
    ( is-trunc-Π (succ-𝕋 k) (λ x → is-trunc-B))
    ( λ x → is-trunc-is-prop k (is-subtype-is-equiv x))

is-prop-equiv-is-prop :
  { l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-prop A → is-prop B → is-prop (A ≃ B)
is-prop-equiv-is-prop = is-trunc-equiv-is-trunc neg-one-𝕋

prop-equiv :
  { l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU-Prop (l1 ⊔ l2)
prop-equiv P Q =
  pair
    ( type-Prop P ≃ type-Prop Q)
    ( is-prop-equiv-is-prop (is-prop-type-Prop P) (is-prop-type-Prop Q))

is-set-equiv-is-set :
  { l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-set A → is-set B → is-set (A ≃ B)
is-set-equiv-is-set = is-trunc-equiv-is-trunc zero-𝕋

set-equiv :
  { l1 l2 : Level} → UU-Set l1 → UU-Set l2 → UU-Set (l1 ⊔ l2)
set-equiv A B =
  pair
    ( type-Set A ≃ type-Set B)
    ( is-set-equiv-is-set (is-set-type-Set A) (is-set-type-Set B))

-- Exercise 13.9

abstract
  dependent-universal-property-empty :
    {l : Level} (P : empty → UU l) → is-contr ((x : empty) → P x)
  dependent-universal-property-empty P =
    pair
      ( ind-empty {P = P})
      ( λ f → eq-htpy ind-empty)

abstract
  universal-property-empty :
    {l : Level} (X : UU l) → is-contr (empty → X)
  universal-property-empty X = dependent-universal-property-empty (λ t → X)

abstract
  uniqueness-empty :
    {l : Level} (Y : UU l) → ((l' : Level) (X : UU l') →
    is-contr (Y → X)) → is-equiv (ind-empty {P = λ t → Y})
  uniqueness-empty Y H =
    is-equiv-is-equiv-precomp ind-empty
      ( λ l X → is-equiv-is-contr
        ( λ g → g ∘ ind-empty)
        ( H _ X)
        ( universal-property-empty X))

abstract
  universal-property-empty-is-equiv-ind-empty :
    {l : Level} (X : UU l) → is-equiv (ind-empty {P = λ t → X}) →
    ((l' : Level) (Y : UU l') → is-contr (X → Y))
  universal-property-empty-is-equiv-ind-empty X is-equiv-ind-empty l' Y =
    is-contr-is-equiv
      ( empty → Y)
      ( λ f → f ∘ ind-empty)
      ( is-equiv-precomp-is-equiv ind-empty is-equiv-ind-empty Y)
      ( universal-property-empty Y)

-- Exercise 13.10

-- Exercise 13.10 (a)

ev-star :
  {l : Level} (P : unit → UU l) → ((x : unit) → P x) → P star
ev-star P f = f star

abstract
  dependent-universal-property-unit :
    {l : Level} (P : unit → UU l) → is-equiv (ev-star P)
  dependent-universal-property-unit P =
    is-equiv-has-inverse
      ( ind-unit)
      ( λ p → refl)
      ( λ f → eq-htpy (ind-unit refl))

equiv-ev-star :
  {l : Level} (P : unit → UU l) → ((x : unit) → P x) ≃ P star
equiv-ev-star P = pair (ev-star P) (dependent-universal-property-unit P)

ev-star' :
  {l : Level} (Y : UU l) → (unit → Y) → Y
ev-star' Y = ev-star (λ t → Y)

abstract
  universal-property-unit :
    {l : Level} (Y : UU l) → is-equiv (ev-star' Y)
  universal-property-unit Y = dependent-universal-property-unit (λ t → Y)

equiv-ev-star' :
  {l : Level} (Y : UU l) → (unit → Y) ≃ Y
equiv-ev-star' Y = pair (ev-star' Y) (universal-property-unit Y)

-- Exercise 13.10 (b)

pt : {l1 : Level} {X : UU l1} (x : X) → unit → X
pt x y = x

abstract
  is-equiv-pt-is-contr :
    {l1 : Level} {X : UU l1} (x : X) →
    is-contr X → is-equiv (pt x)
  is-equiv-pt-is-contr x is-contr-X =
    is-equiv-is-contr (pt x) is-contr-unit is-contr-X

abstract
  is-equiv-pt-universal-property-unit :
    {l1 : Level} (X : UU l1) (x : X) →
    ((l2 : Level) (Y : UU l2) → is-equiv (λ (f : X → Y) → f x)) →
    is-equiv (pt x)
  is-equiv-pt-universal-property-unit X x H =
    is-equiv-is-equiv-precomp
      ( pt x)
      ( λ l Y → is-equiv-right-factor'
        ( ev-star' Y)
        ( precomp (pt x) Y)
        ( universal-property-unit Y)
        ( H _ Y))

abstract
  universal-property-unit-is-equiv-pt :
    {l1 : Level} {X : UU l1} (x : X) →
    is-equiv (pt x) →
    ({l2 : Level} (Y : UU l2) → is-equiv (λ (f : X → Y) → f x))
  universal-property-unit-is-equiv-pt x is-equiv-pt Y =
    is-equiv-comp
      ( λ f → f x)
      ( ev-star' Y)
      ( precomp (pt x) Y)
      ( λ f → refl)
      ( is-equiv-precomp-is-equiv (pt x) is-equiv-pt Y)
      ( universal-property-unit Y)

abstract
  universal-property-unit-is-contr :
    {l1 : Level} {X : UU l1} (x : X) →
    is-contr X →
    ({l2 : Level} (Y : UU l2) → is-equiv (λ (f : X → Y) → f x))
  universal-property-unit-is-contr x is-contr-X =
    universal-property-unit-is-equiv-pt x
      ( is-equiv-pt-is-contr x is-contr-X)

abstract
  is-equiv-diagonal-is-equiv-pt :
    {l1 : Level} {X : UU l1} (x : X) →
    is-equiv (pt x) →
    ({l2 : Level} (Y : UU l2) → is-equiv (λ y → const X Y y))
  is-equiv-diagonal-is-equiv-pt {X = X} x is-equiv-pt Y =
    is-equiv-is-section-is-equiv
      ( universal-property-unit-is-equiv-pt x is-equiv-pt Y)
      ( refl-htpy)

abstract
  is-equiv-diagonal-is-contr :
    {l1 : Level} {X : UU l1} (x : X) →
    is-contr X →
    ({l2 : Level} (Y : UU l2) → is-equiv (λ y → const X Y y))
  is-equiv-diagonal-is-contr x is-contr-X =
    is-equiv-diagonal-is-equiv-pt x (is-equiv-pt-is-contr x is-contr-X)
    
-- Exercise 13.11

ev-inl-inr :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (P : coprod A B → UU l3) →
  ((t : coprod A B) → P t) → ((x : A) → P (inl x)) × ((y : B) → P (inr y))
ev-inl-inr P s = pair (λ x → s (inl x)) (λ y → s (inr y))

abstract
  dependent-universal-property-coprod :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
    (P : coprod A B → UU l3) → is-equiv (ev-inl-inr P)
  dependent-universal-property-coprod P =
    is-equiv-has-inverse
      ( λ p → ind-coprod P (pr1 p) (pr2 p))
      ( ind-Σ (λ f g → eq-pair refl refl))
      ( λ s → eq-htpy (ind-coprod _ (λ x → refl) λ y → refl))

equiv-dependent-universal-property-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (P : coprod A B → UU l3) →
  ((x : coprod A B) → P x) ≃ (((a : A) → P (inl a)) × ((b : B) → P (inr b)))
equiv-dependent-universal-property-coprod P =
  pair (ev-inl-inr P) (dependent-universal-property-coprod P)

abstract
  universal-property-coprod :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (X : UU l3) →
    is-equiv (ev-inl-inr (λ (t : coprod A B) → X))
  universal-property-coprod X = dependent-universal-property-coprod (λ t → X)

equiv-universal-property-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (X : UU l3) →
  (coprod A B → X) ≃ ((A → X) × (B → X))
equiv-universal-property-coprod X =
  equiv-dependent-universal-property-coprod (λ t → X)

abstract
  uniqueness-coprod :
    { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {Y : UU l3}
    ( i : A → Y) (j : B → Y) →
    ( (l : Level) (X : UU l) →
      is-equiv (λ (s : Y → X) → pair' (s ∘ i) (s ∘ j))) →
    is-equiv (ind-coprod (λ t → Y) i j)
  uniqueness-coprod {Y = Y} i j H =
    is-equiv-is-equiv-precomp
      ( ind-coprod _ i j)
      ( λ l X → is-equiv-right-factor'
        ( ev-inl-inr (λ t → X))
        ( precomp (ind-coprod (λ t → Y) i j) X)
        ( universal-property-coprod X)
        ( H _ X))

abstract
  universal-property-coprod-is-equiv-ind-coprod :
    { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (X : UU l3)
    ( i : A → X) (j : B → X) → is-equiv (ind-coprod (λ t → X) i j) →
    ( (l4 : Level) (Y : UU l4) →
      is-equiv (λ (s : X → Y) → pair' (s ∘ i) (s ∘ j)))
  universal-property-coprod-is-equiv-ind-coprod X i j is-equiv-ind-coprod l Y =
    is-equiv-comp
      ( λ s → pair (s ∘ i) (s ∘ j))
      ( ev-inl-inr (λ t → Y))
      ( precomp (ind-coprod (λ t → X) i j) Y)
      ( λ s → refl)
      ( is-equiv-precomp-is-equiv
        ( ind-coprod (λ t → X) i j)
        ( is-equiv-ind-coprod)
        ( Y))
      ( universal-property-coprod Y)

-- Exercise 13.4

postcomp :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (A : UU l3) →
  (X → Y) → (A → X) → (A → Y)
postcomp A f h = f ∘ h

{- We first show that a map f is an equivalence if and only if postcomposition
   by that map is an equivalence. This is the base case of the more general
   claim. -}

abstract
  is-equiv-is-equiv-postcomp :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) →
    ({l3 : Level} (A : UU l3) → is-equiv (postcomp A f)) → is-equiv f
  is-equiv-is-equiv-postcomp {X = X} {Y = Y} f post-comp-equiv-f =
    let sec-f = center (is-contr-map-is-equiv (post-comp-equiv-f Y) id) in
    is-equiv-has-inverse
      ( pr1 sec-f)
      ( htpy-eq (pr2 sec-f))
      ( htpy-eq
        ( ap ( pr1)
             ( eq-is-contr'
               ( is-contr-map-is-equiv (post-comp-equiv-f X) f)
               ( pair ((pr1 sec-f) ∘ f) (ap (λ t → t ∘ f) (pr2 sec-f)))
               ( pair id refl))))

{- The following version of the same theorem works when X and Y are in the same
   universe. The condition of inducing equivalences by postcomposition is 
   simplified to that universe. -}

is-equiv-is-equiv-postcomp' :
  {l : Level} {X : UU l} {Y : UU l} (f : X → Y) →
  ((A : UU l) → is-equiv (postcomp A f)) → is-equiv f
is-equiv-is-equiv-postcomp'
  {l} {X} {Y} f is-equiv-postcomp-f =
  let sec-f = center (is-contr-map-is-equiv (is-equiv-postcomp-f Y) id)
  in
  is-equiv-has-inverse
    ( pr1 sec-f)
    ( htpy-eq (pr2 sec-f))
    ( htpy-eq
      ( ap ( pr1)
           ( eq-is-contr'
             ( is-contr-map-is-equiv (is-equiv-postcomp-f X) f)
             ( pair ((pr1 sec-f) ∘ f) (ap (λ t → t ∘ f) (pr2 sec-f)))
             ( pair id refl))))

abstract
  is-equiv-postcomp-is-equiv :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) → is-equiv f →
    ({l3 : Level} (A : UU l3) → is-equiv (postcomp A f))
  is-equiv-postcomp-is-equiv {X = X} {Y = Y} f is-equiv-f A =
    is-equiv-has-inverse 
      ( postcomp A (map-inv-is-equiv is-equiv-f))
      ( λ g → eq-htpy (htpy-right-whisk (issec-map-inv-is-equiv is-equiv-f) g))
      ( λ h → eq-htpy (htpy-right-whisk (isretr-map-inv-is-equiv is-equiv-f) h))

equiv-postcomp :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (A : UU l3) →
  (X ≃ Y) → (A → X) ≃ (A → Y)
equiv-postcomp A e =
  pair
    ( postcomp A (map-equiv e))
    ( is-equiv-postcomp-is-equiv (map-equiv e) (is-equiv-map-equiv e) A)

{- We now give the solution to the general claim -}

equiv-fiber-postcomp :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  (A : UU l3) (g : A → Y) →
  ( fib (postcomp A f) g) ≃ ((a : A) → (fib f (g a)))
equiv-fiber-postcomp f A g =
  ( equiv-inv-choice-∞ (λ a x → Id (f x) (g a))) ∘e
  ( equiv-tot (λ h → equiv-funext))

is-trunc-map-postcomp-is-trunc-map :
  {l1 l2 l3 : Level} (k : 𝕋) (A : UU l3) {X : UU l1} {Y : UU l2} (f : X → Y) →
  is-trunc-map k f → is-trunc-map k (postcomp A f)
is-trunc-map-postcomp-is-trunc-map k A f is-trunc-f y =
  is-trunc-equiv k _
    ( equiv-fiber-postcomp f A y)
    ( is-trunc-Π k (λ x → is-trunc-f (y x)))

is-trunc-map-is-trunc-map-postcomp :
  {l1 l2 : Level} (k : 𝕋) {X : UU l1} {Y : UU l2} (f : X → Y) →
  ( {l3 : Level} (A : UU l3) → is-trunc-map k (postcomp A f)) →
  is-trunc-map k f
is-trunc-map-is-trunc-map-postcomp k {X} f is-trunc-post-f y = 
  is-trunc-equiv k _
    ( inv-equiv
      ( ( equiv-ev-star (λ x → fib f y)) ∘e
        ( equiv-fiber-postcomp f unit (λ x → y))))
    ( is-trunc-post-f unit (λ x → y))

is-emb-postcomp-is-emb :
  {l1 l2 l3 : Level} (A : UU l3) {X : UU l1} {Y : UU l2} (f : X → Y) →
  is-emb f → is-emb (postcomp A f)
is-emb-postcomp-is-emb A f is-emb-f =
  is-emb-is-prop-map
    ( is-trunc-map-postcomp-is-trunc-map neg-one-𝕋 A f
      ( is-prop-map-is-emb is-emb-f))

is-emb-is-emb-postcomp :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) →
  ({l : Level} (A : UU l) → is-emb (postcomp A f)) → is-emb f
is-emb-is-emb-postcomp f is-emb-post-f =
  is-emb-is-prop-map
    ( is-trunc-map-is-trunc-map-postcomp neg-one-𝕋 f
      ( λ A → is-prop-map-is-emb (is-emb-post-f A)))

-- Exercise 13.5

-- Exercise 13.13

postcomp-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (e : (i : I) → A i → B i) →
  ((i : I) → A i) → ((i : I) → B i)
postcomp-Π e f i = e i (f i)

htpy-postcomp-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {f f' : (i : I) → A i → B i} (H : (i : I) → (f i) ~ (f' i)) →
  (postcomp-Π f) ~ (postcomp-Π f')
htpy-postcomp-Π H h = eq-htpy (λ i → H i (h i))

abstract
  is-equiv-postcomp-Π :
    {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
    (e : (i : I) → A i → B i) (is-equiv-e : is-fiberwise-equiv e) →
    is-equiv (postcomp-Π e)
  is-equiv-postcomp-Π e is-equiv-e =
    is-equiv-has-inverse
      ( λ g i → map-inv-is-equiv (is-equiv-e i) (g i))
      ( λ g → eq-htpy (λ i → issec-map-inv-is-equiv (is-equiv-e i) (g i)))
      ( λ f → eq-htpy (λ i → isretr-map-inv-is-equiv (is-equiv-e i) (f i)))

equiv-postcomp-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (e : (i : I) → (A i) ≃ (B i)) → ((i : I) → A i) ≃ ((i : I) → B i)
equiv-postcomp-Π e =
  pair
    ( postcomp-Π (λ i → map-equiv (e i)))
    ( is-equiv-postcomp-Π _ (λ i → is-equiv-map-equiv (e i)))

-- We conclude this exercise with some bureaucracy

map-equiv-Π :
  { l1 l2 l3 l4 : Level}
  { A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
  ( e : A' ≃ A) (f : (a' : A') → B' a' ≃ B (map-equiv e a')) →
  ( (a' : A') → B' a') → ( (a : A) → B a)
map-equiv-Π {B' = B'} B e f =
  ( postcomp-Π (λ a →
    ( tr B (issec-map-inv-is-equiv (is-equiv-map-equiv e) a)) ∘
    ( map-equiv (f (map-inv-is-equiv (is-equiv-map-equiv e) a))))) ∘
  ( precomp-Π (map-inv-is-equiv (is-equiv-map-equiv e)) B')

id-map-equiv-Π :
  { l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
  ( map-equiv-Π B (equiv-id {A = A}) (λ a → equiv-id {A = B a})) ~ id
id-map-equiv-Π B = refl-htpy

abstract
  is-equiv-map-equiv-Π :
    { l1 l2 l3 l4 : Level}
    { A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
    ( e : A' ≃ A) (f : (a' : A') → B' a' ≃ B (map-equiv e a')) →
    is-equiv (map-equiv-Π B e f)
  is-equiv-map-equiv-Π {B' = B'} B e f =
    is-equiv-comp'
      ( postcomp-Π (λ a →
        ( tr B (issec-map-inv-is-equiv (is-equiv-map-equiv e) a)) ∘
        ( map-equiv (f (map-inv-is-equiv (is-equiv-map-equiv e) a)))))
      ( precomp-Π (map-inv-is-equiv (is-equiv-map-equiv e)) B')
      ( is-equiv-precomp-Π-is-equiv
        ( map-inv-is-equiv (is-equiv-map-equiv e))
        ( is-equiv-map-inv-is-equiv (is-equiv-map-equiv e))
        ( B'))
      ( is-equiv-postcomp-Π _
        ( λ a → is-equiv-comp'
          ( tr B (issec-map-inv-is-equiv (is-equiv-map-equiv e) a))
          ( map-equiv (f (map-inv-is-equiv (is-equiv-map-equiv e) a)))
          ( is-equiv-map-equiv (f (map-inv-is-equiv (is-equiv-map-equiv e) a)))
          ( is-equiv-tr B (issec-map-inv-is-equiv (is-equiv-map-equiv e) a))))

equiv-Π :
  { l1 l2 l3 l4 : Level}
  { A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
  ( e : A' ≃ A) (f : (a' : A') → B' a' ≃ B (map-equiv e a')) →
  ( (a' : A') → B' a') ≃ ( (a : A) → B a)
equiv-Π B e f = pair (map-equiv-Π B e f) (is-equiv-map-equiv-Π B e f)

-- Exercise 13.14

-- Exercise 13.15

abstract
  is-prop-is-path-split :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-prop (is-path-split f)
  is-prop-is-path-split f =
    is-prop-is-proof-irrelevant (λ is-path-split-f →
      let is-equiv-f = is-equiv-is-path-split f is-path-split-f in
      is-contr-prod
        ( is-contr-sec-is-equiv is-equiv-f)
        ( is-contr-Π
          ( λ x → is-contr-Π
            ( λ y → is-contr-sec-is-equiv (is-emb-is-equiv f is-equiv-f x y)))))

abstract
  is-equiv-is-path-split-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-equiv (is-path-split-is-equiv f)
  is-equiv-is-path-split-is-equiv f =
    is-equiv-is-prop
      ( is-subtype-is-equiv f)
      ( is-prop-is-path-split f)
      ( is-equiv-is-path-split f)

abstract
  is-prop-is-coherently-invertible :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-prop (is-coherently-invertible f)
  is-prop-is-coherently-invertible {l1} {l2} {A} {B} f =
    is-prop-is-proof-irrelevant (λ is-hae-f →
      let is-equiv-f = is-equiv-is-coherently-invertible f is-hae-f in
      is-contr-equiv'
        ( Σ (sec f)
          ( λ sf → Σ (((pr1 sf) ∘ f) ~ id)
            ( λ H → (htpy-right-whisk (pr2 sf) f) ~ (htpy-left-whisk f H))))
        ( assoc-Σ (B → A)
          ( λ g → ((f ∘ g) ~ id))
          ( λ sf → Σ (((pr1 sf) ∘ f) ~ id)
            ( λ H → (htpy-right-whisk (pr2 sf) f) ~ (htpy-left-whisk f H))))
        ( is-contr-Σ
          ( is-contr-sec-is-equiv is-equiv-f)
          ( λ sf → is-contr-equiv'
            ( (x : A) →
              Σ (Id ((pr1 sf) (f x)) x) (λ p → Id ((pr2 sf) (f x)) (ap f p)))
            ( equiv-choice-∞)
            ( is-contr-Π (λ x →
              is-contr-equiv'
                ( fib (ap f) ((pr2 sf) (f x)))
                ( equiv-tot
                  ( λ p → equiv-inv (ap f p) ((pr2 sf) (f x))))
                ( is-contr-map-is-equiv
                  ( is-emb-is-equiv f is-equiv-f (pr1 sf (f x)) x)
                  ( (pr2 sf) (f x))))))))

abstract
  is-equiv-is-coherently-invertible-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-equiv (is-coherently-invertible-is-equiv f)
  is-equiv-is-coherently-invertible-is-equiv f =
    is-equiv-is-prop
      ( is-subtype-is-equiv f)
      ( is-prop-is-coherently-invertible f)
      ( is-equiv-is-coherently-invertible f)

-- Exercise 13.15 (b)

is-invertible-id-htpy-id-id :
  {l : Level} (A : UU l) →
  (id {A = A} ~ id {A = A}) → has-inverse (id {A = A})
is-invertible-id-htpy-id-id A H = pair id (pair refl-htpy H)

triangle-is-invertible-id-htpy-id-id :
  {l : Level} (A : UU l) →
  ( is-invertible-id-htpy-id-id A) ~
    ( ( map-assoc-Σ (A → A) (λ g → (id ∘ g) ~ id) (λ s → ((pr1 s) ∘ id) ~ id)) ∘
      ( map-inv-left-unit-law-Σ-is-contr
        { B = λ s → ((pr1 s) ∘ id) ~ id}
        ( is-contr-sec-is-equiv (is-equiv-id {_} {A}))
        ( pair id refl-htpy)))
triangle-is-invertible-id-htpy-id-id A H = refl

abstract
  is-equiv-invertible-id-htpy-id-id :
    {l : Level} (A : UU l) → is-equiv (is-invertible-id-htpy-id-id A)
  is-equiv-invertible-id-htpy-id-id A =
    is-equiv-comp
      ( is-invertible-id-htpy-id-id A)
      ( map-assoc-Σ (A → A) (λ g → (id ∘ g) ~ id) (λ s → ((pr1 s) ∘ id) ~ id))
      ( map-inv-left-unit-law-Σ-is-contr
        ( is-contr-sec-is-equiv is-equiv-id)
        ( pair id refl-htpy))
      ( triangle-is-invertible-id-htpy-id-id A)
      ( is-equiv-map-inv-left-unit-law-Σ-is-contr
        ( is-contr-sec-is-equiv is-equiv-id)
        ( pair id refl-htpy))
      ( is-equiv-map-assoc-Σ _ _ _)
    
-- Exercise 13.12

Eq-sec :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  sec f → sec f → UU (l1 ⊔ l2)
Eq-sec f sec-f sec-f' =
  Σ ( (pr1 sec-f) ~ (pr1 sec-f'))
    ( λ H → (pr2 sec-f) ~ ((f ·l H) ∙h (pr2 sec-f')))

reflexive-Eq-sec :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (sec-f : sec f) → Eq-sec f sec-f sec-f
reflexive-Eq-sec f (pair g G) = pair refl-htpy refl-htpy

Eq-sec-eq :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (sec-f sec-f' : sec f) → Id sec-f sec-f' → Eq-sec f sec-f sec-f'
Eq-sec-eq f sec-f .sec-f refl = reflexive-Eq-sec f sec-f

abstract
  is-contr-total-Eq-sec :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (sec-f : sec f) →
    is-contr (Σ (sec f) (Eq-sec f sec-f))
  is-contr-total-Eq-sec f (pair g G) =
    is-contr-total-Eq-structure
      ( λ g' G' H → G ~ ((f ·l H) ∙h G'))
      ( is-contr-total-htpy g)
      ( pair g refl-htpy)
      ( is-contr-total-htpy G)

abstract
  is-equiv-Eq-sec-eq :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    (sec-f sec-f' : sec f) → is-equiv (Eq-sec-eq f sec-f sec-f')
  is-equiv-Eq-sec-eq f sec-f =
    fundamental-theorem-id sec-f
      ( reflexive-Eq-sec f sec-f)
      ( is-contr-total-Eq-sec f sec-f)
      ( Eq-sec-eq f sec-f)
  
  eq-Eq-sec :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    {sec-f sec-f' : sec f} → Eq-sec f sec-f sec-f' → Id sec-f sec-f'
  eq-Eq-sec f {sec-f} {sec-f'} =
    map-inv-is-equiv (is-equiv-Eq-sec-eq f sec-f sec-f')

isretr-section-comp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) (sec-h : sec h) →
  ((section-comp f g h H sec-h) ∘ (section-comp' f g h H sec-h)) ~ id
isretr-section-comp f g h H (pair k K) (pair l L) =
  eq-Eq-sec g
    ( pair
      ( K ·r l)
      ( ( inv-htpy
          ( assoc-htpy
            ( inv-htpy (H ·r (k ∘ l)))
            ( H ·r (k ∘ l))
            ( (g ·l (K ·r l)) ∙h L))) ∙h
        ( htpy-ap-concat'
          ( (inv-htpy (H ·r (k ∘ l))) ∙h (H ·r (k ∘ l)))
          ( refl-htpy)
          ( (g ·l (K ·r l)) ∙h L)
          ( left-inv-htpy (H ·r (k ∘ l))))))

sec-left-factor-retract-of-sec-composition :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  sec h → (sec g) retract-of (sec f)
sec-left-factor-retract-of-sec-composition {X = X} f g h H sec-h =
  pair
    ( section-comp' f g h H sec-h)
    ( pair
      ( section-comp f g h H sec-h)
      ( isretr-section-comp f g h H sec-h))

Eq-retr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  retr f → retr f → UU (l1 ⊔ l2)
Eq-retr f retr-f retr-f' =
  Σ ( (pr1 retr-f) ~ (pr1 retr-f'))
    ( λ H → (pr2 retr-f) ~ ((H ·r f) ∙h (pr2 retr-f')))

reflexive-Eq-retr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (retr-f : retr f) → Eq-retr f retr-f retr-f
reflexive-Eq-retr f (pair h H) = pair refl-htpy refl-htpy

Eq-retr-eq :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (retr-f retr-f' : retr f) → Id retr-f retr-f' → Eq-retr f retr-f retr-f'
Eq-retr-eq f retr-f .retr-f refl = reflexive-Eq-retr f retr-f

abstract
  is-contr-total-Eq-retr :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (retr-f : retr f) →
    is-contr (Σ (retr f) (Eq-retr f retr-f))
  is-contr-total-Eq-retr f (pair h H) =
    is-contr-total-Eq-structure
      ( λ h' H' K → H ~ ((K ·r f) ∙h H'))
      ( is-contr-total-htpy h)
      ( pair h refl-htpy)
      ( is-contr-total-htpy H)

abstract
  is-equiv-Eq-retr-eq :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    (retr-f retr-f' : retr f) → is-equiv (Eq-retr-eq f retr-f retr-f')
  is-equiv-Eq-retr-eq f retr-f =
    fundamental-theorem-id retr-f
      ( reflexive-Eq-retr f retr-f)
      ( is-contr-total-Eq-retr f retr-f)
      ( Eq-retr-eq f retr-f)
  
  eq-Eq-retr :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    {retr-f retr-f' : retr f} → Eq-retr f retr-f retr-f' → Id retr-f retr-f'
  eq-Eq-retr f {retr-f} {retr-f'} =
    map-inv-is-equiv (is-equiv-Eq-retr-eq f retr-f retr-f')

isretr-retraction-comp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) (retr-g : retr g) →
  ((retraction-comp f g h H retr-g) ∘ (retraction-comp' f g h H retr-g)) ~ id
isretr-retraction-comp f g h H (pair l L) (pair k K) =
  eq-Eq-retr h
    ( pair
      ( k ·l L)
      ( ( inv-htpy
          ( assoc-htpy
            ( inv-htpy ((k ∘ l) ·l H))
            ( (k ∘ l) ·l H)
            ( (k ·l (L ·r h)) ∙h K))) ∙h
        ( htpy-ap-concat'
          ( (inv-htpy ((k ∘ l) ·l H)) ∙h ((k ∘ l) ·l H))
          ( refl-htpy)
          ( (k ·l (L ·r h)) ∙h K)
          ( left-inv-htpy ((k ∘ l) ·l H)))))
  
sec-right-factor-retract-of-sec-left-factor :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  retr g → (retr h) retract-of (retr f)
sec-right-factor-retract-of-sec-left-factor f g h H retr-g =
  pair
    ( retraction-comp' f g h H retr-g)
    ( pair
      ( retraction-comp f g h H retr-g)
      ( isretr-retraction-comp f g h H retr-g))

-- Exercise 13.15

{- Getting rid of fib in a Π-type -}

map-reduce-Π-fib :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (C : (y : B) (z : fib f y) → UU l3) →
  ((y : B) (z : fib f y) → C y z) → ((x : A) → C (f x) (pair x refl))
map-reduce-Π-fib f C h x = h (f x) (pair x refl)

inv-map-reduce-Π-fib :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (C : (y : B) (z : fib f y) → UU l3) →
  ((x : A) → C (f x) (pair x refl)) → ((y : B) (z : fib f y) → C y z)
inv-map-reduce-Π-fib f C h .(f x) (pair x refl) = h x

issec-inv-map-reduce-Π-fib :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (C : (y : B) (z : fib f y) → UU l3) →
  ((map-reduce-Π-fib f C) ∘ (inv-map-reduce-Π-fib f C)) ~ id
issec-inv-map-reduce-Π-fib f C h = refl

isretr-inv-map-reduce-Π-fib' :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (C : (y : B) (z : fib f y) → UU l3) →
  (h : (y : B) (z : fib f y) → C y z) (y : B) →
  (inv-map-reduce-Π-fib f C ((map-reduce-Π-fib f C) h) y) ~ (h y)
isretr-inv-map-reduce-Π-fib' f C h .(f z) (pair z refl) = refl

isretr-inv-map-reduce-Π-fib :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (C : (y : B) (z : fib f y) → UU l3) →
  ((inv-map-reduce-Π-fib f C) ∘ (map-reduce-Π-fib f C)) ~ id
isretr-inv-map-reduce-Π-fib f C h =
  eq-htpy (λ y → eq-htpy (isretr-inv-map-reduce-Π-fib' f C h y))

is-equiv-map-reduce-Π-fib :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (C : (y : B) (z : fib f y) → UU l3) →
  is-equiv (map-reduce-Π-fib f C)
is-equiv-map-reduce-Π-fib f C =
  is-equiv-has-inverse
    ( inv-map-reduce-Π-fib f C)
    ( issec-inv-map-reduce-Π-fib f C)
    ( isretr-inv-map-reduce-Π-fib f C)

reduce-Π-fib' :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (C : (y : B) (z : fib f y) → UU l3) →
  ((y : B) (z : fib f y) → C y z) ≃ ((x : A) → C (f x) (pair x refl))
reduce-Π-fib' f C =
  pair (map-reduce-Π-fib f C) (is-equiv-map-reduce-Π-fib f C)

reduce-Π-fib :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (C : B → UU l3) → ((y : B) → fib f y → C y) ≃ ((x : A) → C (f x))
reduce-Π-fib f C = reduce-Π-fib' f (λ y z → C y)

-- Exercise 13.16

hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → UU (l1 ⊔ (l2 ⊔ l3))
hom-slice {A = A} {B} f g = Σ (A → B) (λ h → f ~ (g ∘ h))

map-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → hom-slice f g → A → B
map-hom-slice f g h = pr1 h

triangle-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (h : hom-slice f g) →
  f ~ (g ∘ (map-hom-slice f g h))
triangle-hom-slice f g h = pr2 h

{- We characterize the identity type of hom-slice -}

htpy-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (h h' : hom-slice f g) → UU (l1 ⊔ l2 ⊔ l3)
htpy-hom-slice f g h h' =
  Σ ( map-hom-slice f g h ~ map-hom-slice f g h')
    ( λ K →
      ( (triangle-hom-slice f g h) ∙h (g ·l K)) ~
      ( triangle-hom-slice f g h'))

refl-htpy-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (h : hom-slice f g) →
  htpy-hom-slice f g h h
refl-htpy-hom-slice f g h = pair refl-htpy right-unit-htpy

htpy-hom-slice-eq :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (h h' : hom-slice f g) →
  Id h h' → htpy-hom-slice f g h h'
htpy-hom-slice-eq f g h .h refl = refl-htpy-hom-slice f g h

is-contr-total-htpy-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (h : hom-slice f g) →
  is-contr (Σ (hom-slice f g) (htpy-hom-slice f g h))
is-contr-total-htpy-hom-slice f g h =
  is-contr-total-Eq-structure
    ( λ h' H' K → ((triangle-hom-slice f g h) ∙h (g ·l K)) ~ H')
    ( is-contr-total-htpy (map-hom-slice f g h))
    ( pair (map-hom-slice f g h) refl-htpy)
    ( is-contr-equiv'
      ( Σ ( f ~ (g ∘ (map-hom-slice f g h)))
          ( λ H' → (triangle-hom-slice f g h) ~ H'))
      ( equiv-tot (equiv-concat-htpy right-unit-htpy))
      ( is-contr-total-htpy (triangle-hom-slice f g h)))

is-equiv-htpy-hom-slice-eq :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (h h' : hom-slice f g) →
  is-equiv (htpy-hom-slice-eq f g h h')
is-equiv-htpy-hom-slice-eq f g h =
  fundamental-theorem-id h
    ( refl-htpy-hom-slice f g h)
    ( is-contr-total-htpy-hom-slice f g h)
    ( htpy-hom-slice-eq f g h)

eq-htpy-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (h h' : hom-slice f g) →
  htpy-hom-slice f g h h' → Id h h'
eq-htpy-hom-slice f g h h' = map-inv-is-equiv (is-equiv-htpy-hom-slice-eq f g h h')

{- Now we relate morphisms in the slice category to fiberwise morphisms -}
  
fiberwise-hom-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  hom-slice f g → (x : X) → (fib f x) → (fib g x)
fiberwise-hom-hom-slice f g (pair h H) = fib-triangle f g h H

hom-slice-fiberwise-hom :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  ((x : X) → (fib f x) → (fib g x)) → hom-slice f g
hom-slice-fiberwise-hom f g α =
  pair
    ( λ a → pr1 (α (f a) (pair a refl)))
    ( λ a → inv (pr2 (α (f a) (pair a refl))))

issec-hom-slice-fiberwise-hom-eq-htpy :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (α : (x : X) → (fib f x) → (fib g x)) (x : X) →
  (fiberwise-hom-hom-slice f g (hom-slice-fiberwise-hom f g α) x) ~ (α x)
issec-hom-slice-fiberwise-hom-eq-htpy f g α .(f a) (pair a refl) =
  eq-pair-Σ refl (inv-inv (pr2 (α (f a) (pair a refl))))

issec-hom-slice-fiberwise-hom :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  ((fiberwise-hom-hom-slice f g) ∘ (hom-slice-fiberwise-hom f g)) ~ id
issec-hom-slice-fiberwise-hom f g α =
  eq-htpy (λ x → eq-htpy (issec-hom-slice-fiberwise-hom-eq-htpy f g α x))

isretr-hom-slice-fiberwise-hom :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  ((hom-slice-fiberwise-hom f g) ∘ (fiberwise-hom-hom-slice f g)) ~ id
isretr-hom-slice-fiberwise-hom f g (pair h H) =
  eq-pair-Σ refl (eq-htpy (λ a → (inv-inv (H a))))

abstract
  is-equiv-fiberwise-hom-hom-slice :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
    (f : A → X) (g : B → X) →
    is-equiv (fiberwise-hom-hom-slice f g)
  is-equiv-fiberwise-hom-hom-slice f g =
    is-equiv-has-inverse
      ( hom-slice-fiberwise-hom f g)
      ( issec-hom-slice-fiberwise-hom f g)
      ( isretr-hom-slice-fiberwise-hom f g)

abstract
  is-equiv-hom-slice-fiberwise-hom :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
    (f : A → X) (g : B → X) →
    is-equiv (hom-slice-fiberwise-hom f g)
  is-equiv-hom-slice-fiberwise-hom f g =
    is-equiv-has-inverse
      ( fiberwise-hom-hom-slice f g)
      ( isretr-hom-slice-fiberwise-hom f g)
      ( issec-hom-slice-fiberwise-hom f g)

equiv-slice :
  {l1 l2 l3 : Level} (X : UU l1) {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → UU (l1 ⊔ (l2 ⊔ l3))
equiv-slice X {A} {B} f g = Σ (A ≃ B) (λ e → f ~ (g ∘ (map-equiv e)))

hom-slice-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  equiv-slice X f g → hom-slice f g
hom-slice-equiv-slice f g (pair (pair h is-equiv-h) H) = pair h H

{- We first prove two closely related generic lemmas that establishes 
   equivalences of subtypes -}

abstract
  is-equiv-subtype-is-equiv :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
    {P : A → UU l3} {Q : B → UU l4}
    (is-subtype-P : is-subtype P) (is-subtype-Q : is-subtype Q)
    (f : A → B) (g : (x : A) → P x → Q (f x)) →
    is-equiv f → ((x : A) → (Q (f x)) → P x) → is-equiv (map-Σ Q f g)
  is-equiv-subtype-is-equiv {Q = Q} is-subtype-P is-subtype-Q f g is-equiv-f h =
    is-equiv-map-Σ Q f g is-equiv-f
      ( λ x → is-equiv-is-prop (is-subtype-P x) (is-subtype-Q (f x)) (h x))

abstract
  is-equiv-subtype-is-equiv' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
    {P : A → UU l3} {Q : B → UU l4}
    (is-subtype-P : is-subtype P) (is-subtype-Q : is-subtype Q)
    (f : A → B) (g : (x : A) → P x → Q (f x)) →
    (is-equiv-f : is-equiv f) →
    ((y : B) → (Q y) → P (map-inv-is-equiv is-equiv-f y)) →
    is-equiv (map-Σ Q f g)
  is-equiv-subtype-is-equiv' {P = P} {Q}
    is-subtype-P is-subtype-Q f g is-equiv-f h =
    is-equiv-map-Σ Q f g is-equiv-f
      ( λ x → is-equiv-is-prop (is-subtype-P x) (is-subtype-Q (f x))
        ( (tr P (isretr-map-inv-is-equiv is-equiv-f x)) ∘ (h (f x))))

abstract
  is-fiberwise-equiv-fiberwise-equiv-equiv-slice :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
    (f : A → X) (g : B → X)
    (t : hom-slice f g) → is-equiv (pr1 t) →
    is-fiberwise-equiv (fiberwise-hom-hom-slice f g t)
  is-fiberwise-equiv-fiberwise-equiv-equiv-slice f g (pair h H) =
    is-fiberwise-equiv-is-equiv-triangle f g h H

left-factor-fiberwise-equiv-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  Σ (hom-slice f g) (λ hH → is-equiv (pr1 hH)) →
  Σ ((x : X) → (fib f x) → (fib g x)) is-fiberwise-equiv
left-factor-fiberwise-equiv-equiv-slice f g =
  map-Σ
    ( is-fiberwise-equiv)
    ( fiberwise-hom-hom-slice f g)
    ( is-fiberwise-equiv-fiberwise-equiv-equiv-slice f g)

swap-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  equiv-slice X f g →
  Σ (hom-slice f g) (λ hH → is-equiv (pr1 hH))
swap-equiv-slice {A = A} {B} f g =
  map-equiv-double-structure is-equiv (λ h → f ~ (g ∘ h))

abstract
  is-equiv-swap-equiv-slice :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
    (f : A → X) (g : B → X) →
    is-equiv (swap-equiv-slice f g)
  is-equiv-swap-equiv-slice f g =
    is-equiv-map-equiv (equiv-double-structure is-equiv (λ h → f ~ (g ∘ h)))

abstract
  fiberwise-equiv-equiv-slice :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
    (f : A → X) (g : B → X) →
    equiv-slice X f g → Σ ((x : X) → (fib f x) → (fib g x)) is-fiberwise-equiv
  fiberwise-equiv-equiv-slice {X = X} {A} {B} f g =
    ( left-factor-fiberwise-equiv-equiv-slice f g) ∘
    ( swap-equiv-slice f g)

abstract
  is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
    (f : A → X) (g : B → X) →
    (t : hom-slice f g) →
    ((x : X) → is-equiv (fiberwise-hom-hom-slice f g t x)) →
    is-equiv (pr1 t)
  is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice
    f g (pair h H) =
    is-equiv-triangle-is-fiberwise-equiv f g h H

abstract
  is-equiv-fiberwise-equiv-equiv-slice :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
    (f : A → X) (g : B → X) →
    is-equiv (fiberwise-equiv-equiv-slice f g)
  is-equiv-fiberwise-equiv-equiv-slice {X = X} {A} {B} f g =
    is-equiv-comp
      ( fiberwise-equiv-equiv-slice f g)
      ( left-factor-fiberwise-equiv-equiv-slice f g)
      ( swap-equiv-slice f g)
      ( refl-htpy)
      ( is-equiv-swap-equiv-slice f g)
      ( is-equiv-subtype-is-equiv
        ( λ t → is-subtype-is-equiv (pr1 t))
        ( λ α → is-prop-Π (λ x → is-subtype-is-equiv (α x)))
        ( fiberwise-hom-hom-slice f g)
        ( is-fiberwise-equiv-fiberwise-equiv-equiv-slice f g)
        ( is-equiv-fiberwise-hom-hom-slice f g)
        ( is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice
          f g))

-- Exercise 13.17

hom-over-morphism :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : X → Y) (f : A → X) (g : B → Y) → UU (l1 ⊔ (l2 ⊔ l4))
hom-over-morphism i f g = hom-slice (i ∘ f) g

fiberwise-hom-hom-over-morphism :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : X → Y) (f : A → X) (g : B → Y) →
  hom-over-morphism i f g → (x : X) → (fib f x) → (fib g (i x))
fiberwise-hom-hom-over-morphism i f g (pair h H) .(f a) (pair a refl) =
  pair (h a) (inv (H a))

hom-over-morphism-fiberwise-hom :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : X → Y) (f : A → X) (g : B → Y) →
  ((x : X) → (fib f x) → (fib g (i x))) → hom-over-morphism i f g
hom-over-morphism-fiberwise-hom i f g α =
  pair
    ( λ a → pr1 (α (f a) (pair a refl)))
    ( λ a → inv (pr2 (α (f a) (pair a refl))))

issec-hom-over-morphism-fiberwise-hom-eq-htpy :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : X → Y) (f : A → X) (g : B → Y) →
  (α : (x : X) → (fib f x) → (fib g (i x))) (x : X) →
  ( fiberwise-hom-hom-over-morphism i f g
    ( hom-over-morphism-fiberwise-hom i f g α) x) ~ (α x)
issec-hom-over-morphism-fiberwise-hom-eq-htpy i f g α .(f a) (pair a refl) =
  eq-pair-Σ refl (inv-inv (pr2 (α (f a) (pair a refl))))

issec-hom-over-morphism-fiberwise-hom :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : X → Y) (f : A → X) (g : B → Y) →
  ( ( fiberwise-hom-hom-over-morphism i f g) ∘
    ( hom-over-morphism-fiberwise-hom i f g)) ~ id
issec-hom-over-morphism-fiberwise-hom i f g α =
  eq-htpy
    ( λ x →
      ( eq-htpy
        ( issec-hom-over-morphism-fiberwise-hom-eq-htpy i f g α x)))

isretr-hom-over-morphism-fiberwise-hom :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : X → Y) (f : A → X) (g : B → Y) →
  ( ( hom-over-morphism-fiberwise-hom i f g) ∘
    ( fiberwise-hom-hom-over-morphism i f g)) ~ id
isretr-hom-over-morphism-fiberwise-hom i f g (pair h H) =
  eq-pair-Σ refl (eq-htpy (λ a → (inv-inv (H a))))

abstract
  is-equiv-fiberwise-hom-hom-over-morphism :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
    (i : X → Y) (f : A → X) (g : B → Y) →
    is-equiv (fiberwise-hom-hom-over-morphism i f g)
  is-equiv-fiberwise-hom-hom-over-morphism i f g =
    is-equiv-has-inverse
      ( hom-over-morphism-fiberwise-hom i f g)
      ( issec-hom-over-morphism-fiberwise-hom i f g)
      ( isretr-hom-over-morphism-fiberwise-hom i f g)

abstract
  is-equiv-hom-over-morphism-fiberwise-hom :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
    (i : X → Y) (f : A → X) (g : B → Y) →
    is-equiv (hom-over-morphism-fiberwise-hom i f g)
  is-equiv-hom-over-morphism-fiberwise-hom i f g =
    is-equiv-has-inverse
      ( fiberwise-hom-hom-over-morphism i f g)
      ( isretr-hom-over-morphism-fiberwise-hom i f g)
      ( issec-hom-over-morphism-fiberwise-hom i f g)

-- Exercise 13.18

set-isomorphism :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2) → UU (l1 ⊔ l2)
set-isomorphism A B =
  Σ ((pr1 A) → (pr1 B)) has-inverse

has-inverse-is-coherently-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-coherently-invertible f → has-inverse f
has-inverse-is-coherently-invertible f =
  tot (λ g → tot (λ G → pr1))

set-isomorphism-equiv-fiberwise :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2) →
  (f : (pr1 A) → (pr1 B)) → is-equiv f → has-inverse f
set-isomorphism-equiv-fiberwise A B f =
  ( has-inverse-is-coherently-invertible f) ∘
  ( is-coherently-invertible-is-equiv f)

abstract
  is-equiv-has-inverse-is-coherently-invertible-is-set :
    {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2) (f : (pr1 A) → (pr1 B)) →
    is-equiv (has-inverse-is-coherently-invertible f)
  is-equiv-has-inverse-is-coherently-invertible-is-set
    (pair A is-set-A) (pair B is-set-B) f =
    is-equiv-tot-is-fiberwise-equiv
      ( λ g → is-equiv-tot-is-fiberwise-equiv
        ( λ G → is-equiv-pr1-is-contr
          ( λ H → is-contr-Π
            ( λ x → is-set-B _ _ (G (f x)) (ap f (H x))))))

abstract
  is-fiberwise-equiv-set-isomorphism-equiv-fiberwise :
    {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2) →
    is-fiberwise-equiv (set-isomorphism-equiv-fiberwise A B)
  is-fiberwise-equiv-set-isomorphism-equiv-fiberwise A B f =
    is-equiv-comp
      ( set-isomorphism-equiv-fiberwise A B f)
      ( has-inverse-is-coherently-invertible f)
      ( is-coherently-invertible-is-equiv f)
      ( refl-htpy)
      ( is-equiv-is-coherently-invertible-is-equiv f)
      ( is-equiv-has-inverse-is-coherently-invertible-is-set A B f)

set-isomorphism-equiv :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2) →
  ((pr1 A) ≃ (pr1 B)) → set-isomorphism A B
set-isomorphism-equiv A B =
  tot (set-isomorphism-equiv-fiberwise A B)

abstract
  is-equiv-set-isomorphism-equiv :
    {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2) →
    is-equiv (set-isomorphism-equiv A B)
  is-equiv-set-isomorphism-equiv A B =
    is-equiv-tot-is-fiberwise-equiv
      ( is-fiberwise-equiv-set-isomorphism-equiv-fiberwise A B)

-- Exercise 13.19

-- We first characterize the identity type of sec f

htpy-sec :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (s t : sec f) → UU (l1 ⊔ l2)
htpy-sec f s t = Σ (pr1 s ~ pr1 t) (λ H → pr2 s ~ ((f ·l H) ∙h pr2 t))

refl-htpy-sec :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (s : sec f) → htpy-sec f s s
refl-htpy-sec f s = pair refl-htpy refl-htpy

htpy-eq-sec :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (s t : sec f) → Id s t → htpy-sec f s t
htpy-eq-sec f s .s refl = refl-htpy-sec f s

is-contr-total-htpy-sec :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (s : sec f) →
  is-contr (Σ (sec f) (htpy-sec f s))
is-contr-total-htpy-sec f s =
  is-contr-total-Eq-structure
    ( λ g G H → pr2 s ~ ((f ·l H) ∙h G))
    ( is-contr-total-htpy (pr1 s))
    ( pair (pr1 s) refl-htpy)
    ( is-contr-total-htpy (pr2 s))

is-equiv-htpy-eq-sec :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (s t : sec f) → is-equiv (htpy-eq-sec f s t)
is-equiv-htpy-eq-sec f s =
  fundamental-theorem-id s
    ( refl-htpy-sec f s)
    ( is-contr-total-htpy-sec f s)
    ( htpy-eq-sec f s)

eq-htpy-sec :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (s t : sec f) →
  (H : (pr1 s) ~ (pr1 t)) (K : (pr2 s) ~ ((f ·l H) ∙h (pr2 t))) →
  Id s t
eq-htpy-sec {f = f} s t H K =
  map-inv-is-equiv (is-equiv-htpy-eq-sec f s t) (pair H K)

sec-pr1-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  ((x : A) → B x) → sec (pr1 {B = B})
sec-pr1-Π f = pair (λ x → pair x (f x)) refl-htpy

map-inv-sec-pr1-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  sec (pr1 {B = B}) → ((x : A) → B x)
map-inv-sec-pr1-Π {B = B} s x = tr B (pr2 s x) (pr2 (pr1 s x))

{-
issec-map-inv-sec-pr1-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (sec-pr1-Π {B = B} ∘ map-inv-sec-pr1-Π {B = B}) ~ id
issec-map-inv-sec-pr1-Π {A = A} {B = B} s =
  eq-htpy-sec
    { A = Σ A B}
    { A}
    { pr1}
    ( sec-pr1-Π (map-inv-sec-pr1-Π s))
    ( s)
    ( λ x → inv (eq-pair-Σ (pr2 s x) refl))
    ( λ x → inv {x = (ap pr1 (inv (eq-pair-Σ (pr2 s x) refl))) ∙ pr2 s x} {y = refl} (ap (concat' x (pr2 s x)) (ap-inv pr1 (eq-pair-Σ (pr2 s x) refl)) ∙ {!!}))
-}

-- Exercise 13.20

-- Exercise 13.21


--------------------------------------------------------------------------------

{- Some lemmas about equivalences on Π-types -}

abstract
  is-equiv-inv-htpy-con :
    { l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
    ( H : f ~ g) (K : g ~ h) (L : f ~ h) →
    is-equiv (inv-htpy-con H K L)
  is-equiv-inv-htpy-con H K L =
    is-equiv-postcomp-Π _ (λ x → is-equiv-inv-con (H x) (K x) (L x))

equiv-inv-htpy-con :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  ( H : f ~ g) (K : g ~ h) (L : f ~ h) →
  ( (H ∙h K) ~ L) ≃ (K ~ ((inv-htpy H) ∙h L))
equiv-inv-htpy-con H K L =
  pair
    ( inv-htpy-con H K L)
    ( is-equiv-inv-htpy-con H K L)

abstract
  is-equiv-htpy-con-inv :
    { l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
    ( H : f ~ g) (K : g ~ h) (L : f ~ h) →
    is-equiv (htpy-con-inv H K L)
  is-equiv-htpy-con-inv H K L =
    is-equiv-postcomp-Π _ (λ x → is-equiv-con-inv (H x) (K x) (L x))

equiv-htpy-con-inv :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  ( H : f ~ g) (K : g ~ h) (L : f ~ h) →
  ( (H ∙h K) ~ L) ≃ (H ~ (L ∙h (inv-htpy K)))
equiv-htpy-con-inv H K L =
  pair
    ( htpy-con-inv H K L)
    ( is-equiv-htpy-con-inv H K L)

HTPY-map-equiv-Π :
  { l1 l2 l3 l4 : Level}
  { A' : UU l1} (B' : A' → UU l2) {A : UU l3} (B : A → UU l4)
  ( e e' : A' ≃ A) (H : htpy-equiv e e') →
  UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l4)))
HTPY-map-equiv-Π {A' = A'} B' {A} B e e' H =
  ( f : (a' : A') → B' a' ≃ B (map-equiv e a')) →
  ( f' : (a' : A') → B' a' ≃ B (map-equiv e' a')) →
  ( K : (a' : A') → ((tr B (H a')) ∘ (map-equiv (f a'))) ~ (map-equiv (f' a'))) →
  ( map-equiv-Π B e f) ~ (map-equiv-Π B e' f')

htpy-map-equiv-Π-refl-htpy :
  { l1 l2 l3 l4 : Level}
  { A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
  ( e : A' ≃ A) →
  HTPY-map-equiv-Π B' B e e (refl-htpy-equiv e)
htpy-map-equiv-Π-refl-htpy {B' = B'} B e f f' K =
  ( htpy-postcomp-Π
    ( λ a →
      ( tr B (issec-map-inv-is-equiv (is-equiv-map-equiv e) a)) ·l
      ( K (map-inv-is-equiv (is-equiv-map-equiv e) a)))) ·r
  ( precomp-Π (map-inv-is-equiv (is-equiv-map-equiv e)) B')

abstract
  htpy-map-equiv-Π :
    { l1 l2 l3 l4 : Level}
    { A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
    ( e e' : A' ≃ A) (H : htpy-equiv e e') →
    HTPY-map-equiv-Π B' B e e' H
  htpy-map-equiv-Π {B' = B'} B e e' H f f' K =
    ind-htpy-equiv e
      ( HTPY-map-equiv-Π B' B e)
      ( htpy-map-equiv-Π-refl-htpy B e)
      e' H f f' K
  
  comp-htpy-map-equiv-Π :
    { l1 l2 l3 l4 : Level}
    { A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
    ( e : A' ≃ A) →
    Id ( htpy-map-equiv-Π {B' = B'} B e e (refl-htpy-equiv e))
      ( ( htpy-map-equiv-Π-refl-htpy B e))
  comp-htpy-map-equiv-Π {B' = B'} B e =
    comp-htpy-equiv e
      ( HTPY-map-equiv-Π B' B e)
      ( htpy-map-equiv-Π-refl-htpy B e)

map-automorphism-Π :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  ( e : A ≃ A) (f : (a : A) → B a ≃ B (map-equiv e a)) →
  ( (a : A) → B a) → ((a : A) → B a)
map-automorphism-Π {B = B} e f =
  ( postcomp-Π (λ a → (map-inv-is-equiv (is-equiv-map-equiv (f a))))) ∘
  ( precomp-Π (map-equiv e) B)

abstract
  is-equiv-map-automorphism-Π :
    { l1 l2 : Level} {A : UU l1} {B : A → UU l2}
    ( e : A ≃ A) (f : (a : A) → B a ≃ B (map-equiv e a)) →
    is-equiv (map-automorphism-Π e f)
  is-equiv-map-automorphism-Π {B = B} e f =
    is-equiv-comp' _ _
      ( is-equiv-precomp-Π-is-equiv _ (is-equiv-map-equiv e) B)
      ( is-equiv-postcomp-Π _
        ( λ a → is-equiv-map-inv-is-equiv (is-equiv-map-equiv (f a))))

automorphism-Π :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  ( e : A ≃ A) (f : (a : A) → B a ≃ B (map-equiv e a)) →
  ( (a : A) → B a) ≃ ((a : A) → B a)
automorphism-Π e f =
  pair (map-automorphism-Π e f) (is-equiv-map-automorphism-Π e f)

--------------------------------------------------------------------------------

function-Fin :
  (k l : ℕ) → (Fin k → Fin l) ≃ Fin (exp-ℕ l k)
function-Fin zero-ℕ l =
  ( inv-left-unit-law-coprod unit) ∘e
  ( equiv-is-contr (universal-property-empty (Fin l)) is-contr-unit)
function-Fin (succ-ℕ k) l =
  ( ( prod-Fin (exp-ℕ l k) l) ∘e
    ( equiv-prod (function-Fin k l) (equiv-ev-star' (Fin l)))) ∘e
  ( equiv-universal-property-coprod (Fin l))

--------------------------------------------------------------------------------

{-
pointed-successor-algebra : {l : Level} (X : UU l) → UU l
pointed-successor-algebra X = X × (X → X)

pointed-successor-algebra-ℕ : pointed-successor-algebra ℕ
pointed-successor-algebra-ℕ = pair zero-ℕ succ-ℕ

Eq-pointed-successor-algebra :
  {l : Level} {X : UU l} (x y : pointed-successor-algebra X) → UU l
Eq-pointed-successor-algebra x y =
  (Id (pr1 x) (pr1 y)) × ((pr2 x) ~ (pr2 y))

refl-Eq-pointed-successor-algebra :
  {l : Level} {X : UU l} (x : pointed-successor-algebra X) →
  Eq-pointed-successor-algebra x x
refl-Eq-pointed-successor-algebra (pair x f) = pair refl refl-htpy

Eq-pointed-successor-algebra-eq :
  {l : Level} {X : UU l} (x y : pointed-successor-algebra X) →
  Id x y → Eq-pointed-successor-algebra x y
Eq-pointed-successor-algebra-eq x .x refl =
  refl-Eq-pointed-successor-algebra x

is-contr-total-Eq-pointed-successor-algebra :
  {l : Level} {X : UU l} (x : pointed-successor-algebra X) →
  is-contr (Σ (pointed-successor-algebra X) (Eq-pointed-successor-algebra x))
is-contr-total-Eq-pointed-successor-algebra {l} {X} x =
  is-contr-total-Eq-structure
    ( λ (y : X) (g : X → X) (p : Id (pr1 x) y) → (pr2 x) ~ g)
    ( is-contr-total-path (pr1 x))
    ( pair (pr1 x) refl)
    ( is-contr-total-htpy (pr2 x))

ev-zero-succ-ℕ :
  {l : Level} {X : UU l} → pointed-successor-algebra X → ℕ → X
ev-zero-succ-ℕ (pair x f) zero-ℕ = x
ev-zero-succ-ℕ (pair x f) (succ-ℕ n) = f (ev-zero-succ-ℕ (pair x f) n)

hom-pointed-successor-algebra :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  (H : pointed-successor-algebra X) (K : pointed-successor-algebra Y) →
  UU (l1 ⊔ l2)
hom-pointed-successor-algebra {l1} {l2} {X} {Y} H K =
  Σ ( X → Y)
    ( λ h →
      ( Id (h (pr1 H)) (pr1 K)) ×
      ( (x : X) → Id (h (pr2 H x)) (pr2 K (h x))))

map-hom-pointed-successor-algebra :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  (H : pointed-successor-algebra X) (K : pointed-successor-algebra Y) →
  (h : hom-pointed-successor-algebra H K) → X → Y
map-hom-pointed-successor-algebra H K h = pr1 h

comp-base-hom-pointed-successor-algebra :
  {l1 l2 : Level} {X : UU l1} {Y : UU l1}
  (H : pointed-successor-algebra X) (K : pointed-successor-algebra Y) →
  (h : hom-pointed-successor-algebra H K) →
  Id (map-hom-pointed-successor-algebra H K h (pr1 H)) (pr1 K)
comp-base-hom-pointed-successor-algebra H K h =
  pr1 (pr2 h)

comp-succ-hom-pointed-successor-algebra :
  {l1 l2 : Level} {X : UU l1} {Y : UU l1}
  (H : pointed-successor-algebra X) (K : pointed-successor-algebra Y) →
  (h : hom-pointed-successor-algebra H K) →
  (map-hom-pointed-successor-algebra H K h ∘ (pr2 H)) ~
  (pr2 K ∘ (map-hom-pointed-successor-algebra H K h))
comp-succ-hom-pointed-successor-algebra H K h =
  pr2 (pr2 h)

hom-is-initial-pointed-successor-algebra-ℕ :
  {l1 : Level} {X : UU l1} (x : pointed-successor-algebra X) →
  hom-pointed-successor-algebra pointed-successor-algebra-ℕ x
hom-is-initial-pointed-successor-algebra-ℕ x =
  pair
    ( ind-ℕ (pr1 x) (λ n → (pr2 x)))
    ( pair refl refl-htpy)

htpy-hom-pointed-successor-algebra :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  (H : pointed-successor-algebra X) (K : pointed-successor-algebra Y) →
  (h1 h2 : hom-pointed-successor-algebra H K) → UU (l1 ⊔ l2)
htpy-hom-pointed-successor-algebra H K h1 h2 =
  Σ ( (pr1 h1) ~ pr1 h2)
    ( λ α →
      {! Id (comp-base-hom-pointed-successor-algebra H K h1) ? × ?!})

-}
