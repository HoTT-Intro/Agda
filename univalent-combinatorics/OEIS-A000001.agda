{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.OEIS-A000001 where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public

UU : (i : Level) → Set (lsuc i)
UU i = Set i

data raise (l : Level) {l1 : Level} (A : UU l1) : UU (l1 ⊔ l) where
  map-raise : A → raise l A

map-inv-raise :
  {l l1 : Level} {A : UU l1} → raise l A → A
map-inv-raise (map-raise x) = x

id : {i : Level} {A : UU i} → A → A
id a = a 

_∘_ :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k} →
  (B → C) → ((A → B) → (A → C))
(g ∘ f) a = g (f a)

const : {i j : Level} (A : UU i) (B : UU j) (b : B) → A → B
const A B b x = b

data unit : UU lzero where
  star : unit

raise-unit : (l : Level) → UU l
raise-unit l = raise l unit

raise-star : {l : Level} → raise l unit
raise-star = map-raise star

ind-unit : {l : Level} {P : unit → UU l} → P star → ((x : unit) → P x)
ind-unit p star = p

terminal-map : {l : Level} {A : UU l} → A → unit
terminal-map a = star

data empty : UU lzero where

raise-empty : (l : Level) → UU l
raise-empty l = raise l empty

ind-empty : {l : Level} {P : empty → UU l} → ((x : empty) → P x)
ind-empty ()

ex-falso : {l : Level} {A : UU l} → empty → A
ex-falso = ind-empty

¬ : {l : Level} → UU l → UU l
¬ A = A → empty

¬¬ : {l : Level} → UU l → UU l
¬¬ P = ¬ (¬ P)

functor-neg : {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  (P → Q) → (¬ Q → ¬ P)
functor-neg f nq p = nq (f p)

is-empty : {l : Level} → UU l → UU l
is-empty = ¬

is-nonempty : {l : Level} → UU l → UU l
is-nonempty A = ¬ (is-empty A)

intro-dn : {l : Level} {P : UU l} → P → ¬¬ P
intro-dn p f = f p

data coprod {l1 l2 : Level} (A : UU l1) (B : UU l2) : UU (l1 ⊔ l2)  where
  inl : A → coprod A B
  inr : B → coprod A B

ind-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : coprod A B → UU l3) →
  ((x : A) → C (inl x)) → ((y : B) → C (inr y)) →
  (t : coprod A B) → C t
ind-coprod C f g (inl x) = f x
ind-coprod C f g (inr x) = g x

map-coprod :
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'} →
  (A → A') → (B → B') → coprod A B → coprod A' B'
map-coprod f g (inl x) = inl (f x)
map-coprod f g (inr y) = inr (g y)

data ℕ : UU lzero where
  zero-ℕ : ℕ
  succ-ℕ : ℕ → ℕ

one-ℕ : ℕ
one-ℕ = succ-ℕ zero-ℕ

add-ℕ : ℕ → ℕ → ℕ
add-ℕ x zero-ℕ = x
add-ℕ x (succ-ℕ y) = succ-ℕ (add-ℕ x y)

add-ℕ' : ℕ → ℕ → ℕ
add-ℕ' m n = add-ℕ n m

mul-ℕ : ℕ → (ℕ → ℕ)
mul-ℕ zero-ℕ n = zero-ℕ
mul-ℕ (succ-ℕ m) n = add-ℕ (mul-ℕ m n) n

data Σ {l1 l2 : Level} (A : UU l1) (B : A → UU l2) : UU (l1 ⊔ l2) where
  pair : (x : A) → (B x → Σ A B)

ind-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  ((x : A) (y : B x) → C (pair x y)) → ((t : Σ A B) → C t)
ind-Σ f (pair x y) = f x y

ev-pair :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  ((t : Σ A B) → C t) → (x : A) (y : B x) → C (pair x y)
ev-pair f x y = f (pair x y)

pr1 : {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → Σ A B → A
pr1 (pair a _) = a

pr2 : {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → (t : Σ A B) → B (pr1 t)
pr2 (pair a b) = b

prod : {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
prod A B = Σ A (λ a → B)

pair' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → A → B → prod A B
pair' = pair

_×_ :  {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
A × B = prod A B

map-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) → (A × B) → (C × D)
map-prod f g (pair a b) = pair (f a) (g b)

Fin : ℕ → UU lzero
Fin zero-ℕ = empty
Fin (succ-ℕ k) = coprod (Fin k) unit

inl-Fin :
  (k : ℕ) → Fin k → Fin (succ-ℕ k)
inl-Fin k = inl

data Id {i : Level} {A : UU i} (x : A) : A → UU i where
  refl : Id x x

ind-Id :
  {i j : Level} {A : UU i} (x : A) (B : (y : A) (p : Id x y) → UU j) →
  (B x refl) → (y : A) (p : Id x y) → B y p
ind-Id x B b y refl = b

is-zero-ℕ : ℕ → UU lzero
is-zero-ℕ n = Id n zero-ℕ

is-nonzero-ℕ : ℕ → UU lzero
is-nonzero-ℕ n = ¬ (is-zero-ℕ n)

is-one-ℕ : ℕ → UU lzero
is-one-ℕ n = Id n one-ℕ

is-successor-ℕ : ℕ → UU lzero
is-successor-ℕ n = Σ ℕ (λ y → Id n (succ-ℕ y))

_∙_ :
  {i : Level} {A : UU i} {x y z : A} → Id x y → Id y z → Id x z
refl ∙ q = q

concat :
  {i : Level} {A : UU i} {x y : A} → Id x y → (z : A) → Id y z → Id x z
concat p z q = p ∙ q

inv :
  {i : Level} {A : UU i} {x y : A} → Id x y → Id y x
inv refl = refl

assoc :
  {i : Level} {A : UU i} {x y z w : A} (p : Id x y) (q : Id y z)
  (r : Id z w) → Id ((p ∙ q) ∙ r) (p ∙ (q ∙ r))
assoc refl q r = refl

left-unit :
  {i : Level} {A : UU i} {x y : A} {p : Id x y} → Id (refl ∙ p) p
left-unit = refl

right-unit :
  {i : Level} {A : UU i} {x y : A} {p : Id x y} → Id (p ∙ refl) p
right-unit {p = refl} = refl

left-inv :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) →
  Id ((inv p) ∙ p) refl
left-inv refl = refl

right-inv :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) →
  Id (p ∙ (inv p)) refl
right-inv refl = refl

ap :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) {x y : A} (p : Id x y) →
  Id (f x) (f y)
ap f refl = refl

ap-id :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) → Id (ap id p) p
ap-id refl = refl

ap-comp :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k} (g : B → C)
  (f : A → B) {x y : A} (p : Id x y) → Id (ap (g ∘ f) p) (ap g (ap f p))
ap-comp g f refl = refl

ap-binary :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  {x x' : A} (p : Id x x') {y y' : B} (q : Id y y') → Id (f x y) (f x' y')
ap-binary f refl refl = refl

triangle-ap-binary :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  {x x' : A} (p : Id x x') {y y' : B} (q : Id y y') →
  Id (ap-binary f p q) (ap (λ z → f z y) p ∙ ap (f x') q)
triangle-ap-binary f refl refl = refl

triangle-ap-binary' :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  {x x' : A} (p : Id x x') {y y' : B} (q : Id y y') →
  Id (ap-binary f p q) (ap (f x) q ∙ ap (λ z → f z y') p)
triangle-ap-binary' f refl refl = refl

left-unit-ap-binary :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  {x : A} {y y' : B} (q : Id y y') →
  Id (ap-binary f refl q) (ap (f x) q)
left-unit-ap-binary f refl = refl

right-unit-ap-binary :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  {x x' : A} (p : Id x x') {y : B} →
  Id (ap-binary f p refl) (ap (λ z → f z y) p)
right-unit-ap-binary f refl = refl

tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A} (p : Id x y) → B x → B y
tr B refl b = b

apd :
  {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) {x y : A}
  (p : Id x y) → Id (tr B p (f x)) (f y)
apd f refl = refl

tr-ap :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} {D : C → UU l4}
  (f : A → C) (g : (x : A) → B x → D (f x)) {x y : A} (p : Id x y) (z : B x) →
  Id (tr D (ap f p) (g x z)) (g y (tr B p z))
tr-ap f g refl z = refl

inv-con :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) {z : A} (q : Id y z)
  (r : Id x z) → (Id (p ∙ q) r) → Id q ((inv p) ∙ r)
inv-con refl q r = id 

con-inv :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) {z : A} (q : Id y z)
  (r : Id x z) → (Id (p ∙ q) r) → Id p (r ∙ (inv q))
con-inv p refl r =
  ( λ α → α ∙ (inv right-unit)) ∘ (concat (inv right-unit) r)

zero-Fin : {k : ℕ} → Fin (succ-ℕ k)
zero-Fin {zero-ℕ} = inr star
zero-Fin {succ-ℕ k} = inl zero-Fin

is-zero-Fin : {k : ℕ} → Fin k → UU lzero
is-zero-Fin {succ-ℕ k} x = Id x zero-Fin

neg-one-Fin : {k : ℕ} → Fin (succ-ℕ k)
neg-one-Fin {k} = inr star

Eq-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  coprod A B → coprod A B → UU (l1 ⊔ l2)
Eq-coprod {l1} {l2} A B (inl x) (inl y) = raise (l1 ⊔ l2) (Id x y)
Eq-coprod {l1} {l2} A B (inl x) (inr y) = raise-empty (l1 ⊔ l2)
Eq-coprod {l1} {l2} A B (inr x) (inl y) = raise-empty (l1 ⊔ l2)
Eq-coprod {l1} {l2} A B (inr x) (inr y) = raise (l1 ⊔ l2) (Id x y)

reflexive-Eq-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  (t : coprod A B) → Eq-coprod A B t t
reflexive-Eq-coprod {l1} {l2} A B (inl x) = map-raise refl
reflexive-Eq-coprod {l1} {l2} A B (inr x) = map-raise refl

Eq-eq-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  (s t : coprod A B) → Id s t → Eq-coprod A B s t
Eq-eq-coprod A B s .s refl = reflexive-Eq-coprod A B s

eq-Eq-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (s t : coprod A B) →
  Eq-coprod A B s t → Id s t
eq-Eq-coprod A B (inl x) (inl x') = ap inl ∘ map-inv-raise
eq-Eq-coprod A B (inl x) (inr y') = ex-falso ∘ map-inv-raise
eq-Eq-coprod A B (inr y) (inl x') = ex-falso ∘ map-inv-raise
eq-Eq-coprod A B (inr y) (inr y') = ap inr ∘ map-inv-raise

Eq-Fin : (k : ℕ) → Fin k → Fin k → UU lzero
Eq-Fin (succ-ℕ k) (inl x) (inl y) = Eq-Fin k x y
Eq-Fin (succ-ℕ k) (inl x) (inr y) = empty
Eq-Fin (succ-ℕ k) (inr x) (inl y) = empty
Eq-Fin (succ-ℕ k) (inr x) (inr y) = unit

refl-Eq-Fin : {k : ℕ} (x : Fin k) → Eq-Fin k x x
refl-Eq-Fin {succ-ℕ k} (inl x) = refl-Eq-Fin x
refl-Eq-Fin {succ-ℕ k} (inr x) = star

Eq-Fin-eq : {k : ℕ} {x y : Fin k} → Id x y → Eq-Fin k x y
Eq-Fin-eq {k} refl = refl-Eq-Fin {k} _

eq-Eq-Fin :
  {k : ℕ} {x y : Fin k} → Eq-Fin k x y → Id x y
eq-Eq-Fin {succ-ℕ k} {inl x} {inl y} e = ap inl (eq-Eq-Fin e)
eq-Eq-Fin {succ-ℕ k} {inr star} {inr star} star = refl

is-injective : {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-injective {l1} {l2} {A} {B} f = ({x y : A} → Id (f x) (f y) → Id x y)

is-decidable : {l : Level} (A : UU l) → UU l
is-decidable A = coprod A (¬ A)

has-decidable-equality : {l : Level} (A : UU l) → UU l
has-decidable-equality A = (x y : A) → is-decidable (Id x y)

is-decidable-Eq-Fin : (k : ℕ) (x y : Fin k) → is-decidable (Eq-Fin k x y)
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inl y) = is-decidable-Eq-Fin k x y
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inr y) = inr id
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inl y) = inr id
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inr y) = inl star

has-decidable-equality-Fin :
  {k : ℕ} (x y : Fin k) → is-decidable (Id x y)
has-decidable-equality-Fin {k} x y =
  map-coprod eq-Eq-Fin (functor-neg Eq-Fin-eq) (is-decidable-Eq-Fin k x y)

has-decidable-equality-prod' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (f : B → has-decidable-equality A) (g : A → has-decidable-equality B) →
  has-decidable-equality (A × B)
has-decidable-equality-prod' f g (pair x y) (pair x' y') with
  f y x x' | g x y y'
... | inl refl | inl refl = inl refl
... | inl refl | inr nq = inr (λ r → nq (ap pr2 r))
... | inr np | inl refl = inr (λ r → np (ap pr1 r))
... | inr np | inr nq = inr (λ r → np (ap pr1 r))

has-decidable-equality-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-equality A → has-decidable-equality B →
  has-decidable-equality (A × B)
has-decidable-equality-prod d e =
  has-decidable-equality-prod' (λ y → d) (λ x → e)

has-decidable-equality-left-factor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-equality (A × B) → B → has-decidable-equality A
has-decidable-equality-left-factor d b x y with d (pair x b) (pair y b)
... | inl p = inl (ap pr1 p)
... | inr np = inr (λ q → np (ap (λ z → pair z b) q))

has-decidable-equality-right-factor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-equality (A × B) → A → has-decidable-equality B
has-decidable-equality-right-factor d a x y with d (pair a x) (pair a y)
... | inl p = inl (ap pr2 p)
... | inr np = inr (λ q → np (ap (pair a) q))

_↔_ : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
A ↔ B = (A → B) × (B → A)

Eq-ℕ : ℕ → ℕ → UU lzero
Eq-ℕ zero-ℕ zero-ℕ = unit
Eq-ℕ zero-ℕ (succ-ℕ n) = empty
Eq-ℕ (succ-ℕ m) zero-ℕ = empty
Eq-ℕ (succ-ℕ m) (succ-ℕ n) = Eq-ℕ m n

refl-Eq-ℕ : (n : ℕ) → Eq-ℕ n n
refl-Eq-ℕ zero-ℕ = star
refl-Eq-ℕ (succ-ℕ n) = refl-Eq-ℕ n

Eq-eq-ℕ : {x y : ℕ} → Id x y → Eq-ℕ x y
Eq-eq-ℕ {x} {.x} refl = refl-Eq-ℕ x

eq-Eq-ℕ : (x y : ℕ) → Eq-ℕ x y → Id x y
eq-Eq-ℕ zero-ℕ zero-ℕ e = refl
eq-Eq-ℕ (succ-ℕ x) (succ-ℕ y) e = ap succ-ℕ (eq-Eq-ℕ x y e)

ℤ : UU lzero
ℤ = coprod ℕ (coprod unit ℕ)

is-injective-inl :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → is-injective (inl {A = X} {B = Y})
is-injective-inl {l1} {l2} {X} {Y} {x} {y} p =
  map-inv-raise (Eq-eq-coprod X Y (inl x) (inl y) p)

is-injective-inr :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → is-injective (inr {A = X} {B = Y})
is-injective-inr {l1} {l2} {X} {Y} {x} {y} p =
  map-inv-raise (Eq-eq-coprod X Y (inr x) (inr y) p)

neq-inl-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (x : A) (y : B) →
  ¬ (Id (inl x) (inr y))
neq-inl-inr {l1} {l2} {A} {B} x y =
  map-inv-raise ∘ Eq-eq-coprod A B (inl x) (inr y)

is-decidable-unit : is-decidable unit
is-decidable-unit = inl star

is-decidable-empty : is-decidable empty
is-decidable-empty = inr id

is-decidable-coprod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (coprod A B)
is-decidable-coprod (inl a) y = inl (inl a)
is-decidable-coprod (inr na) (inl b) = inl (inr b)
is-decidable-coprod (inr na) (inr nb) = inr (ind-coprod (λ x → empty) na nb)

is-decidable-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (A × B)
is-decidable-prod (inl a) (inl b) = inl (pair a b)
is-decidable-prod (inl a) (inr g) = inr (g ∘ pr2)
is-decidable-prod (inr f) (inl b) = inr (f ∘ pr1)
is-decidable-prod (inr f) (inr g) = inr (f ∘ pr1)

is-decidable-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (A → B)
is-decidable-function-type (inl a) (inl b) = inl (λ x → b)
is-decidable-function-type (inl a) (inr g) = inr (λ h → g (h a))
is-decidable-function-type (inr f) (inl b) = inl (ex-falso ∘ f)
is-decidable-function-type (inr f) (inr g) = inl (ex-falso ∘ f)

is-decidable-neg :
  {l : Level} {A : UU l} → is-decidable A → is-decidable (¬ A)
is-decidable-neg d = is-decidable-function-type d is-decidable-empty

Peano-8 : (x : ℕ) → is-nonzero-ℕ (succ-ℕ x)
Peano-8 x p = Eq-eq-ℕ p

is-nonzero-succ-ℕ : (x : ℕ) → is-nonzero-ℕ (succ-ℕ x)
is-nonzero-succ-ℕ = Peano-8

is-nonzero-is-successor-ℕ : {x : ℕ} → is-successor-ℕ x → is-nonzero-ℕ x
is-nonzero-is-successor-ℕ {.succ-ℕ x} (pair x refl) = Peano-8 x

is-successor-is-nonzero-ℕ : {x : ℕ} → is-nonzero-ℕ x → is-successor-ℕ x
is-successor-is-nonzero-ℕ {zero-ℕ} H = ex-falso (H refl)
is-successor-is-nonzero-ℕ {succ-ℕ x} H = pair x refl

ap-add-ℕ :
  {m n m' n' : ℕ} → Id m m' → Id n n' → Id (add-ℕ m n) (add-ℕ m' n')
ap-add-ℕ p q = ap-binary add-ℕ p q

is-decidable-iff :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A → B) → (B → A) → is-decidable A → is-decidable B
is-decidable-iff f g =
  map-coprod f (functor-neg g)

is-decidable-Eq-ℕ :
  (m n : ℕ) → is-decidable (Eq-ℕ m n)
is-decidable-Eq-ℕ zero-ℕ zero-ℕ = inl star
is-decidable-Eq-ℕ zero-ℕ (succ-ℕ n) = inr id
is-decidable-Eq-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-Eq-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-Eq-ℕ m n

has-decidable-equality-ℕ : has-decidable-equality ℕ
has-decidable-equality-ℕ x y =
  is-decidable-iff (eq-Eq-ℕ x y) Eq-eq-ℕ (is-decidable-Eq-ℕ x y)

is-decidable-is-zero-ℕ : (n : ℕ) → is-decidable (is-zero-ℕ n)
is-decidable-is-zero-ℕ n = has-decidable-equality-ℕ n zero-ℕ

skip-zero-Fin : {k : ℕ} → Fin k → Fin (succ-ℕ k)
skip-zero-Fin {succ-ℕ k} (inl x) = inl (skip-zero-Fin x)
skip-zero-Fin {succ-ℕ k} (inr star) = inr star

succ-Fin : {k : ℕ} → Fin k → Fin k
succ-Fin {succ-ℕ k} (inl x) = skip-zero-Fin x
succ-Fin {succ-ℕ k} (inr star) = zero-Fin

mod-succ-ℕ : (k : ℕ) → ℕ → Fin (succ-ℕ k)
mod-succ-ℕ k zero-ℕ = zero-Fin
mod-succ-ℕ k (succ-ℕ n) = succ-Fin (mod-succ-ℕ k n)

leq-ℕ : ℕ → ℕ → UU lzero
leq-ℕ zero-ℕ m = unit
leq-ℕ (succ-ℕ n) zero-ℕ = empty
leq-ℕ (succ-ℕ n) (succ-ℕ m) = leq-ℕ n m

_≤-ℕ_ = leq-ℕ

is-lower-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) → UU l
is-lower-bound-ℕ P n =
  (m : ℕ) → P m → leq-ℕ n m

antisymmetric-leq-ℕ : (m n : ℕ) → m ≤-ℕ n → n ≤-ℕ m → Id m n
antisymmetric-leq-ℕ zero-ℕ zero-ℕ p q = refl
antisymmetric-leq-ℕ (succ-ℕ m) (succ-ℕ n) p q =
  ap succ-ℕ (antisymmetric-leq-ℕ m n p q)

minimal-element-ℕ :
  {l : Level} (P : ℕ → UU l) → UU l
minimal-element-ℕ P = Σ ℕ (λ n → (P n) × (is-lower-bound-ℕ P n))

is-decidable-fam :
  {l1 l2 : Level} {A : UU l1} (P : A → UU l2) → UU (l1 ⊔ l2)
is-decidable-fam {A = A} P = (x : A) → is-decidable (P x)

leq-zero-ℕ :
  (n : ℕ) → zero-ℕ ≤-ℕ n
leq-zero-ℕ n = star

is-minimal-element-succ-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P)
  (m : ℕ) (pm : P (succ-ℕ m))
  (is-lower-bound-m : is-lower-bound-ℕ (λ x → P (succ-ℕ x)) m) →
  ¬ (P zero-ℕ) → is-lower-bound-ℕ P (succ-ℕ m)
is-minimal-element-succ-ℕ P d m pm is-lower-bound-m neg-p0 zero-ℕ p0 =
  ind-empty (neg-p0 p0)
is-minimal-element-succ-ℕ
  P d zero-ℕ pm is-lower-bound-m neg-p0 (succ-ℕ n) psuccn =
  leq-zero-ℕ n
is-minimal-element-succ-ℕ
  P d (succ-ℕ m) pm is-lower-bound-m neg-p0 (succ-ℕ n) psuccn =
  is-minimal-element-succ-ℕ (λ x → P (succ-ℕ x)) (λ x → d (succ-ℕ x)) m pm
    ( λ m → is-lower-bound-m (succ-ℕ m))
    ( is-lower-bound-m zero-ℕ)
    ( n)
    ( psuccn)
  
well-ordering-principle-succ-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P)
  (n : ℕ) (p : P (succ-ℕ n)) →
  is-decidable (P zero-ℕ) →
  minimal-element-ℕ (λ m → P (succ-ℕ m)) → minimal-element-ℕ P
well-ordering-principle-succ-ℕ P d n p (inl p0) _ =
  pair zero-ℕ (pair p0 (λ m q → leq-zero-ℕ m))
well-ordering-principle-succ-ℕ P d n p
  (inr neg-p0) (pair m (pair pm is-min-m)) =
  pair
    ( succ-ℕ m)
    ( pair pm
      ( is-minimal-element-succ-ℕ P d m pm is-min-m neg-p0))

well-ordering-principle-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) →
  Σ ℕ P → minimal-element-ℕ P
well-ordering-principle-ℕ P d (pair zero-ℕ p) =
  pair zero-ℕ (pair p (λ m q → leq-zero-ℕ m))
well-ordering-principle-ℕ P d (pair (succ-ℕ n) p) =
  well-ordering-principle-succ-ℕ P d n p (d zero-ℕ)
    ( well-ordering-principle-ℕ
      ( λ m → P (succ-ℕ m))
      ( λ m → d (succ-ℕ m))
      ( pair n p))

number-well-ordering-principle-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) (nP : Σ ℕ P) → ℕ
number-well-ordering-principle-ℕ P d nP =
  pr1 (well-ordering-principle-ℕ P d nP)

nat-Fin : {k : ℕ} → Fin k → ℕ
nat-Fin {succ-ℕ k} (inl x) = nat-Fin x
nat-Fin {succ-ℕ k} (inr x) = k

le-ℕ : ℕ → ℕ → UU lzero
le-ℕ m zero-ℕ = empty
le-ℕ zero-ℕ (succ-ℕ m) = unit
le-ℕ (succ-ℕ n) (succ-ℕ m) = le-ℕ n m

_<_ = le-ℕ

is-injective-succ-ℕ : is-injective succ-ℕ
is-injective-succ-ℕ {x} {y} e = eq-Eq-ℕ x y (Eq-eq-ℕ e)

neq-le-ℕ : {x y : ℕ} → le-ℕ x y → ¬ (Id x y)
neq-le-ℕ {zero-ℕ} {succ-ℕ y} H = Peano-8 y ∘ inv
neq-le-ℕ {succ-ℕ x} {succ-ℕ y} H p = neq-le-ℕ H (is-injective-succ-ℕ p)

dist-ℕ : ℕ → ℕ → ℕ
dist-ℕ zero-ℕ n = n
dist-ℕ (succ-ℕ m) zero-ℕ = succ-ℕ m
dist-ℕ (succ-ℕ m) (succ-ℕ n) = dist-ℕ m n

anti-reflexive-le-ℕ : (n : ℕ) → ¬ (n < n)
anti-reflexive-le-ℕ zero-ℕ = ind-empty
anti-reflexive-le-ℕ (succ-ℕ n) = anti-reflexive-le-ℕ n

transitive-le-ℕ : (n m l : ℕ) → (le-ℕ n m) → (le-ℕ m l) → (le-ℕ n l)
transitive-le-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ l) p q = star
transitive-le-ℕ (succ-ℕ n) (succ-ℕ m) (succ-ℕ l) p q =
  transitive-le-ℕ n m l p q

succ-le-ℕ : (n : ℕ) → le-ℕ n (succ-ℕ n)
succ-le-ℕ zero-ℕ = star
succ-le-ℕ (succ-ℕ n) = succ-le-ℕ n

preserves-le-succ-ℕ :
  (m n : ℕ) → le-ℕ m n → le-ℕ m (succ-ℕ n)
preserves-le-succ-ℕ m n H =
  transitive-le-ℕ m n (succ-ℕ n) H (succ-le-ℕ n)

strict-upper-bound-dist-ℕ :
  (b x y : ℕ) → le-ℕ x b → le-ℕ y b → le-ℕ (dist-ℕ x y) b
strict-upper-bound-dist-ℕ (succ-ℕ b) zero-ℕ y H K = K
strict-upper-bound-dist-ℕ (succ-ℕ b) (succ-ℕ x) zero-ℕ H K = H
strict-upper-bound-dist-ℕ (succ-ℕ b) (succ-ℕ x) (succ-ℕ y) H K =
  preserves-le-succ-ℕ (dist-ℕ x y) b (strict-upper-bound-dist-ℕ b x y H K)

strict-upper-bound-nat-Fin : {k : ℕ} (x : Fin k) → le-ℕ (nat-Fin x) k
strict-upper-bound-nat-Fin {succ-ℕ k} (inl x) =
  transitive-le-ℕ
    ( nat-Fin x)
    ( k)
    ( succ-ℕ k)
    ( strict-upper-bound-nat-Fin x)
    ( succ-le-ℕ k)
strict-upper-bound-nat-Fin {succ-ℕ k} (inr star) =
  succ-le-ℕ k

is-injective-nat-Fin : {k : ℕ} → is-injective (nat-Fin {k})
is-injective-nat-Fin {succ-ℕ k} {inl x} {inl y} p =
  ap inl (is-injective-nat-Fin p)
is-injective-nat-Fin {succ-ℕ k} {inl x} {inr star} p =
  ex-falso (neq-le-ℕ (strict-upper-bound-nat-Fin x) p)
is-injective-nat-Fin {succ-ℕ k} {inr star} {inl y} p =
  ex-falso (neq-le-ℕ (strict-upper-bound-nat-Fin y) (inv p))
is-injective-nat-Fin {succ-ℕ k} {inr star} {inr star} p =
  refl

div-ℕ : ℕ → ℕ → UU lzero
div-ℕ m n = Σ ℕ (λ k → Id (mul-ℕ k m) n)

cong-ℕ :
  ℕ → ℕ → ℕ → UU lzero
cong-ℕ k x y = div-ℕ k (dist-ℕ x y)

_≡_mod_ : ℕ → ℕ → ℕ → UU lzero
x ≡ y mod k = cong-ℕ k x y

contradiction-le-ℕ : (m n : ℕ) → le-ℕ m n → ¬ (n ≤-ℕ m)
contradiction-le-ℕ zero-ℕ (succ-ℕ n) H K = K
contradiction-le-ℕ (succ-ℕ m) (succ-ℕ n) H = contradiction-le-ℕ m n H

concatenate-leq-eq-ℕ :
  (m : ℕ) {n n' : ℕ} → m ≤-ℕ n → Id n n' → m ≤-ℕ n'
concatenate-leq-eq-ℕ m H refl = H

refl-leq-ℕ : (n : ℕ) → n ≤-ℕ n
refl-leq-ℕ zero-ℕ = star
refl-leq-ℕ (succ-ℕ n) = refl-leq-ℕ n

transitive-leq-ℕ :
  (n m l : ℕ) → (n ≤-ℕ m) → (m ≤-ℕ l) → (n ≤-ℕ l)
transitive-leq-ℕ zero-ℕ m l p q = star
transitive-leq-ℕ (succ-ℕ n) (succ-ℕ m) (succ-ℕ l) p q =
  transitive-leq-ℕ n m l p q

succ-leq-ℕ : (n : ℕ) → n ≤-ℕ (succ-ℕ n)
succ-leq-ℕ zero-ℕ = star
succ-leq-ℕ (succ-ℕ n) = succ-leq-ℕ n

leq-add-ℕ : (m n : ℕ) → m ≤-ℕ (add-ℕ m n)
leq-add-ℕ m zero-ℕ = refl-leq-ℕ m
leq-add-ℕ m (succ-ℕ n) =
  transitive-leq-ℕ m (add-ℕ m n) (succ-ℕ (add-ℕ m n))
    ( leq-add-ℕ m n)
    ( succ-leq-ℕ (add-ℕ m n))

right-unit-law-add-ℕ :
  (x : ℕ) → Id (add-ℕ x zero-ℕ) x
right-unit-law-add-ℕ x = refl

left-unit-law-add-ℕ :
  (x : ℕ) → Id (add-ℕ zero-ℕ x) x
left-unit-law-add-ℕ zero-ℕ = refl
left-unit-law-add-ℕ (succ-ℕ x) = ap succ-ℕ (left-unit-law-add-ℕ x)

left-successor-law-add-ℕ :
  (x y : ℕ) → Id (add-ℕ (succ-ℕ x) y) (succ-ℕ (add-ℕ x y))
left-successor-law-add-ℕ x zero-ℕ = refl
left-successor-law-add-ℕ x (succ-ℕ y) =
  ap succ-ℕ (left-successor-law-add-ℕ x y)
                                        
right-successor-law-add-ℕ :
  (x y : ℕ) → Id (add-ℕ x (succ-ℕ y)) (succ-ℕ (add-ℕ x y))
right-successor-law-add-ℕ x y = refl

associative-add-ℕ :
  (x y z : ℕ) → Id (add-ℕ (add-ℕ x y) z) (add-ℕ x (add-ℕ y z))
associative-add-ℕ x y zero-ℕ = refl 
associative-add-ℕ x y (succ-ℕ z) = ap succ-ℕ (associative-add-ℕ x y z)

commutative-add-ℕ : (x y : ℕ) → Id (add-ℕ x y) (add-ℕ y x)
commutative-add-ℕ zero-ℕ y = left-unit-law-add-ℕ y
commutative-add-ℕ (succ-ℕ x) y =
  (left-successor-law-add-ℕ x y) ∙ (ap succ-ℕ (commutative-add-ℕ x y))

leq-add-ℕ' : (m n : ℕ) → m ≤-ℕ (add-ℕ n m)
leq-add-ℕ' m n =
  concatenate-leq-eq-ℕ m (leq-add-ℕ m n) (commutative-add-ℕ m n)

is-zero-div-ℕ :
  (d x : ℕ) → le-ℕ x d → div-ℕ d x → is-zero-ℕ x
is-zero-div-ℕ d zero-ℕ H D = refl
is-zero-div-ℕ d (succ-ℕ x) H (pair (succ-ℕ k) p) =
  ex-falso
    ( contradiction-le-ℕ
      ( succ-ℕ x) d H
      ( concatenate-leq-eq-ℕ d
        ( leq-add-ℕ' d (mul-ℕ k d)) p))

eq-dist-ℕ :
  (m n : ℕ) → is-zero-ℕ (dist-ℕ m n) → Id m n
eq-dist-ℕ zero-ℕ zero-ℕ p = refl
eq-dist-ℕ (succ-ℕ m) (succ-ℕ n) p = ap succ-ℕ (eq-dist-ℕ m n p)

eq-cong-le-dist-ℕ :
  (k x y : ℕ) → le-ℕ (dist-ℕ x y) k → cong-ℕ k x y → Id x y
eq-cong-le-dist-ℕ k x y H K =
  eq-dist-ℕ x y (is-zero-div-ℕ k (dist-ℕ x y) H K)

eq-cong-le-ℕ :
  (k x y : ℕ) → le-ℕ x k → le-ℕ y k → cong-ℕ k x y → Id x y
eq-cong-le-ℕ k x y H K =
  eq-cong-le-dist-ℕ k x y (strict-upper-bound-dist-ℕ k x y H K)

left-zero-law-mul-ℕ :
  (x : ℕ) → Id (mul-ℕ zero-ℕ x) zero-ℕ
left-zero-law-mul-ℕ x = refl

right-zero-law-mul-ℕ :
  (x : ℕ) → Id (mul-ℕ x zero-ℕ) zero-ℕ
right-zero-law-mul-ℕ zero-ℕ = refl
right-zero-law-mul-ℕ (succ-ℕ x) =
  ( right-unit-law-add-ℕ (mul-ℕ x zero-ℕ)) ∙ (right-zero-law-mul-ℕ x)

dist-eq-ℕ' :
  (n : ℕ) → is-zero-ℕ (dist-ℕ n n)
dist-eq-ℕ' zero-ℕ = refl
dist-eq-ℕ' (succ-ℕ n) = dist-eq-ℕ' n

dist-eq-ℕ :
  (m n : ℕ) → Id m n → is-zero-ℕ (dist-ℕ m n)
dist-eq-ℕ m .m refl = dist-eq-ℕ' m

refl-cong-ℕ :
  (k x : ℕ) → cong-ℕ k x x
refl-cong-ℕ k x =
  pair zero-ℕ ((left-zero-law-mul-ℕ (succ-ℕ k)) ∙ (inv (dist-eq-ℕ x x refl)))

cong-identification-ℕ :
  (k : ℕ) {x y : ℕ} → Id x y → cong-ℕ k x y
cong-identification-ℕ k {x} refl = refl-cong-ℕ k x

is-zero-nat-zero-Fin : {k : ℕ} → is-zero-ℕ (nat-Fin (zero-Fin {k}))
is-zero-nat-zero-Fin {zero-ℕ} = refl 
is-zero-nat-zero-Fin {succ-ℕ k} = is-zero-nat-zero-Fin {k}

cases-order-three-elements-ℕ :
  (x y z : ℕ) → UU lzero
cases-order-three-elements-ℕ x y z =
  coprod
    ( coprod ((leq-ℕ x y) × (leq-ℕ y z)) ((leq-ℕ x z) × (leq-ℕ z y)))
    ( coprod
      ( coprod ((leq-ℕ y z) × (leq-ℕ z x)) ((leq-ℕ y x) × (leq-ℕ x z)))
      ( coprod ((leq-ℕ z x) × (leq-ℕ x y)) ((leq-ℕ z y) × (leq-ℕ y x))))

decide-leq-ℕ :
  (m n : ℕ) → coprod (m ≤-ℕ n) (n ≤-ℕ m)
decide-leq-ℕ zero-ℕ zero-ℕ = inl star
decide-leq-ℕ zero-ℕ (succ-ℕ n) = inl star
decide-leq-ℕ (succ-ℕ m) zero-ℕ = inr star
decide-leq-ℕ (succ-ℕ m) (succ-ℕ n) = decide-leq-ℕ m n

order-three-elements-ℕ :
  (x y z : ℕ) → cases-order-three-elements-ℕ x y z
order-three-elements-ℕ zero-ℕ zero-ℕ zero-ℕ = inl (inl (pair star star))
order-three-elements-ℕ zero-ℕ zero-ℕ (succ-ℕ z) = inl (inl (pair star star))
order-three-elements-ℕ zero-ℕ (succ-ℕ y) zero-ℕ = inl (inr (pair star star))
order-three-elements-ℕ zero-ℕ (succ-ℕ y) (succ-ℕ z) =
  inl (map-coprod (pair star) (pair star) (decide-leq-ℕ y z))
order-three-elements-ℕ (succ-ℕ x) zero-ℕ zero-ℕ =
  inr (inl (inl (pair star star)))
order-three-elements-ℕ (succ-ℕ x) zero-ℕ (succ-ℕ z) =
  inr (inl (map-coprod (pair star) (pair star) (decide-leq-ℕ z x)))
order-three-elements-ℕ (succ-ℕ x) (succ-ℕ y) zero-ℕ =
  inr (inr (map-coprod (pair star) (pair star) (decide-leq-ℕ x y)))
order-three-elements-ℕ (succ-ℕ x) (succ-ℕ y) (succ-ℕ z) =
  order-three-elements-ℕ x y z

cases-dist-ℕ :
  (x y z : ℕ) → UU lzero
cases-dist-ℕ x y z = 
  coprod
    ( Id (add-ℕ (dist-ℕ x y) (dist-ℕ y z)) (dist-ℕ x z))
    ( coprod
      ( Id (add-ℕ (dist-ℕ y z) (dist-ℕ x z)) (dist-ℕ x y))
      ( Id (add-ℕ (dist-ℕ x z) (dist-ℕ x y)) (dist-ℕ y z)))

is-additive-right-inverse-dist-ℕ :
  (x y : ℕ) → x ≤-ℕ y → Id (add-ℕ x (dist-ℕ x y)) y
is-additive-right-inverse-dist-ℕ zero-ℕ zero-ℕ H = refl
is-additive-right-inverse-dist-ℕ zero-ℕ (succ-ℕ y) star = left-unit-law-add-ℕ (succ-ℕ y)
is-additive-right-inverse-dist-ℕ (succ-ℕ x) (succ-ℕ y) H =
  ( left-successor-law-add-ℕ x (dist-ℕ x y)) ∙
  ( ap succ-ℕ (is-additive-right-inverse-dist-ℕ x y H))

triangle-equality-dist-ℕ :
  (x y z : ℕ) → (x ≤-ℕ y) → (y ≤-ℕ z) →
  Id (add-ℕ (dist-ℕ x y) (dist-ℕ y z)) (dist-ℕ x z)
triangle-equality-dist-ℕ zero-ℕ zero-ℕ zero-ℕ H1 H2 = refl
triangle-equality-dist-ℕ zero-ℕ zero-ℕ (succ-ℕ z) star star =
  ap succ-ℕ (left-unit-law-add-ℕ z)
triangle-equality-dist-ℕ zero-ℕ (succ-ℕ y) (succ-ℕ z) star H2 =
  left-successor-law-add-ℕ y (dist-ℕ y z) ∙
  ap succ-ℕ (is-additive-right-inverse-dist-ℕ y z H2)
triangle-equality-dist-ℕ (succ-ℕ x) (succ-ℕ y) (succ-ℕ z) H1 H2 =
  triangle-equality-dist-ℕ x y z H1 H2

symmetric-dist-ℕ :
  (m n : ℕ) → Id (dist-ℕ m n) (dist-ℕ n m)
symmetric-dist-ℕ zero-ℕ zero-ℕ = refl
symmetric-dist-ℕ zero-ℕ (succ-ℕ n) = refl
symmetric-dist-ℕ (succ-ℕ m) zero-ℕ = refl
symmetric-dist-ℕ (succ-ℕ m) (succ-ℕ n) = symmetric-dist-ℕ m n

is-total-dist-ℕ :
  (x y z : ℕ) → cases-dist-ℕ x y z
is-total-dist-ℕ x y z with order-three-elements-ℕ x y z
is-total-dist-ℕ x y z | inl (inl (pair H1 H2)) =
  inl (triangle-equality-dist-ℕ x y z H1 H2)
is-total-dist-ℕ x y z | inl (inr (pair H1 H2)) = 
  inr
    ( inl
      ( ( commutative-add-ℕ (dist-ℕ y z) (dist-ℕ x z)) ∙
        ( ( ap (add-ℕ (dist-ℕ x z)) (symmetric-dist-ℕ y z)) ∙
          ( triangle-equality-dist-ℕ x z y H1 H2))))
is-total-dist-ℕ x y z | inr (inl (inl (pair H1 H2))) =
  inr
    ( inl
      ( ( ap (add-ℕ (dist-ℕ y z)) (symmetric-dist-ℕ x z)) ∙
        ( ( triangle-equality-dist-ℕ y z x H1 H2) ∙
          ( symmetric-dist-ℕ y x))))
is-total-dist-ℕ x y z | inr (inl (inr (pair H1 H2))) =
  inr
    ( inr
      ( ( ap (add-ℕ (dist-ℕ x z)) (symmetric-dist-ℕ x y)) ∙
        ( ( commutative-add-ℕ (dist-ℕ x z) (dist-ℕ y x)) ∙
          ( triangle-equality-dist-ℕ y x z H1 H2)))) 
is-total-dist-ℕ x y z | inr (inr (inl (pair H1 H2))) =
  inr
    ( inr
      ( ( ap (add-ℕ' (dist-ℕ x y)) (symmetric-dist-ℕ x z)) ∙
        ( ( triangle-equality-dist-ℕ z x y H1 H2) ∙
          ( symmetric-dist-ℕ z y))))
is-total-dist-ℕ x y z | inr (inr (inr (pair H1 H2))) =
  inl
    ( ( ap-add-ℕ (symmetric-dist-ℕ x y) (symmetric-dist-ℕ y z)) ∙
      ( ( commutative-add-ℕ (dist-ℕ y x) (dist-ℕ z y)) ∙
        ( ( triangle-equality-dist-ℕ z y x H1 H2) ∙
          ( symmetric-dist-ℕ z x))))

concatenate-div-eq-ℕ :
  {x y z : ℕ} → div-ℕ x y → Id y z → div-ℕ x z
concatenate-div-eq-ℕ p refl = p

left-successor-law-mul-ℕ :
  (x y : ℕ) → Id (mul-ℕ (succ-ℕ x) y) (add-ℕ (mul-ℕ x y) y)
left-successor-law-mul-ℕ x y = refl

right-successor-law-mul-ℕ :
  (x y : ℕ) → Id (mul-ℕ x (succ-ℕ y)) (add-ℕ x (mul-ℕ x y))
right-successor-law-mul-ℕ zero-ℕ y = refl
right-successor-law-mul-ℕ (succ-ℕ x) y =
  ( ( ap (λ t → succ-ℕ (add-ℕ t y)) (right-successor-law-mul-ℕ x y)) ∙
    ( ap succ-ℕ (associative-add-ℕ x (mul-ℕ x y) y))) ∙
  ( inv (left-successor-law-add-ℕ x (add-ℕ (mul-ℕ x y) y)))

left-distributive-mul-add-ℕ :
  (x y z : ℕ) → Id (mul-ℕ x (add-ℕ y z)) (add-ℕ (mul-ℕ x y) (mul-ℕ x z))
left-distributive-mul-add-ℕ zero-ℕ y z = refl
left-distributive-mul-add-ℕ (succ-ℕ x) y z =
  ( left-successor-law-mul-ℕ x (add-ℕ y z)) ∙ 
  ( ( ap (add-ℕ' (add-ℕ y z)) (left-distributive-mul-add-ℕ x y z)) ∙ 
    ( ( associative-add-ℕ (mul-ℕ x y) (mul-ℕ x z) (add-ℕ y z)) ∙
      ( ( ap ( add-ℕ (mul-ℕ x y)) 
             ( ( inv (associative-add-ℕ (mul-ℕ x z) y z)) ∙
               ( ( ap (add-ℕ' z) (commutative-add-ℕ (mul-ℕ x z) y)) ∙
                 ( associative-add-ℕ y (mul-ℕ x z) z)))) ∙ 
        ( inv (associative-add-ℕ (mul-ℕ x y) y (add-ℕ (mul-ℕ x z) z))))))

commutative-mul-ℕ :
  (x y : ℕ) → Id (mul-ℕ x y) (mul-ℕ y x)
commutative-mul-ℕ zero-ℕ y = inv (right-zero-law-mul-ℕ y)
commutative-mul-ℕ (succ-ℕ x) y =
  ( commutative-add-ℕ (mul-ℕ x y) y) ∙ 
  ( ( ap (add-ℕ y) (commutative-mul-ℕ x y)) ∙
    ( inv (right-successor-law-mul-ℕ y x)))

right-distributive-mul-add-ℕ :
  (x y z : ℕ) → Id (mul-ℕ (add-ℕ x y) z) (add-ℕ (mul-ℕ x z) (mul-ℕ y z))
right-distributive-mul-add-ℕ x y z =
  ( commutative-mul-ℕ (add-ℕ x y) z) ∙ 
  ( ( left-distributive-mul-add-ℕ z x y) ∙ 
    ( ( ap (add-ℕ' (mul-ℕ z y)) (commutative-mul-ℕ z x)) ∙ 
      ( ap (add-ℕ (mul-ℕ x z)) (commutative-mul-ℕ z y))))

div-add-ℕ :
  (d x y : ℕ) → div-ℕ d x → div-ℕ d y → div-ℕ d (add-ℕ x y)
div-add-ℕ d x y (pair n p) (pair m q) =
  pair
    ( add-ℕ n m)
    ( ( right-distributive-mul-add-ℕ n m d) ∙
      ( ap-add-ℕ p q))

is-injective-add-ℕ' : (k : ℕ) → is-injective (add-ℕ' k)
is-injective-add-ℕ' zero-ℕ = id
is-injective-add-ℕ' (succ-ℕ k) p = is-injective-add-ℕ' k (is-injective-succ-ℕ p)

mul-ℕ' : ℕ → (ℕ → ℕ)
mul-ℕ' x y = mul-ℕ y x

leq-leq-add-ℕ :
  (m n x : ℕ) → (add-ℕ m x) ≤-ℕ (add-ℕ n x) → m ≤-ℕ n
leq-leq-add-ℕ m n zero-ℕ H = H
leq-leq-add-ℕ m n (succ-ℕ x) H = leq-leq-add-ℕ m n x H

concatenate-eq-leq-eq-ℕ :
  {x' x y y' : ℕ} → Id x' x → x ≤-ℕ y → Id y y' → x' ≤-ℕ y'
concatenate-eq-leq-eq-ℕ refl H refl = H

concatenate-eq-leq-ℕ :
  {m m' : ℕ} (n : ℕ) → Id m' m → m ≤-ℕ n → m' ≤-ℕ n
concatenate-eq-leq-ℕ n refl H = H

leq-leq-add-ℕ' :
  (m n x : ℕ) → (add-ℕ x m) ≤-ℕ (add-ℕ x n) → m ≤-ℕ n
leq-leq-add-ℕ' m n x H =
  leq-leq-add-ℕ m n x
    ( concatenate-eq-leq-eq-ℕ
      ( commutative-add-ℕ m x)
      ( H)
      ( commutative-add-ℕ x n))


leq-leq-mul-ℕ :
  (m n x : ℕ) → (mul-ℕ (succ-ℕ x) m) ≤-ℕ (mul-ℕ (succ-ℕ x) n) → m ≤-ℕ n
leq-leq-mul-ℕ zero-ℕ zero-ℕ x H = star
leq-leq-mul-ℕ zero-ℕ (succ-ℕ n) x H = star
leq-leq-mul-ℕ (succ-ℕ m) zero-ℕ x H =
  ex-falso
    ( concatenate-leq-eq-ℕ
      ( mul-ℕ (succ-ℕ x) (succ-ℕ m))
      ( H)
      ( right-zero-law-mul-ℕ (succ-ℕ x)))
leq-leq-mul-ℕ (succ-ℕ m) (succ-ℕ n) x H =
  leq-leq-mul-ℕ m n x
    ( leq-leq-add-ℕ' (mul-ℕ (succ-ℕ x) m) (mul-ℕ (succ-ℕ x) n) (succ-ℕ x)
      ( concatenate-eq-leq-eq-ℕ
        ( inv (right-successor-law-mul-ℕ (succ-ℕ x) m))
        ( H)
        ( right-successor-law-mul-ℕ (succ-ℕ x) n)))

leq-leq-mul-ℕ' :
  (m n x : ℕ) → (mul-ℕ m (succ-ℕ x)) ≤-ℕ (mul-ℕ n (succ-ℕ x)) → m ≤-ℕ n
leq-leq-mul-ℕ' m n x H =
  leq-leq-mul-ℕ m n x
    ( concatenate-eq-leq-eq-ℕ
      ( commutative-mul-ℕ (succ-ℕ x) m)
      ( H)
      ( commutative-mul-ℕ n (succ-ℕ x)))

div-left-summand-ℕ :
  (d x y : ℕ) → div-ℕ d y → div-ℕ d (add-ℕ x y) → div-ℕ d x
div-left-summand-ℕ zero-ℕ x y (pair m q) (pair n p) =
  pair zero-ℕ
    ( ( inv (right-zero-law-mul-ℕ n)) ∙
      ( p ∙ (ap (add-ℕ x) ((inv q) ∙ (right-zero-law-mul-ℕ m)))))
div-left-summand-ℕ (succ-ℕ d) x y (pair m q) (pair n p) =
  pair
    ( dist-ℕ m n)
    ( is-injective-add-ℕ' (mul-ℕ m (succ-ℕ d))
      ( ( inv
          ( ( right-distributive-mul-add-ℕ m (dist-ℕ m n) (succ-ℕ d)) ∙
            ( commutative-add-ℕ
              ( mul-ℕ m (succ-ℕ d))
              ( mul-ℕ (dist-ℕ m n) (succ-ℕ d))))) ∙ 
        ( ( ap
            ( mul-ℕ' (succ-ℕ d))
            ( is-additive-right-inverse-dist-ℕ m n
              ( leq-leq-mul-ℕ' m n d
                ( concatenate-eq-leq-eq-ℕ q
                  ( leq-add-ℕ' y x)
                  ( inv p))))) ∙
          ( p ∙ (ap (add-ℕ x) (inv q))))))

div-right-summand-ℕ :
  (d x y : ℕ) → div-ℕ d x → div-ℕ d (add-ℕ x y) → div-ℕ d y
div-right-summand-ℕ d x y H1 H2 =
  div-left-summand-ℕ d y x H1 (concatenate-div-eq-ℕ H2 (commutative-add-ℕ x y))

trans-cong-ℕ :
  (k x y z : ℕ) →
  cong-ℕ k x y → cong-ℕ k y z → cong-ℕ k x z
trans-cong-ℕ k x y z d e with is-total-dist-ℕ x y z
trans-cong-ℕ k x y z d e | inl α =
  concatenate-div-eq-ℕ (div-add-ℕ k (dist-ℕ x y) (dist-ℕ y z) d e) α
trans-cong-ℕ k x y z d e | inr (inl α) =
  div-right-summand-ℕ k (dist-ℕ y z) (dist-ℕ x z) e
    ( concatenate-div-eq-ℕ d (inv α))
trans-cong-ℕ k x y z d e | inr (inr α) =
  div-left-summand-ℕ k (dist-ℕ x z) (dist-ℕ x y) d
    ( concatenate-div-eq-ℕ e (inv α))

concatenate-cong-eq-cong-ℕ :
  {k x1 x2 x3 x4 : ℕ} →
  cong-ℕ k x1 x2 → Id x2 x3 → cong-ℕ k x3 x4 → cong-ℕ k x1 x4
concatenate-cong-eq-cong-ℕ {k} {x} {y} {.y} {z} H refl K =
  trans-cong-ℕ k x y z H K
  
concatenate-eq-cong-eq-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 x4 x5 x6 : ℕ} →
  Id x1 x2 → cong-ℕ k x2 x3 → Id x3 x4 →
  cong-ℕ k x4 x5 → Id x5 x6 → cong-ℕ k x1 x6
concatenate-eq-cong-eq-cong-eq-ℕ k {x} {.x} {y} {.y} {z} {.z} refl H refl K refl =
  trans-cong-ℕ k x y z H K

nat-skip-zero-Fin :
  {k : ℕ} (x : Fin k) → Id (nat-Fin (skip-zero-Fin x)) (succ-ℕ (nat-Fin x))
nat-skip-zero-Fin {succ-ℕ k} (inl x) = nat-skip-zero-Fin x
nat-skip-zero-Fin {succ-ℕ k} (inr star) = refl

nat-succ-Fin :
  {k : ℕ} (x : Fin k) → Id (nat-Fin (succ-Fin (inl x))) (succ-ℕ (nat-Fin x))
nat-succ-Fin {k} x = nat-skip-zero-Fin x

concatenate-eq-cong-ℕ :
  (k : ℕ) {x1 x2 x3 : ℕ} →
  Id x1 x2 → cong-ℕ k x2 x3 → cong-ℕ k x1 x3
concatenate-eq-cong-ℕ k refl H = H

symm-cong-ℕ :
  (k x y : ℕ) → cong-ℕ k x y → cong-ℕ k y x
symm-cong-ℕ k x y (pair d p) =
  pair d (p ∙ (symmetric-dist-ℕ x y))

right-unit-law-mul-ℕ :
  (x : ℕ) → Id (mul-ℕ x one-ℕ) x
right-unit-law-mul-ℕ zero-ℕ = refl
right-unit-law-mul-ℕ (succ-ℕ x) = ap succ-ℕ (right-unit-law-mul-ℕ x)

left-unit-law-mul-ℕ :
  (x : ℕ) → Id (mul-ℕ one-ℕ x) x
left-unit-law-mul-ℕ zero-ℕ = refl
left-unit-law-mul-ℕ (succ-ℕ x) = ap succ-ℕ (left-unit-law-mul-ℕ x)

left-unit-law-dist-ℕ :
  (n : ℕ) → Id (dist-ℕ zero-ℕ n) n
left-unit-law-dist-ℕ zero-ℕ = refl
left-unit-law-dist-ℕ (succ-ℕ n) = refl

right-unit-law-dist-ℕ :
  (n : ℕ) → Id (dist-ℕ n zero-ℕ) n
right-unit-law-dist-ℕ zero-ℕ = refl
right-unit-law-dist-ℕ (succ-ℕ n) = refl

cong-zero-ℕ :
  (k : ℕ) → cong-ℕ k k zero-ℕ
cong-zero-ℕ k =
  pair one-ℕ ((left-unit-law-mul-ℕ k) ∙ (inv (right-unit-law-dist-ℕ k)))

cong-zero-ℕ' :
  (k : ℕ) → cong-ℕ k zero-ℕ k
cong-zero-ℕ' k =
  symm-cong-ℕ k k zero-ℕ (cong-zero-ℕ k)

cong-nat-succ-Fin :
  (k : ℕ) (x : Fin k) → cong-ℕ k (nat-Fin (succ-Fin x)) (succ-ℕ (nat-Fin x))
cong-nat-succ-Fin (succ-ℕ k) (inl x) =
  cong-identification-ℕ
    ( succ-ℕ k)
    { nat-Fin (succ-Fin (inl x))}
    { succ-ℕ (nat-Fin x)}
    ( nat-succ-Fin x)
cong-nat-succ-Fin (succ-ℕ k) (inr star) =
  concatenate-eq-cong-ℕ
    ( succ-ℕ k)
    { nat-Fin {succ-ℕ k} zero-Fin}
    { zero-ℕ}
    { succ-ℕ k}
    ( is-zero-nat-zero-Fin {k})
    ( cong-zero-ℕ' (succ-ℕ k))

cong-nat-mod-succ-ℕ :
  (k x : ℕ) → cong-ℕ (succ-ℕ k) (nat-Fin (mod-succ-ℕ k x)) x
cong-nat-mod-succ-ℕ k zero-ℕ =
  cong-identification-ℕ (succ-ℕ k) (is-zero-nat-zero-Fin {k})
cong-nat-mod-succ-ℕ k (succ-ℕ x) =
  trans-cong-ℕ
    ( succ-ℕ k)
    ( nat-Fin (mod-succ-ℕ k (succ-ℕ x)))
    ( succ-ℕ (nat-Fin (mod-succ-ℕ k x)))
    ( succ-ℕ x)
    ( cong-nat-succ-Fin (succ-ℕ k) (mod-succ-ℕ k x) )
    ( cong-nat-mod-succ-ℕ k x)

issec-nat-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mod-succ-ℕ k (nat-Fin x)) x
issec-nat-Fin {k} x =
  is-injective-nat-Fin
    ( eq-cong-le-ℕ
      ( succ-ℕ k)
      ( nat-Fin (mod-succ-ℕ k (nat-Fin x)))
      ( nat-Fin x)
      ( strict-upper-bound-nat-Fin (mod-succ-ℕ k (nat-Fin x)))
      ( strict-upper-bound-nat-Fin x)
      ( cong-nat-mod-succ-ℕ k (nat-Fin x)))

mul-Fin :
  {k : ℕ} → Fin k → Fin k → Fin k
mul-Fin {succ-ℕ k} x y = mod-succ-ℕ k (mul-ℕ (nat-Fin x) (nat-Fin y))

one-Fin : {k : ℕ} → Fin (succ-ℕ k)
one-Fin {k} = mod-succ-ℕ k one-ℕ

div-Fin : {k : ℕ} → Fin k → Fin k → UU lzero
div-Fin {k} x y = Σ (Fin k) (λ u → Id (mul-Fin u x) y)

eq-cong-nat-Fin :
  (k : ℕ) (x y : Fin k) → cong-ℕ k (nat-Fin x) (nat-Fin y) → Id x y
eq-cong-nat-Fin (succ-ℕ k) x y H =
  is-injective-nat-Fin
    ( eq-cong-le-ℕ (succ-ℕ k) (nat-Fin x) (nat-Fin y)
      ( strict-upper-bound-nat-Fin x)
      ( strict-upper-bound-nat-Fin y)
      ( H))

eq-mod-succ-cong-ℕ :
  (k x y : ℕ) → cong-ℕ (succ-ℕ k) x y → Id (mod-succ-ℕ k x) (mod-succ-ℕ k y)
eq-mod-succ-cong-ℕ k x y H =
  eq-cong-nat-Fin
    ( succ-ℕ k)
    ( mod-succ-ℕ k x)
    ( mod-succ-ℕ k y)
    ( trans-cong-ℕ
      ( succ-ℕ k)
      ( nat-Fin (mod-succ-ℕ k x))
      ( x)
      ( nat-Fin (mod-succ-ℕ k y))
      ( cong-nat-mod-succ-ℕ k x)
      ( trans-cong-ℕ (succ-ℕ k) x y (nat-Fin (mod-succ-ℕ k y)) H
        ( symm-cong-ℕ (succ-ℕ k) (nat-Fin (mod-succ-ℕ k y)) y
          ( cong-nat-mod-succ-ℕ k y))))

is-one-nat-one-Fin :
  (k : ℕ) → is-one-ℕ (nat-Fin (one-Fin {succ-ℕ k}))
is-one-nat-one-Fin zero-ℕ = refl
is-one-nat-one-Fin (succ-ℕ k) = is-one-nat-one-Fin k

left-unit-law-mul-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mul-Fin one-Fin x) x
left-unit-law-mul-Fin {zero-ℕ} (inr star) = refl
left-unit-law-mul-Fin {succ-ℕ k} x =
  ( eq-mod-succ-cong-ℕ (succ-ℕ k)
    ( mul-ℕ (nat-Fin (one-Fin {succ-ℕ k})) (nat-Fin x))
    ( nat-Fin x)
    ( cong-identification-ℕ
      ( succ-ℕ (succ-ℕ k))
      ( ( ap ( mul-ℕ' (nat-Fin x))
             ( is-one-nat-one-Fin k)) ∙
        ( left-unit-law-mul-ℕ (nat-Fin x))))) ∙
  ( issec-nat-Fin x)

commutative-mul-Fin :
  {k : ℕ} (x y : Fin k) → Id (mul-Fin x y) (mul-Fin y x)
commutative-mul-Fin {succ-ℕ k} x y =
  eq-mod-succ-cong-ℕ k
    ( mul-ℕ (nat-Fin x) (nat-Fin y))
    ( mul-ℕ (nat-Fin y) (nat-Fin x))
    ( cong-identification-ℕ
      ( succ-ℕ k)
      ( commutative-mul-ℕ (nat-Fin x) (nat-Fin y)))

right-unit-law-mul-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mul-Fin x one-Fin) x
right-unit-law-mul-Fin x =
  ( commutative-mul-Fin x one-Fin) ∙
  ( left-unit-law-mul-Fin x)

refl-div-Fin : {k : ℕ} (x : Fin k) → div-Fin x x
refl-div-Fin {succ-ℕ k} x = pair one-Fin (left-unit-law-mul-Fin x)

associative-mul-ℕ :
  (x y z : ℕ) → Id (mul-ℕ (mul-ℕ x y) z) (mul-ℕ x (mul-ℕ y z))
associative-mul-ℕ zero-ℕ y z = refl
associative-mul-ℕ (succ-ℕ x) y z =
  ( right-distributive-mul-add-ℕ (mul-ℕ x y) y z) ∙ 
  ( ap (add-ℕ' (mul-ℕ y z)) (associative-mul-ℕ x y z))

dist-ℕ' : ℕ → ℕ → ℕ
dist-ℕ' m n = dist-ℕ n m

ap-dist-ℕ :
  {m n m' n' : ℕ} → Id m m' → Id n n' → Id (dist-ℕ m n) (dist-ℕ m' n')
ap-dist-ℕ p q = ap-binary dist-ℕ p q

translation-invariant-dist-ℕ :
  (k m n : ℕ) → Id (dist-ℕ (add-ℕ k m) (add-ℕ k n)) (dist-ℕ m n)
translation-invariant-dist-ℕ zero-ℕ m n =
  ap-dist-ℕ (left-unit-law-add-ℕ m) (left-unit-law-add-ℕ n)
translation-invariant-dist-ℕ (succ-ℕ k)  m n =
  ( ap-dist-ℕ (left-successor-law-add-ℕ k m) (left-successor-law-add-ℕ k n)) ∙
  ( translation-invariant-dist-ℕ k m n)

translation-invariant-dist-ℕ' :
  (k m n : ℕ) → Id (dist-ℕ (add-ℕ m k) (add-ℕ n k)) (dist-ℕ m n)
translation-invariant-dist-ℕ' k m n =
  ( ap-dist-ℕ (commutative-add-ℕ m k) (commutative-add-ℕ n k)) ∙
  ( translation-invariant-dist-ℕ k m n)

left-distributive-mul-dist-ℕ :
  (m n k : ℕ) → Id (mul-ℕ k (dist-ℕ m n)) (dist-ℕ (mul-ℕ k m) (mul-ℕ k n))
left-distributive-mul-dist-ℕ zero-ℕ zero-ℕ zero-ℕ = refl
left-distributive-mul-dist-ℕ zero-ℕ zero-ℕ (succ-ℕ k) = left-distributive-mul-dist-ℕ zero-ℕ zero-ℕ k
left-distributive-mul-dist-ℕ zero-ℕ (succ-ℕ n) zero-ℕ = refl
left-distributive-mul-dist-ℕ zero-ℕ (succ-ℕ n) (succ-ℕ k) =
  ap ( dist-ℕ' (mul-ℕ (succ-ℕ k) (succ-ℕ n)))
     ( inv (right-zero-law-mul-ℕ (succ-ℕ k)))
left-distributive-mul-dist-ℕ (succ-ℕ m) zero-ℕ zero-ℕ = refl
left-distributive-mul-dist-ℕ (succ-ℕ m) zero-ℕ (succ-ℕ k) =
  ap ( dist-ℕ (mul-ℕ (succ-ℕ k) (succ-ℕ m)))
     ( inv (right-zero-law-mul-ℕ (succ-ℕ k)))
left-distributive-mul-dist-ℕ (succ-ℕ m) (succ-ℕ n) zero-ℕ = refl
left-distributive-mul-dist-ℕ (succ-ℕ m) (succ-ℕ n) (succ-ℕ k) =
  inv
    ( ( ap-dist-ℕ
        ( right-successor-law-mul-ℕ (succ-ℕ k) m)
        ( right-successor-law-mul-ℕ (succ-ℕ k) n)) ∙
      ( ( translation-invariant-dist-ℕ
          ( succ-ℕ k)
          ( mul-ℕ (succ-ℕ k) m)
          ( mul-ℕ (succ-ℕ k) n)) ∙
        ( inv (left-distributive-mul-dist-ℕ m n (succ-ℕ k)))))

scalar-invariant-cong-ℕ :
  (k x y z : ℕ) → cong-ℕ k x y →  cong-ℕ k (mul-ℕ z x) (mul-ℕ z y)
scalar-invariant-cong-ℕ k x y z (pair d p) =
  pair
    ( mul-ℕ z d)
    ( ( associative-mul-ℕ z d k) ∙
      ( ( ap (mul-ℕ z) p) ∙
        ( left-distributive-mul-dist-ℕ x y z)))

concatenate-eq-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 x4 : ℕ} →
  Id x1 x2 → cong-ℕ k x2 x3 → Id x3 x4 → cong-ℕ k x1 x4
concatenate-eq-cong-eq-ℕ k refl H refl = H

scalar-invariant-cong-ℕ' :
  (k x y z : ℕ) → cong-ℕ k x y → cong-ℕ k (mul-ℕ x z) (mul-ℕ y z)
scalar-invariant-cong-ℕ' k x y z H =
  concatenate-eq-cong-eq-ℕ k
    ( commutative-mul-ℕ x z)
    ( scalar-invariant-cong-ℕ k x y z H)
    ( commutative-mul-ℕ z y)

congruence-mul-ℕ :
  (k : ℕ) {x y x' y' : ℕ} →
  cong-ℕ  k x x' → cong-ℕ k y y' → cong-ℕ k (mul-ℕ x y) (mul-ℕ x' y')
congruence-mul-ℕ k {x} {y} {x'} {y'} H K =
  trans-cong-ℕ k (mul-ℕ x y) (mul-ℕ x y') (mul-ℕ x' y')
    ( scalar-invariant-cong-ℕ k y y' x K)
    ( scalar-invariant-cong-ℕ' k x x' y' H)

cong-mul-Fin :
  {k : ℕ} (x y : Fin k) →
  cong-ℕ k (nat-Fin (mul-Fin x y)) (mul-ℕ (nat-Fin x) (nat-Fin y))
cong-mul-Fin {succ-ℕ k} x y =
  cong-nat-mod-succ-ℕ k (mul-ℕ (nat-Fin x) (nat-Fin y))

associative-mul-Fin :
  {k : ℕ} (x y z : Fin k) →
  Id (mul-Fin (mul-Fin x y) z) (mul-Fin x (mul-Fin y z))
associative-mul-Fin {succ-ℕ k} x y z =
  eq-mod-succ-cong-ℕ k
    ( mul-ℕ (nat-Fin (mul-Fin x y)) (nat-Fin z))
    ( mul-ℕ (nat-Fin x) (nat-Fin (mul-Fin y z)))
    ( concatenate-cong-eq-cong-ℕ
      { x1 = mul-ℕ (nat-Fin (mul-Fin x y)) (nat-Fin z)}
      { x2 = mul-ℕ (mul-ℕ (nat-Fin x) (nat-Fin y)) (nat-Fin z)}
      { x3 = mul-ℕ (nat-Fin x) (mul-ℕ (nat-Fin y) (nat-Fin z))}
      { x4 = mul-ℕ (nat-Fin x) (nat-Fin (mul-Fin y z))}
      ( congruence-mul-ℕ
        ( succ-ℕ k)
        { x = nat-Fin (mul-Fin x y)}
        { y = nat-Fin z}
        ( cong-mul-Fin x y)
        ( refl-cong-ℕ (succ-ℕ k) (nat-Fin z)))
      ( associative-mul-ℕ (nat-Fin x) (nat-Fin y) (nat-Fin z))
      ( symm-cong-ℕ
        ( succ-ℕ k)
        ( mul-ℕ (nat-Fin x) (nat-Fin (mul-Fin y z)))
        ( mul-ℕ (nat-Fin x) (mul-ℕ (nat-Fin y) (nat-Fin z)))
        ( congruence-mul-ℕ
          ( succ-ℕ k)
          { x = nat-Fin x}
          { y = nat-Fin (mul-Fin y z)}
          ( refl-cong-ℕ (succ-ℕ k) (nat-Fin x))
          ( cong-mul-Fin y z))))

trans-div-Fin :
  {k : ℕ} (x y z : Fin k) → div-Fin x y → div-Fin y z → div-Fin x z
trans-div-Fin x y z (pair u p) (pair v q) =
  pair (mul-Fin v u) (associative-mul-Fin v u x ∙ (ap (mul-Fin v) p ∙ q))

left-zero-law-mul-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mul-Fin zero-Fin x) zero-Fin
left-zero-law-mul-Fin {k} x =
  ( eq-mod-succ-cong-ℕ k
    ( mul-ℕ (nat-Fin (zero-Fin {k})) (nat-Fin x))
    ( nat-Fin (zero-Fin {k}))
    ( cong-identification-ℕ
      ( succ-ℕ k)
      { mul-ℕ (nat-Fin (zero-Fin {k})) (nat-Fin x)}
      { nat-Fin (zero-Fin {k})}
      ( ap (mul-ℕ' (nat-Fin x)) (is-zero-nat-zero-Fin {k}) ∙ inv (is-zero-nat-zero-Fin {k})))) ∙
  ( issec-nat-Fin (zero-Fin {k}))

div-zero-Fin : {k : ℕ} (x : Fin (succ-ℕ k)) → div-Fin x zero-Fin
div-zero-Fin x = pair zero-Fin (left-zero-law-mul-Fin x)

div-one-Fin : {k : ℕ} (x : Fin (succ-ℕ k)) → div-Fin one-Fin x
div-one-Fin x = pair x (right-unit-law-mul-Fin x)

right-zero-law-mul-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mul-Fin x zero-Fin) zero-Fin
right-zero-law-mul-Fin x =
  ( commutative-mul-Fin x zero-Fin) ∙
  ( left-zero-law-mul-Fin x)

is-zero-div-zero-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → div-Fin zero-Fin x → is-zero-Fin x
is-zero-div-zero-Fin {k} x (pair u p) = inv p ∙ right-zero-law-mul-Fin u

is-unit-Fin : {k : ℕ} → Fin k → UU lzero
is-unit-Fin {succ-ℕ k} x = div-Fin x one-Fin

unit-Fin : ℕ → UU lzero
unit-Fin k = Σ (Fin k) is-unit-Fin

is-unit-one-Fin : {k : ℕ} → is-unit-Fin (one-Fin {k})
is-unit-one-Fin {k} = refl-div-Fin one-Fin

one-unit-Fin : {k : ℕ} → unit-Fin (succ-ℕ k)
one-unit-Fin {k} = pair one-Fin is-unit-one-Fin

square-ℕ : ℕ → ℕ
square-ℕ x = mul-ℕ x x

square-succ-ℕ :
  (k : ℕ) →
  Id (square-ℕ (succ-ℕ k)) (succ-ℕ (mul-ℕ (succ-ℕ (succ-ℕ k)) k))
square-succ-ℕ k =
  ( right-successor-law-mul-ℕ (succ-ℕ k) k) ∙
  ( commutative-add-ℕ (succ-ℕ k) (mul-ℕ (succ-ℕ k) k))

is-unit-neg-one-Fin : {k : ℕ} → is-unit-Fin (neg-one-Fin {k})
is-unit-neg-one-Fin {zero-ℕ} = refl-div-Fin neg-one-Fin
is-unit-neg-one-Fin {succ-ℕ k} =
  pair
    ( neg-one-Fin)
    ( eq-mod-succ-cong-ℕ
      ( succ-ℕ k)
      ( mul-ℕ (succ-ℕ k) (succ-ℕ k))
      ( one-ℕ)
      ( concatenate-eq-cong-ℕ
        ( succ-ℕ (succ-ℕ k))
        { x3 = one-ℕ}
        ( square-succ-ℕ k)
        ( pair k
          ( ( commutative-mul-ℕ k (succ-ℕ (succ-ℕ k))) ∙
            ( inv (right-unit-law-dist-ℕ (mul-ℕ (succ-ℕ (succ-ℕ k)) k)))))))

neg-one-unit-Fin : {k : ℕ} → unit-Fin (succ-ℕ k)
neg-one-unit-Fin = pair neg-one-Fin is-unit-neg-one-Fin

mul-Fin' :
  {k : ℕ} → Fin k → Fin k → Fin k
mul-Fin' {k} x y = mul-Fin y x

is-unit-mul-Fin :
  {k : ℕ} {x y : Fin k} →
  is-unit-Fin x → is-unit-Fin y → is-unit-Fin (mul-Fin x y)
is-unit-mul-Fin {succ-ℕ k} {x} {y} (pair d p) (pair e q) =
  pair
    ( mul-Fin e d)
    ( ( associative-mul-Fin e d (mul-Fin x y)) ∙
      ( ( ap
          ( mul-Fin e)
          ( ( inv (associative-mul-Fin d x y)) ∙
            ( ap (mul-Fin' y) p ∙ left-unit-law-mul-Fin y))) ∙
        ( q)))

mul-unit-Fin : {k : ℕ} → unit-Fin k → unit-Fin k → unit-Fin k
mul-unit-Fin u v =
  pair (mul-Fin (pr1 u) (pr1 v)) (is-unit-mul-Fin (pr2 u) (pr2 v))

inv-unit-Fin : {k : ℕ} → unit-Fin k → unit-Fin k
inv-unit-Fin {succ-ℕ k} (pair u (pair v p)) =
  pair v (pair u (commutative-mul-Fin u v ∙ p))

sim-unit-Fin :
  {k : ℕ} → Fin k → Fin k → UU lzero
sim-unit-Fin {k} x y = Σ (unit-Fin k) (λ u → Id (mul-Fin (pr1 u) x) y)

refl-sim-unit-Fin :
  {k : ℕ} (x : Fin k) → sim-unit-Fin x x
refl-sim-unit-Fin {succ-ℕ k} x = pair one-unit-Fin (left-unit-law-mul-Fin x)

symm-sim-unit-Fin :
  {k : ℕ} (x y : Fin k) → sim-unit-Fin x y → sim-unit-Fin y x
symm-sim-unit-Fin {succ-ℕ k} x y (pair (pair u (pair v q)) p) =
  pair
    ( inv-unit-Fin (pair u (pair v q)))
    ( ( ( ( ap (mul-Fin v) (inv p)) ∙
          ( inv (associative-mul-Fin v u x))) ∙
        ( ap (mul-Fin' x) q)) ∙
      ( left-unit-law-mul-Fin x))

trans-sim-unit-Fin :
  {k : ℕ} (x y z : Fin k) → sim-unit-Fin x y → sim-unit-Fin y z →
  sim-unit-Fin x z
trans-sim-unit-Fin {succ-ℕ k} x y z (pair u p) (pair v q) =
  pair
    ( mul-unit-Fin v u)
    ( associative-mul-Fin (pr1 v) (pr1 u) x ∙ (ap (mul-Fin (pr1 v)) p ∙ q))

is-mod-unit-ℕ : (k x : ℕ) → UU lzero
is-mod-unit-ℕ k x = Σ ℕ (λ l → cong-ℕ k (mul-ℕ l x) one-ℕ)

cong-eq-mod-succ-ℕ :
  (k x y : ℕ) → Id (mod-succ-ℕ k x) (mod-succ-ℕ k y) → cong-ℕ (succ-ℕ k) x y
cong-eq-mod-succ-ℕ k x y p =
  concatenate-cong-eq-cong-ℕ {succ-ℕ k} {x}
    ( symm-cong-ℕ (succ-ℕ k) (nat-Fin (mod-succ-ℕ k x)) x
      ( cong-nat-mod-succ-ℕ k x))
    ( ap nat-Fin p)
    ( cong-nat-mod-succ-ℕ k y)

is-mod-unit-sim-unit-mod-succ-ℕ :
  (k x : ℕ) → sim-unit-Fin (mod-succ-ℕ k x) one-Fin → is-mod-unit-ℕ (succ-ℕ k) x
is-mod-unit-sim-unit-mod-succ-ℕ k x (pair u p) =
  pair
    ( nat-Fin (pr1 u))
    ( cong-eq-mod-succ-ℕ k
      ( mul-ℕ (nat-Fin (pr1 u)) x)
      ( one-ℕ)
      ( ( eq-mod-succ-cong-ℕ k
          ( mul-ℕ (nat-Fin (pr1 u)) x)
          ( mul-ℕ (nat-Fin (pr1 u)) (nat-Fin (mod-succ-ℕ k x)))
          ( scalar-invariant-cong-ℕ
            ( succ-ℕ k)
            ( x)
            ( nat-Fin (mod-succ-ℕ k x))
            ( nat-Fin (pr1 u))
            ( symm-cong-ℕ
              ( succ-ℕ k)
              ( nat-Fin (mod-succ-ℕ k x))
              ( x)
              ( cong-nat-mod-succ-ℕ k x)))) ∙
        ( p)))

is-decidable-Σ-Fin :
  {l : Level} {k : ℕ} {P : Fin k → UU l} →
  ((x : Fin k) → is-decidable (P x)) → is-decidable (Σ (Fin k) P)
is-decidable-Σ-Fin {l} {zero-ℕ} {P} d = inr pr1
is-decidable-Σ-Fin {l} {succ-ℕ k} {P} d with d (inr star)
... | inl p = inl (pair (inr star) p)
... | inr f =
  is-decidable-iff
    ( λ t → pair (inl (pr1 t)) (pr2 t))
    ( g)
    ( is-decidable-Σ-Fin {l} {k} {P ∘ inl} (λ x → d (inl x)))
  where
  g : Σ (Fin (succ-ℕ k)) P → Σ (Fin k) (P ∘ inl)
  g (pair (inl x) p) = pair x p
  g (pair (inr star) p) = ex-falso (f p)

--------------------------------------------------------------------------------

-- Equivalences

_~_ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f g : (x : A) → B x) → UU (l1 ⊔ l2)
f ~ g = (x : _) → Id (f x) (g x)

refl-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f : (x : A) → B x} → f ~ f
refl-htpy x = refl

inv-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x} →
  (f ~ g) → (g ~ f)
inv-htpy H x = inv (H x)

_∙h_ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x} →
  (f ~ g) → (g ~ h) → (f ~ h)
_∙h_ H K x = (H x) ∙ (K x)

concat-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x} →
  (f ~ g) → (h : (x : A) → B x) → (g ~ h) → (f ~ h)
concat-htpy H h K x = concat (H x) (h x) (K x)

square :
  {l1 : Level} {A : UU l1} {x y1 y2 z : A}
  (p-left : Id x y1) (p-bottom : Id y1 z)
  (p-top : Id x y2) (p-right : Id y2 z) → UU l1
square p-left p-bottom p-top p-right = Id (p-left ∙ p-bottom) (p-top ∙ p-right)

htpy-left-whisk :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k}
  (h : B → C) {f g : A → B} → (f ~ g) → ((h ∘ f) ~ (h ∘ g))
htpy-left-whisk h H x = ap h (H x)

_·l_ = htpy-left-whisk

htpy-right-whisk :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k}
  {g h : B → C} (H : g ~ h) (f : A → B) → ((g ∘ f) ~ (h ∘ f))
htpy-right-whisk H f x = H (f x)

_·r_ = htpy-right-whisk

sq-left-whisk :
  {i : Level} {A : UU i} {x y1 y2 z : A} {p1 p1' : Id x y1}
  (s : Id p1 p1') {q1 : Id y1 z} {p2 : Id x y2} {q2 : Id y2 z} →
  square p1 q1 p2 q2 → square p1' q1 p2 q2
sq-left-whisk refl sq = sq

sq-top-whisk :
  {i : Level} {A : UU i} {x y1 y2 z : A}
  (p1 : Id x y1) (q1 : Id y1 z)
  (p2 : Id x y2) {p2' : Id x y2} (s : Id p2 p2') (q2 : Id y2 z) →
  square p1 q1 p2 q2 → square p1 q1 p2' q2
sq-top-whisk p1 q1 p2 refl q2 sq = sq

left-unit-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  {H : f ~ g} → (refl-htpy ∙h H) ~ H
left-unit-htpy x = left-unit

right-unit-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  {H : f ~ g} → (H ∙h refl-htpy) ~ H
right-unit-htpy x = right-unit

sec :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
sec {i} {j} {A} {B} f = Σ (B → A) (λ g → (f ∘ g) ~ id)

retr :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
retr {i} {j} {A} {B} f = Σ (B → A) (λ g → (g ∘ f) ~ id)

_retract-of_ :
  {i j : Level} → UU i → UU j → UU (i ⊔ j)
A retract-of B = Σ (A → B) retr

is-equiv :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
is-equiv f = sec f × retr f

_≃_ :
  {i j : Level} (A : UU i) (B : UU j) → UU (i ⊔ j)
A ≃ B = Σ (A → B) (λ f → is-equiv f)

map-equiv :
  {i j : Level} {A : UU i} {B : UU j} → (A ≃ B) → (A → B)
map-equiv e = pr1 e

is-equiv-map-equiv :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) → is-equiv (map-equiv e)
is-equiv-map-equiv e = pr2 e

is-equiv-id :
  {i : Level} {A : UU i} → is-equiv (id {i} {A})
is-equiv-id = pair (pair id refl-htpy) (pair id refl-htpy)

equiv-id :
  {i : Level} {A : UU i} → A ≃ A
equiv-id = pair id is-equiv-id

has-inverse :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
has-inverse {i} {j} {A} {B} f =
  Σ (B → A) (λ g → ((f ∘ g) ~ id) × ((g ∘ f) ~ id))

is-equiv-has-inverse' :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  has-inverse f → is-equiv f
is-equiv-has-inverse' (pair g (pair H K)) = pair (pair g H) (pair g K)

is-equiv-has-inverse :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (g : B → A) (H : (f ∘ g) ~ id) (K : (g ∘ f) ~ id) → is-equiv f
is-equiv-has-inverse g H K =
  is-equiv-has-inverse' (pair g (pair H K))

htpy-section-retraction :
  { i j : Level} {A : UU i} {B : UU j} {f : A → B}
  ( is-equiv-f : is-equiv f) →
  ( (pr1 (pr1 is-equiv-f))) ~ (pr1 (pr2 is-equiv-f))
htpy-section-retraction {i} {j} {A} {B} {f} (pair (pair g G) (pair h H)) =
    (inv-htpy (H ·r g)) ∙h (h ·l G)

has-inverse-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-equiv f → has-inverse f
has-inverse-is-equiv {i} {j} {A} {B} {f} (pair (pair g G) (pair h H)) =
  let is-equiv-f = pair (pair g G) (pair h H) in
  pair g (pair G (((htpy-section-retraction is-equiv-f) ·r f) ∙h H))

map-inv-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} → is-equiv f → B → A
map-inv-is-equiv is-equiv-f = pr1 (has-inverse-is-equiv is-equiv-f)

issec-map-inv-is-equiv' :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (is-equiv-f : is-equiv f) → (f ∘ (map-inv-is-equiv is-equiv-f)) ~ id
issec-map-inv-is-equiv' is-equiv-f = pr1 (pr2 (has-inverse-is-equiv is-equiv-f))

isretr-map-inv-is-equiv' :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (is-equiv-f : is-equiv f) → ((map-inv-is-equiv is-equiv-f) ∘ f) ~ id
isretr-map-inv-is-equiv' is-equiv-f =
  pr2 (pr2 (has-inverse-is-equiv is-equiv-f))

is-equiv-map-inv-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (is-equiv-f : is-equiv f) → is-equiv (map-inv-is-equiv is-equiv-f)
is-equiv-map-inv-is-equiv {i} {j} {A} {B} {f} is-equiv-f =
  is-equiv-has-inverse f
    ( isretr-map-inv-is-equiv' is-equiv-f)
    ( issec-map-inv-is-equiv' is-equiv-f)

map-inv-equiv' :
  {i j : Level} {A : UU i} {B : UU j} → (A ≃ B) → (B → A)
map-inv-equiv' e = map-inv-is-equiv (is-equiv-map-equiv e)

issec-map-inv-equiv' :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) →
  ((map-equiv e) ∘ (map-inv-equiv' e)) ~ id
issec-map-inv-equiv' e = issec-map-inv-is-equiv' (is-equiv-map-equiv e)

isretr-map-inv-equiv' :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) →
  ((map-inv-equiv' e) ∘ (map-equiv e)) ~ id
isretr-map-inv-equiv' e = isretr-map-inv-is-equiv' (is-equiv-map-equiv e)

is-equiv-map-inv-equiv :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) → is-equiv (map-inv-equiv' e)
is-equiv-map-inv-equiv e =
  is-equiv-map-inv-is-equiv (is-equiv-map-equiv e)

inv-equiv :
  {i j : Level} {A : UU i} {B : UU j} → (A ≃ B) → (B ≃ A)
inv-equiv e = pair (map-inv-equiv' e) (is-equiv-map-inv-equiv e)

triangle-section :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) (S : sec h) →
  g ~ (f ∘ (pr1 S))
triangle-section f g h H (pair s issec) =
  inv-htpy (( H ·r s) ∙h (g ·l issec))

section-comp :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  sec h → sec f → sec g
section-comp f g h H sec-h sec-f =
  pair (h ∘ (pr1 sec-f)) ((inv-htpy (H ·r (pr1 sec-f))) ∙h (pr2 sec-f))

section-comp' :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  sec h → sec g → sec f
section-comp' f g h H sec-h sec-g =
  pair
    ( (pr1 sec-h) ∘ (pr1 sec-g))
    ( ( H ·r ((pr1 sec-h) ∘ (pr1 sec-g))) ∙h
      ( ( g ·l ((pr2 sec-h) ·r (pr1 sec-g))) ∙h ((pr2 sec-g))))

triangle-retraction :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) (R : retr g) →
  h ~ ((pr1 R) ∘ f)
triangle-retraction f g h H (pair r isretr) =
  inv-htpy (( r ·l H) ∙h (isretr ·r h))

retraction-comp :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  retr g → retr f → retr h
retraction-comp f g h H retr-g retr-f =
  pair
    ( (pr1 retr-f) ∘ g)
    ( (inv-htpy ((pr1 retr-f) ·l H)) ∙h (pr2 retr-f))

retraction-comp' :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  retr g → retr h → retr f
retraction-comp' f g h H retr-g retr-h =
  pair
    ( (pr1 retr-h) ∘ (pr1 retr-g))
    ( ( ((pr1 retr-h) ∘ (pr1 retr-g)) ·l H) ∙h
      ( ((pr1 retr-h) ·l ((pr2 retr-g) ·r h)) ∙h (pr2 retr-h)))

is-equiv-comp :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  is-equiv h → is-equiv g → is-equiv f
is-equiv-comp f g h H (pair sec-h retr-h) (pair sec-g retr-g) =
  pair
    ( section-comp' f g h H sec-h sec-g)
    ( retraction-comp' f g h H retr-g retr-h)

is-equiv-comp' :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k} (g : B → X) (h : A → B) →
  is-equiv h → is-equiv g → is-equiv (g ∘ h)
is-equiv-comp' g h = is-equiv-comp (g ∘ h) g h refl-htpy

equiv-comp :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k} →
  (B ≃ X) → (A ≃ B) → (A ≃ X)
equiv-comp g h =
  pair ((pr1 g) ∘ (pr1 h)) (is-equiv-comp' (pr1 g) (pr1 h) (pr2 h) (pr2 g))

_∘e_ :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k} →
  (B ≃ X) → (A ≃ B) → (A ≃ X)
_∘e_ = equiv-comp

is-equiv-left-factor :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  is-equiv f → is-equiv h → is-equiv g
is-equiv-left-factor f g h H
  ( pair sec-f retr-f)
  ( pair (pair sh sh-issec) retr-h) =
  pair
    ( section-comp f g h H (pair sh sh-issec) sec-f)
    ( retraction-comp' g f sh
      ( triangle-section f g h H (pair sh sh-issec))
      ( retr-f)
      ( pair h sh-issec))

is-equiv-left-factor' :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k} (g : B → X) (h : A → B) →
  is-equiv (g ∘ h) → is-equiv h → is-equiv g
is-equiv-left-factor' g h =
  is-equiv-left-factor (g ∘ h) g h refl-htpy

is-equiv-right-factor :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  is-equiv g → is-equiv f → is-equiv h
is-equiv-right-factor f g h H
  ( pair sec-g (pair rg rg-isretr))
  ( pair sec-f retr-f) =
  pair
    ( section-comp' h rg f
      ( triangle-retraction f g h H (pair rg rg-isretr))
      ( sec-f)
      ( pair g rg-isretr))
    ( retraction-comp f g h H (pair rg rg-isretr) retr-f)

is-equiv-right-factor' :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k} (g : B → X) (h : A → B) → 
  is-equiv g → is-equiv (g ∘ h) → is-equiv h
is-equiv-right-factor' g h =
  is-equiv-right-factor (g ∘ h) g h refl-htpy

is-equiv-is-section-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} {g : B → A} →
  is-equiv f → (f ∘ g) ~ id → is-equiv g
is-equiv-is-section-is-equiv {B = B} {f = f} {g = g} is-equiv-f H =
  is-equiv-right-factor id f g (inv-htpy H) is-equiv-f is-equiv-id

is-equiv-is-retraction-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} {g : B → A} →
  is-equiv f  → (g ∘ f) ~ id → is-equiv g
is-equiv-is-retraction-is-equiv {A = A} {f = f} {g = g} is-equiv-f H =
  is-equiv-left-factor id g f (inv-htpy H) is-equiv-id is-equiv-f

inv-inv :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) → Id (inv (inv p)) p
inv-inv refl = refl

is-equiv-inv :
  {i : Level} {A : UU i} (x y : A) →
  is-equiv (λ (p : Id x y) → inv p)
is-equiv-inv x y =
  is-equiv-has-inverse inv inv-inv inv-inv

equiv-inv :
  {i : Level} {A : UU i} (x y : A) → (Id x y) ≃ (Id y x)
equiv-inv x y = pair inv (is-equiv-inv x y)

inv-tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A} →
  Id x y → B y → B x
inv-tr B p = tr B (inv p)

isretr-inv-tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A}
  (p : Id x y) → ((inv-tr B p ) ∘ (tr B p)) ~ id
isretr-inv-tr B refl b = refl

issec-inv-tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A}
  (p : Id x y) → ((tr B p) ∘ (inv-tr B p)) ~ id
issec-inv-tr B refl b = refl

is-equiv-tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A}
  (p : Id x y) → is-equiv (tr B p)
is-equiv-tr B p =
  is-equiv-has-inverse
    ( inv-tr B p)
    ( issec-inv-tr B p)
    ( isretr-inv-tr B p)

equiv-tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A}
  (p : Id x y) → (B x) ≃ (B y)
equiv-tr B p = pair (tr B p) (is-equiv-tr B p)

Eq-Σ :
  {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) → UU (i ⊔ j)
Eq-Σ {B = B} s t = Σ (Id (pr1 s) (pr1 t)) (λ α → Id (tr B α (pr2 s)) (pr2 t))

reflexive-Eq-Σ :
  {i j : Level} {A : UU i} {B : A → UU j} (s : Σ A B) → Eq-Σ s s
reflexive-Eq-Σ (pair a b) = pair refl refl

pair-eq-Σ :
  {i j : Level} {A : UU i} {B : A → UU j} {s t : Σ A B} →
  (Id s t) → Eq-Σ s t
pair-eq-Σ {s = s} refl = reflexive-Eq-Σ s

eq-pair-Σ :
  {i j : Level} {A : UU i} {B : A → UU j} {s t : Σ A B} →
  (α : Id (pr1 s) (pr1 t)) → Id (tr B α (pr2 s)) (pr2 t) → Id s t
eq-pair-Σ {B = B} {pair x y} {pair .x .y} refl refl = refl

eq-pair-Σ' :
  {i j : Level} {A : UU i} {B : A → UU j} {s t : Σ A B} →
  Eq-Σ s t → Id s t
eq-pair-Σ' (pair α β) = eq-pair-Σ α β

isretr-pair-eq-Σ :
  {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) →
  ((pair-eq-Σ {s = s} {t}) ∘ (eq-pair-Σ' {s = s} {t})) ~ id {A = Eq-Σ s t}
isretr-pair-eq-Σ (pair x y) (pair .x .y) (pair refl refl) = refl

issec-pair-eq-Σ :
  {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) →
  ((eq-pair-Σ' {s = s} {t}) ∘ (pair-eq-Σ {s = s} {t})) ~ id
issec-pair-eq-Σ (pair x y) .(pair x y) refl = refl

is-equiv-eq-pair-Σ :
  {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) →
  is-equiv (eq-pair-Σ' {s = s} {t})
is-equiv-eq-pair-Σ s t =
  is-equiv-has-inverse
    ( pair-eq-Σ)
    ( issec-pair-eq-Σ s t)
    ( isretr-pair-eq-Σ s t)

equiv-eq-pair-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (s t : Σ A B) → Eq-Σ s t ≃ Id s t
equiv-eq-pair-Σ s t = pair eq-pair-Σ' (is-equiv-eq-pair-Σ s t)

is-equiv-pair-eq-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (s t : Σ A B) →
  is-equiv (pair-eq-Σ {s = s} {t})
is-equiv-pair-eq-Σ s t =
  is-equiv-has-inverse
    ( eq-pair-Σ')
    ( isretr-pair-eq-Σ s t)
    ( issec-pair-eq-Σ s t)

equiv-pair-eq-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (s t : Σ A B) → Id s t ≃ Eq-Σ s t
equiv-pair-eq-Σ s t = pair pair-eq-Σ (is-equiv-pair-eq-Σ s t)

η-pair :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (t : Σ A B) →
  Id (pair (pr1 t) (pr2 t)) t
η-pair t = eq-pair-Σ refl refl

Eq-prod :
  {i j : Level} {A : UU i} {B : UU j} (s t : A × B) → UU (i ⊔ j)
Eq-prod s t = (Id (pr1 s) (pr1 t)) × (Id (pr2 s) (pr2 t))

eq-pair' :
  {i j : Level} {A : UU i} {B : UU j} {s t : prod A B} →
  Eq-prod s t → Id s t
eq-pair' {s = pair x y} {pair .x .y} (pair refl refl) = refl

eq-pair :
  {i j : Level} {A : UU i} {B : UU j} {s t : prod A B} →
  Id (pr1 s) (pr1 t) → Id (pr2 s) (pr2 t) → Id s t
eq-pair p q = eq-pair' (pair p q)

pair-eq :
  {i j : Level} {A : UU i} {B : UU j} {s t : prod A B} →
  Id s t → Eq-prod s t
pair-eq α = pair (ap pr1 α) (ap pr2 α)

isretr-pair-eq :
  {i j : Level} {A : UU i} {B : UU j} {s t : prod A B} →
  ((pair-eq {s = s} {t}) ∘ (eq-pair' {s = s} {t})) ~ id
isretr-pair-eq {s = pair x y} {pair .x .y} (pair refl refl) = refl

issec-pair-eq :
  {i j : Level} {A : UU i} {B : UU j} {s t : prod A B} →
  ((eq-pair' {s = s} {t}) ∘ (pair-eq {s = s} {t})) ~ id
issec-pair-eq {s = pair x y} {pair .x .y} refl = refl

is-equiv-eq-pair :
  {i j : Level} {A : UU i} {B : UU j} (s t : prod A B) →
  is-equiv (eq-pair' {s = s} {t})
is-equiv-eq-pair s t =
  is-equiv-has-inverse pair-eq issec-pair-eq isretr-pair-eq

equiv-eq-pair :
  {i j : Level} {A : UU i} {B : UU j} (s t : prod A B) →
  Eq-prod s t ≃ Id s t
equiv-eq-pair s t = pair eq-pair' (is-equiv-eq-pair s t)

is-equiv-pair-eq :
  {i j : Level} {A : UU i} {B : UU j} (s t : A × B) →
  is-equiv (pair-eq {s = s} {t})
is-equiv-pair-eq s t =
  is-equiv-has-inverse eq-pair' isretr-pair-eq issec-pair-eq

equiv-pair-eq :
  {i j : Level} {A : UU i} {B : UU j} (s t : A × B) →
  Id s t ≃ Eq-prod s t
equiv-pair-eq s t = pair pair-eq (is-equiv-pair-eq s t)

swap-prod :
  {i j : Level} (A : UU i) (B : UU j) → prod A B → prod B A
swap-prod A B t = pair (pr2 t) (pr1 t)

swap-swap-prod :
  {i j : Level} (A : UU i) (B : UU j) →
  ((swap-prod B A) ∘ (swap-prod A B)) ~ id
swap-swap-prod A B (pair x y) = refl

is-equiv-swap-prod :
  {i j : Level} (A : UU i) (B : UU j) →
  is-equiv (swap-prod A B)
is-equiv-swap-prod A B =
  is-equiv-has-inverse
    ( swap-prod B A)
    ( swap-swap-prod B A)
    ( swap-swap-prod A B)

equiv-swap-prod :
  {i j : Level} (A : UU i) (B : UU j) → (A × B) ≃ (B × A)
equiv-swap-prod A B = pair (swap-prod A B) (is-equiv-swap-prod A B)

triple :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  (a : A) (b : B a) → C a b → Σ A (λ x → Σ (B x) (C x))
triple a b c = pair a (pair b c)

triple' :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  (a : A) (b : B a) → C (pair a b) → Σ (Σ A B) C
triple' a b c = pair (pair a b) c

map-assoc-Σ :
  {i j k : Level} (A : UU i) (B : A → UU j) (C : (Σ A B) → UU k) →
  Σ (Σ A B) C → Σ A (λ x → Σ (B x) (λ y → C (pair x y)))
map-assoc-Σ A B C (pair (pair x y) z) = triple x y z

map-inv-assoc-Σ :
  {i j k : Level} (A : UU i) (B : A → UU j) (C : (Σ A B) → UU k) →
  Σ A (λ x → Σ (B x) (λ y → C (pair x y))) → Σ (Σ A B) C
map-inv-assoc-Σ A B C t = triple' (pr1 t) (pr1 (pr2 t)) (pr2 (pr2 t))

isretr-map-inv-assoc-Σ :
  {i j k : Level} (A : UU i) (B : A → UU j)
  (C : (Σ A B) → UU k) → ((map-inv-assoc-Σ  A B C) ∘ (map-assoc-Σ A B C)) ~ id
isretr-map-inv-assoc-Σ A B C (pair (pair x y) z) = refl

issec-map-inv-assoc-Σ :
  {i j k : Level} (A : UU i) (B : A → UU j)
  (C : (Σ A B) → UU k) → ((map-assoc-Σ A B C) ∘ (map-inv-assoc-Σ A B C)) ~ id
issec-map-inv-assoc-Σ A B C (pair x (pair y z)) = refl

is-equiv-map-assoc-Σ :
  {i j k : Level} (A : UU i) (B : A → UU j)
  (C : (Σ A B) → UU k) → is-equiv (map-assoc-Σ A B C)
is-equiv-map-assoc-Σ A B C =
  is-equiv-has-inverse
    ( map-inv-assoc-Σ A B C)
    ( issec-map-inv-assoc-Σ A B C)
    ( isretr-map-inv-assoc-Σ A B C)

assoc-Σ :
  {i j k : Level} (A : UU i) (B : A → UU j) (C : (Σ A B) → UU k) →
  Σ (Σ A B) C ≃ Σ A (λ x → Σ (B x) (λ y → C (pair x y)))
assoc-Σ A B C =
  pair (map-assoc-Σ A B C) (is-equiv-map-assoc-Σ A B C)

inv-assoc-Σ :
  {i j k : Level} (A : UU i) (B : A → UU j) (C : (Σ A B) → UU k) →
  Σ A (λ x → Σ (B x) (λ y → C (pair x y))) ≃ Σ (Σ A B) C
inv-assoc-Σ A B C =
  pair
    ( map-inv-assoc-Σ A B C)
    ( is-equiv-has-inverse
      ( map-assoc-Σ A B C)
      ( isretr-map-inv-assoc-Σ A B C)
      ( issec-map-inv-assoc-Σ A B C))

map-commutative-prod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → A × B → B × A
map-commutative-prod A B (pair a b) = pair b a

map-inv-commutative-prod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → B × A → A × B
map-inv-commutative-prod A B = map-commutative-prod B A

issec-map-inv-commutative-prod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  (map-commutative-prod A B ∘ map-inv-commutative-prod A B) ~ id
issec-map-inv-commutative-prod A B (pair b a) = refl

isretr-map-inv-commutative-prod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  (map-inv-commutative-prod A B ∘ map-commutative-prod A B) ~ id
isretr-map-inv-commutative-prod A B (pair a b) = refl

is-equiv-map-commutative-prod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-equiv (map-commutative-prod A B)
is-equiv-map-commutative-prod A B =
  is-equiv-has-inverse
    ( map-inv-commutative-prod A B)
    ( issec-map-inv-commutative-prod A B)
    ( isretr-map-inv-commutative-prod A B)

commutative-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A × B) ≃ (B × A)
commutative-prod {l1} {l2} {A} {B} =
  pair (map-commutative-prod A B) (is-equiv-map-commutative-prod A B)

map-right-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-empty B → coprod A B → A
map-right-unit-law-coprod-is-empty A B nb (inl a) = a
map-right-unit-law-coprod-is-empty A B nb (inr b) = ex-falso (nb b)

map-left-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-empty A → coprod A B → B
map-left-unit-law-coprod-is-empty A B na (inl a) = ex-falso (na a)
map-left-unit-law-coprod-is-empty A B na (inr b) = b

map-inv-left-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-empty A → B → coprod A B
map-inv-left-unit-law-coprod-is-empty A B H = inr

issec-map-inv-left-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty A) →
  ( map-left-unit-law-coprod-is-empty A B H ∘ map-inv-left-unit-law-coprod-is-empty A B H) ~ id
issec-map-inv-left-unit-law-coprod-is-empty A B H a = refl

isretr-map-inv-left-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty A) →
  ( map-inv-left-unit-law-coprod-is-empty A B H ∘ map-left-unit-law-coprod-is-empty A B H) ~ id
isretr-map-inv-left-unit-law-coprod-is-empty A B H (inl a) = ex-falso (H a)
isretr-map-inv-left-unit-law-coprod-is-empty A B H (inr b) = refl

is-equiv-map-left-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty A) →
  is-equiv (map-left-unit-law-coprod-is-empty A B H)
is-equiv-map-left-unit-law-coprod-is-empty A B H =
  is-equiv-has-inverse
    ( map-inv-left-unit-law-coprod-is-empty A B H)
    ( issec-map-inv-left-unit-law-coprod-is-empty A B H)
    ( isretr-map-inv-left-unit-law-coprod-is-empty A B H)

left-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty A) →
  coprod A B ≃ B
left-unit-law-coprod-is-empty A B H =
  pair (map-left-unit-law-coprod-is-empty A B H) (is-equiv-map-left-unit-law-coprod-is-empty A B H)

inv-left-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty A) →
  B ≃ coprod A B
inv-left-unit-law-coprod-is-empty A B H =
  pair ( map-inv-left-unit-law-coprod-is-empty A B H)
       ( is-equiv-has-inverse
         ( map-left-unit-law-coprod-is-empty A B H)
         ( isretr-map-inv-left-unit-law-coprod-is-empty A B H)
         ( issec-map-inv-left-unit-law-coprod-is-empty A B H))

map-left-unit-law-coprod :
  {l : Level} (B : UU l) → coprod empty B → B
map-left-unit-law-coprod B =
  map-left-unit-law-coprod-is-empty empty B id

map-inv-left-unit-law-coprod :
  {l : Level} (B : UU l) → B → coprod empty B
map-inv-left-unit-law-coprod B = inr

issec-map-inv-left-unit-law-coprod :
  {l : Level} (B : UU l) →
  ( map-left-unit-law-coprod B ∘ map-inv-left-unit-law-coprod B) ~ id
issec-map-inv-left-unit-law-coprod B =
  issec-map-inv-left-unit-law-coprod-is-empty empty B id

isretr-map-inv-left-unit-law-coprod :
  {l : Level} (B : UU l) →
  ( map-inv-left-unit-law-coprod B ∘ map-left-unit-law-coprod B) ~ id
isretr-map-inv-left-unit-law-coprod B =
  isretr-map-inv-left-unit-law-coprod-is-empty empty B id

is-equiv-map-left-unit-law-coprod :
  {l : Level} (B : UU l) → is-equiv (map-left-unit-law-coprod B)
is-equiv-map-left-unit-law-coprod B =
  is-equiv-map-left-unit-law-coprod-is-empty empty B id

left-unit-law-coprod :
  {l : Level} (B : UU l) → coprod empty B ≃ B
left-unit-law-coprod B =
  left-unit-law-coprod-is-empty empty B id

inv-left-unit-law-coprod :
  {l : Level} (B : UU l) → B ≃ (coprod empty B)
inv-left-unit-law-coprod B =
  inv-left-unit-law-coprod-is-empty empty B id

map-inv-right-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-empty B → A → coprod A B
map-inv-right-unit-law-coprod-is-empty A B is-empty-B = inl

issec-map-inv-right-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty B) →
  ( map-right-unit-law-coprod-is-empty A B H ∘ map-inv-right-unit-law-coprod-is-empty A B H) ~ id
issec-map-inv-right-unit-law-coprod-is-empty A B H a = refl

isretr-map-inv-right-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty B) →
  ( map-inv-right-unit-law-coprod-is-empty A B H ∘ map-right-unit-law-coprod-is-empty A B H) ~ id
isretr-map-inv-right-unit-law-coprod-is-empty A B H (inl a) = refl
isretr-map-inv-right-unit-law-coprod-is-empty A B H (inr b) = ex-falso (H b)

is-equiv-map-right-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty B) →
  is-equiv (map-right-unit-law-coprod-is-empty A B H)
is-equiv-map-right-unit-law-coprod-is-empty A B H =
  is-equiv-has-inverse
    ( map-inv-right-unit-law-coprod-is-empty A B H)
    ( issec-map-inv-right-unit-law-coprod-is-empty A B H)
    ( isretr-map-inv-right-unit-law-coprod-is-empty A B H)

is-equiv-inl-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  is-empty B → is-equiv (inl {l1} {l2} {A} {B})
is-equiv-inl-is-empty A B H =
  is-equiv-has-inverse
    ( map-right-unit-law-coprod-is-empty A B H)
    ( isretr-map-inv-right-unit-law-coprod-is-empty A B H)
    ( issec-map-inv-right-unit-law-coprod-is-empty A B H)

right-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-empty B →
  (coprod A B) ≃ A
right-unit-law-coprod-is-empty A B H =
  pair ( map-right-unit-law-coprod-is-empty A B H)
       ( is-equiv-map-right-unit-law-coprod-is-empty A B H)

inv-right-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-empty B →
  A ≃ (coprod A B)
inv-right-unit-law-coprod-is-empty A B H =
  pair ( inl)
       ( is-equiv-has-inverse
         ( map-right-unit-law-coprod-is-empty A B H)
          ( isretr-map-inv-right-unit-law-coprod-is-empty A B H)
         ( issec-map-inv-right-unit-law-coprod-is-empty A B H))

map-right-unit-law-coprod :
  {l1 : Level} (A : UU l1) → coprod A empty → A
map-right-unit-law-coprod A = map-right-unit-law-coprod-is-empty A empty id

map-inv-right-unit-law-coprod :
  {l1 : Level} (A : UU l1) → A → coprod A empty
map-inv-right-unit-law-coprod A = inl

issec-map-inv-right-unit-law-coprod :
  {l1 : Level} (A : UU l1) →
  ( map-right-unit-law-coprod A ∘ map-inv-right-unit-law-coprod A) ~ id
issec-map-inv-right-unit-law-coprod A =
  issec-map-inv-right-unit-law-coprod-is-empty A empty id

isretr-map-inv-right-unit-law-coprod :
  {l1 : Level} (A : UU l1) →
  ( map-inv-right-unit-law-coprod A ∘ map-right-unit-law-coprod A) ~ id
isretr-map-inv-right-unit-law-coprod A =
  isretr-map-inv-right-unit-law-coprod-is-empty A empty id

is-equiv-map-right-unit-law-coprod :
  {l1 : Level} (A : UU l1) → is-equiv (map-right-unit-law-coprod A)
is-equiv-map-right-unit-law-coprod A =
  is-equiv-map-right-unit-law-coprod-is-empty A empty id

right-unit-law-coprod :
  {l1 : Level} (A : UU l1) → coprod A empty ≃ A
right-unit-law-coprod A =
  right-unit-law-coprod-is-empty A empty id

inv-right-unit-law-coprod :
  {l1 : Level} (A : UU l1) → A ≃ coprod A empty
inv-right-unit-law-coprod A =
  inv-right-unit-law-coprod-is-empty A empty id

htpy-map-coprod :
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  {f f' : A → A'} (H : f ~ f') {g g' : B → B'} (K : g ~ g') →
  (map-coprod f g) ~ (map-coprod f' g')
htpy-map-coprod H K (inl x) = ap inl (H x)
htpy-map-coprod H K (inr y) = ap inr (K y)

id-map-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  (map-coprod (id {A = A}) (id {A = B})) ~ id
id-map-coprod A B (inl x) = refl
id-map-coprod A B (inr x) = refl

compose-map-coprod :
  {l1 l2 l1' l2' l1'' l2'' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  {A'' : UU l1''} {B'' : UU l2''}
  (f : A → A') (f' : A' → A'') (g : B → B') (g' : B' → B'') →
  (map-coprod (f' ∘ f) (g' ∘ g)) ~
  ((map-coprod f' g') ∘ (map-coprod f g))
compose-map-coprod f f' g g' (inl x) = refl
compose-map-coprod f f' g g' (inr y) = refl

is-equiv-map-coprod :
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  {f : A → A'} {g : B → B'} →
  is-equiv f → is-equiv g → is-equiv (map-coprod f g)
is-equiv-map-coprod {A = A} {B = B} {A' = A'} {B' = B'} {f = f} {g = g}
  (pair (pair sf issec-sf) (pair rf isretr-rf))
  (pair (pair sg issec-sg) (pair rg isretr-rg)) =
  pair
    ( pair
      ( map-coprod sf sg)
      ( ( ( inv-htpy (compose-map-coprod sf f sg g)) ∙h
          ( htpy-map-coprod issec-sf issec-sg)) ∙h
        ( id-map-coprod A' B')))
    ( pair
      ( map-coprod rf rg)
      ( ( ( inv-htpy (compose-map-coprod f rf g rg)) ∙h
          ( htpy-map-coprod isretr-rf isretr-rg)) ∙h
        ( id-map-coprod A B)))
  
equiv-coprod :
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'} →
  (A ≃ A') → (B ≃ B') → ((coprod A B) ≃ (coprod A' B'))
equiv-coprod (pair e is-equiv-e) (pair f is-equiv-f) =
  pair
    ( map-coprod e f)
    ( is-equiv-map-coprod is-equiv-e is-equiv-f)

map-assoc-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  coprod (coprod A B) C → coprod A (coprod B C)
map-assoc-coprod (inl (inl x)) = inl x
map-assoc-coprod (inl (inr x)) = inr (inl x)
map-assoc-coprod (inr x) = inr (inr x)

map-inv-assoc-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  coprod A (coprod B C) → coprod (coprod A B) C
map-inv-assoc-coprod (inl x) = inl (inl x)
map-inv-assoc-coprod (inr (inl x)) = inl (inr x)
map-inv-assoc-coprod (inr (inr x)) = inr x

issec-map-inv-assoc-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  ( map-assoc-coprod {A = A} {B} {C} ∘ map-inv-assoc-coprod) ~ id
issec-map-inv-assoc-coprod (inl x) = refl
issec-map-inv-assoc-coprod (inr (inl x)) = refl
issec-map-inv-assoc-coprod (inr (inr x)) = refl

isretr-map-inv-assoc-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  ( map-inv-assoc-coprod ∘ map-assoc-coprod {A = A} {B} {C}) ~ id
isretr-map-inv-assoc-coprod (inl (inl x)) = refl
isretr-map-inv-assoc-coprod (inl (inr x)) = refl
isretr-map-inv-assoc-coprod (inr x) = refl

is-equiv-map-assoc-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  is-equiv (map-assoc-coprod {A = A} {B} {C})
is-equiv-map-assoc-coprod =
  is-equiv-has-inverse
    map-inv-assoc-coprod
    issec-map-inv-assoc-coprod
    isretr-map-inv-assoc-coprod

is-equiv-map-inv-assoc-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  is-equiv (map-inv-assoc-coprod {A = A} {B} {C})
is-equiv-map-inv-assoc-coprod =
  is-equiv-has-inverse
    map-assoc-coprod
    isretr-map-inv-assoc-coprod
    issec-map-inv-assoc-coprod

assoc-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  coprod (coprod A B) C ≃ coprod A (coprod B C)
assoc-coprod = pair map-assoc-coprod is-equiv-map-assoc-coprod

inv-assoc-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  coprod A (coprod B C) ≃ coprod (coprod A B) C
inv-assoc-coprod = pair map-inv-assoc-coprod is-equiv-map-inv-assoc-coprod

coprod-Fin :
  (k l : ℕ) → coprod (Fin k) (Fin l) ≃ Fin (add-ℕ k l)
coprod-Fin k zero-ℕ = right-unit-law-coprod (Fin k)
coprod-Fin k (succ-ℕ l) =
  (equiv-coprod (coprod-Fin k l) equiv-id) ∘e inv-assoc-coprod

map-right-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2)
  (C : coprod A B → UU l3) → Σ (coprod A B) C →
  coprod (Σ A (λ x → C (inl x))) (Σ B (λ y → C (inr y)))
map-right-distributive-Σ-coprod A B C (pair (inl x) z) = inl (pair x z)
map-right-distributive-Σ-coprod A B C (pair (inr y) z) = inr (pair y z)

map-inv-right-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2)
  (C : coprod A B → UU l3) →
  coprod (Σ A (λ x → C (inl x))) (Σ B (λ y → C (inr y))) → Σ (coprod A B) C
map-inv-right-distributive-Σ-coprod A B C (inl (pair x z)) = pair (inl x) z
map-inv-right-distributive-Σ-coprod A B C (inr (pair y z)) = pair (inr y) z

issec-map-inv-right-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : coprod A B → UU l3) →
  ( (map-right-distributive-Σ-coprod A B C) ∘
    (map-inv-right-distributive-Σ-coprod A B C)) ~ id
issec-map-inv-right-distributive-Σ-coprod A B C (inl (pair x z)) = refl
issec-map-inv-right-distributive-Σ-coprod A B C (inr (pair y z)) = refl

isretr-map-inv-right-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : coprod A B → UU l3) →
  ( (map-inv-right-distributive-Σ-coprod A B C) ∘
    (map-right-distributive-Σ-coprod A B C)) ~ id
isretr-map-inv-right-distributive-Σ-coprod A B C (pair (inl x) z) = refl
isretr-map-inv-right-distributive-Σ-coprod A B C (pair (inr y) z) = refl

is-equiv-map-right-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : coprod A B → UU l3) →
  is-equiv (map-right-distributive-Σ-coprod A B C)
is-equiv-map-right-distributive-Σ-coprod A B C =
  is-equiv-has-inverse
    ( map-inv-right-distributive-Σ-coprod A B C)
    ( issec-map-inv-right-distributive-Σ-coprod A B C)
    ( isretr-map-inv-right-distributive-Σ-coprod A B C)

right-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : coprod A B → UU l3) →
  Σ (coprod A B) C ≃ coprod (Σ A (λ x → C (inl x))) (Σ B (λ y → C (inr y)))
right-distributive-Σ-coprod A B C =
  pair ( map-right-distributive-Σ-coprod A B C)
       ( is-equiv-map-right-distributive-Σ-coprod A B C)

issec-map-inv-raise :
  {l l1 : Level} {A : UU l1} (x : raise l A) →
  Id (map-raise (map-inv-raise x)) x
issec-map-inv-raise (map-raise x) = refl

isretr-map-inv-raise :
  {l l1 : Level} {A : UU l1} (x : A) → Id (map-inv-raise {l} (map-raise x)) x
isretr-map-inv-raise x = refl

is-equiv-map-raise :
  (l : Level) {l1 : Level} (A : UU l1) → is-equiv (map-raise {l} {l1} {A})
is-equiv-map-raise l A =
  is-equiv-has-inverse
    map-inv-raise
    ( issec-map-inv-raise)
    ( isretr-map-inv-raise {l})

equiv-raise : (l : Level) {l1 : Level} (A : UU l1) → A ≃ raise l A
equiv-raise l A = pair map-raise (is-equiv-map-raise l A)

equiv-raise-unit : (l : Level) → unit ≃ raise-unit l
equiv-raise-unit l = equiv-raise l unit

equiv-raise-empty : (l : Level) → empty ≃ raise-empty l
equiv-raise-empty l = equiv-raise l empty

Raise :
  (l : Level) {l1 : Level} (A : UU l1) → Σ (UU (l1 ⊔ l)) (λ X → A ≃ X)
Raise l A = pair (raise l A) (equiv-raise l A)

is-equiv-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-empty B → is-equiv f
is-equiv-is-empty f H =
  is-equiv-has-inverse
    ( ex-falso ∘ H)
    ( λ y → ex-falso (H y))
    ( λ x → ex-falso (H (f x)))

is-equiv-is-empty' :
  {l : Level} {A : UU l} (f : is-empty A) → is-equiv f
is-equiv-is-empty' f = is-equiv-is-empty f id

map-right-absorption-Σ :
  {l : Level} (A : UU l) → Σ A (λ x → empty) → empty
map-right-absorption-Σ A (pair x ())

map-right-absorption-prod = map-right-absorption-Σ

is-equiv-map-right-absorption-Σ :
  {l : Level} (A : UU l) → is-equiv (map-right-absorption-Σ A)
is-equiv-map-right-absorption-Σ A =
  is-equiv-is-empty' (map-right-absorption-Σ A)

is-equiv-map-right-absorption-prod = is-equiv-map-right-absorption-Σ

right-absorption-Σ :
  {l : Level} (A : UU l) → Σ A (λ x → empty) ≃ empty
right-absorption-Σ A =
  pair (map-right-absorption-Σ A) (is-equiv-map-right-absorption-Σ A)

right-absorption-prod :
  {l : Level} (A : UU l) → (A × empty) ≃ empty
right-absorption-prod = right-absorption-Σ

map-left-unit-law-Σ :
  {l : Level} (A : unit → UU l) → Σ unit A → A star
map-left-unit-law-Σ A (pair star a) = a

map-inv-left-unit-law-Σ :
  {l : Level} (A : unit → UU l) → A star → Σ unit A
map-inv-left-unit-law-Σ A a = (pair star a)

issec-map-inv-left-unit-law-Σ :
  {l : Level} (A : unit → UU l) →
  ( map-left-unit-law-Σ A ∘ map-inv-left-unit-law-Σ A) ~ id
issec-map-inv-left-unit-law-Σ A a = refl

isretr-map-inv-left-unit-law-Σ :
  {l : Level} (A : unit → UU l) →
  ( map-inv-left-unit-law-Σ A ∘ map-left-unit-law-Σ A) ~ id
isretr-map-inv-left-unit-law-Σ A (pair star a) = refl

is-equiv-map-left-unit-law-Σ :
  {l : Level} (A : unit → UU l) → is-equiv (map-left-unit-law-Σ A)
is-equiv-map-left-unit-law-Σ A =
  is-equiv-has-inverse
    ( map-inv-left-unit-law-Σ A)
    ( issec-map-inv-left-unit-law-Σ A)
    ( isretr-map-inv-left-unit-law-Σ A)

left-unit-law-Σ :
  {l : Level} (A : unit → UU l) → Σ unit A ≃ A star
left-unit-law-Σ A =
  pair (map-left-unit-law-Σ A) (is-equiv-map-left-unit-law-Σ A)

is-equiv-map-inv-left-unit-law-Σ :
  {l : Level} (A : unit → UU l) → is-equiv (map-inv-left-unit-law-Σ A)
is-equiv-map-inv-left-unit-law-Σ A =
  is-equiv-has-inverse
    ( map-left-unit-law-Σ A)
    ( isretr-map-inv-left-unit-law-Σ A)
    ( issec-map-inv-left-unit-law-Σ A)

map-left-unit-law-prod :
  {l : Level} (A : UU l) → unit × A → A
map-left-unit-law-prod A = pr2

map-inv-left-unit-law-prod :
  {l : Level} (A : UU l) → A → unit × A
map-inv-left-unit-law-prod A = map-inv-left-unit-law-Σ (λ x → A)

issec-map-inv-left-unit-law-prod :
  {l : Level} (A : UU l) →
  ( map-left-unit-law-prod A ∘ map-inv-left-unit-law-prod A) ~ id
issec-map-inv-left-unit-law-prod A =
  issec-map-inv-left-unit-law-Σ (λ x → A)

isretr-map-inv-left-unit-law-prod :
  {l : Level} (A : UU l) →
  ( map-inv-left-unit-law-prod A ∘ map-left-unit-law-prod A) ~ id
isretr-map-inv-left-unit-law-prod A (pair star a) = refl

is-equiv-map-left-unit-law-prod :
  {l : Level} (A : UU l) → is-equiv (map-left-unit-law-prod A)
is-equiv-map-left-unit-law-prod A =
  is-equiv-has-inverse
    ( map-inv-left-unit-law-prod A)
    ( issec-map-inv-left-unit-law-prod A)
    ( isretr-map-inv-left-unit-law-prod A)

left-unit-law-prod :
  {l : Level} (A : UU l) → (unit × A) ≃ A
left-unit-law-prod A =
  pair
    ( map-left-unit-law-prod A)
    ( is-equiv-map-left-unit-law-prod A)

is-equiv-map-inv-left-unit-law-prod :
  {l : Level} (A : UU l) → is-equiv (map-inv-left-unit-law-prod A)
is-equiv-map-inv-left-unit-law-prod A =
  is-equiv-has-inverse
    ( map-left-unit-law-prod A)
    ( isretr-map-inv-left-unit-law-prod A)
    ( issec-map-inv-left-unit-law-prod A)

inv-left-unit-law-prod :
  {l : Level} (A : UU l) → A ≃ (unit × A)
inv-left-unit-law-prod A =
  pair
    ( map-inv-left-unit-law-prod A)
    ( is-equiv-map-inv-left-unit-law-prod A)

map-right-unit-law-prod :
  {l1 : Level} {A : UU l1} → A × unit → A
map-right-unit-law-prod = pr1

map-inv-right-unit-law-prod :
  {l1 : Level} {A : UU l1} → A → A × unit
map-inv-right-unit-law-prod a = pair a star

issec-map-inv-right-unit-law-prod :
  {l1 : Level} {A : UU l1} →
  (map-right-unit-law-prod {A = A} ∘ map-inv-right-unit-law-prod {A = A}) ~ id
issec-map-inv-right-unit-law-prod a = refl

isretr-map-inv-right-unit-law-prod :
  {l1 : Level} {A : UU l1} →
  (map-inv-right-unit-law-prod {A = A} ∘ map-right-unit-law-prod {A = A}) ~ id
isretr-map-inv-right-unit-law-prod (pair a star) = refl

is-equiv-map-right-unit-law-prod :
  {l1 : Level} {A : UU l1} → is-equiv (map-right-unit-law-prod {A = A})
is-equiv-map-right-unit-law-prod =
  is-equiv-has-inverse
    map-inv-right-unit-law-prod
    issec-map-inv-right-unit-law-prod
    isretr-map-inv-right-unit-law-prod

right-unit-law-prod : {l1 : Level} {A : UU l1} → (A × unit) ≃ A
right-unit-law-prod =
  pair map-right-unit-law-prod is-equiv-map-right-unit-law-prod

is-injective-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-equiv f → is-injective f
is-injective-is-equiv {l1} {l2} {A} {B} {f} H {x} {y} p =
  ( inv (isretr-map-inv-is-equiv' H x)) ∙
  ( ( ap (map-inv-is-equiv H) p) ∙
    ( isretr-map-inv-is-equiv' H y))

is-injective-map-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (e : A ≃ B) → is-injective (map-equiv e)
is-injective-map-equiv (pair f H) = is-injective-is-equiv H

is-injective-map-inv-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (e : A ≃ B) → is-injective (map-inv-equiv' e)
is-injective-map-inv-equiv e =
  is-injective-is-equiv (is-equiv-map-inv-equiv e)

map-left-absorption-Σ :
  {l : Level} (A : empty → UU l) → Σ empty A → empty
map-left-absorption-Σ A = pr1

map-left-absorption-prod :
  {l : Level} (A : UU l) → empty × A → empty
map-left-absorption-prod A = map-left-absorption-Σ (λ x → A)

is-equiv-map-left-absorption-Σ :
  {l : Level} (A : empty → UU l) → is-equiv (map-left-absorption-Σ A)
is-equiv-map-left-absorption-Σ A =
  is-equiv-is-empty' (map-left-absorption-Σ A)

is-equiv-map-left-absorption-prod :
  {l : Level} (A : UU l) → is-equiv (map-left-absorption-prod A)
is-equiv-map-left-absorption-prod A =
  is-equiv-map-left-absorption-Σ (λ x → A)

left-absorption-Σ :
  {l : Level} (A : empty → UU l) → Σ empty A ≃ empty
left-absorption-Σ A =
  pair (map-left-absorption-Σ A) (is-equiv-map-left-absorption-Σ A)

left-absorption-prod :
  {l : Level} (A : UU l) → (empty × A) ≃ empty
left-absorption-prod A = left-absorption-Σ (λ x → A)

map-prod-pr1 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) → (pr1 ∘ (map-prod f g)) ~ (f ∘ pr1)
map-prod-pr1 f g (pair a b) = refl

map-prod-pr2 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) → (pr2 ∘ (map-prod f g)) ~ (g ∘ pr2)
map-prod-pr2 f g (pair a b) = refl

map-prod-id :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (map-prod (id {A = A}) (id {A = B})) ~ id
map-prod-id (pair a b) = refl

map-prod-comp :
  {l1 l2 l3 l4 l5 l6 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {E : UU l5} {F : UU l6} (f : A → C) (g : B → D) (h : C → E) (k : D → F) →
  map-prod (h ∘ f) (k ∘ g) ~ ((map-prod h k) ∘ (map-prod f g))
map-prod-comp f g h k (pair a b) = refl

htpy-map-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f f' : A → C} (H : f ~ f') {g g' : B → D} (K : g ~ g') →
  map-prod f g ~ map-prod f' g'
htpy-map-prod {f = f} {f'} H {g} {g'} K (pair a b) =
  eq-pair (H a) (K b)

is-equiv-map-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) →
  is-equiv f → is-equiv g → is-equiv (map-prod f g)
is-equiv-map-prod f g
  ( pair (pair sf issec-sf) (pair rf isretr-rf))
  ( pair (pair sg issec-sg) (pair rg isretr-rg)) =
  pair
    ( pair
      ( map-prod sf sg)
      ( ( inv-htpy (map-prod-comp sf sg f g)) ∙h
        ( (htpy-map-prod issec-sf issec-sg) ∙h map-prod-id)))
    ( pair
      ( map-prod rf rg)
      ( ( inv-htpy (map-prod-comp f g rf rg)) ∙h
        ( (htpy-map-prod isretr-rf isretr-rg) ∙h map-prod-id)))

equiv-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A ≃ C) (g : B ≃ D) → (A × B) ≃ (C × D)
equiv-prod (pair f is-equiv-f) (pair g is-equiv-g) =
  pair (map-prod f g) (is-equiv-map-prod f g is-equiv-f is-equiv-g)

map-right-distributive-prod-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  (coprod A B) × C → coprod (A × C) (B × C)
map-right-distributive-prod-coprod A B C =
  map-right-distributive-Σ-coprod A B (λ x → C)

map-inv-right-distributive-prod-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  coprod (A × C) (B × C) → (coprod A B) × C
map-inv-right-distributive-prod-coprod A B C =
  map-inv-right-distributive-Σ-coprod A B (λ x → C)

issec-map-inv-right-distributive-prod-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  ( (map-right-distributive-prod-coprod A B C) ∘
    (map-inv-right-distributive-prod-coprod A B C)) ~ id
issec-map-inv-right-distributive-prod-coprod A B C =
  issec-map-inv-right-distributive-Σ-coprod A B (λ x → C)

isretr-map-inv-right-distributive-prod-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  ( (map-inv-right-distributive-prod-coprod A B C) ∘
    (map-right-distributive-prod-coprod A B C)) ~ id
isretr-map-inv-right-distributive-prod-coprod A B C =
  isretr-map-inv-right-distributive-Σ-coprod A B (λ x → C)

is-equiv-map-right-distributive-prod-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  is-equiv (map-right-distributive-prod-coprod A B C)
is-equiv-map-right-distributive-prod-coprod A B C =
  is-equiv-map-right-distributive-Σ-coprod A B (λ x → C)

right-distributive-prod-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3) →
  ((coprod A B) × C) ≃ coprod (A × C) (B × C)
right-distributive-prod-coprod A B C =
  right-distributive-Σ-coprod A B (λ x → C)

prod-Fin : (k l : ℕ) → ((Fin k) × (Fin l)) ≃ Fin (mul-ℕ k l)
prod-Fin zero-ℕ l = left-absorption-prod (Fin l)
prod-Fin (succ-ℕ k) l =
  ( ( coprod-Fin (mul-ℕ k l) l) ∘e
    ( equiv-coprod (prod-Fin k l) (left-unit-law-prod (Fin l)))) ∘e
  ( right-distributive-prod-coprod (Fin k) unit (Fin l))

Fin-mul-ℕ : (k l : ℕ) → (Fin (mul-ℕ k l)) ≃ ((Fin k) × (Fin l))
Fin-mul-ℕ k l = inv-equiv (prod-Fin k l)

is-equiv-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y} (i : A ≃ X) (j : B ≃ Y)
  (H : (map-equiv j ∘ f) ~ (g ∘ map-equiv i)) → is-equiv g → is-equiv f
is-equiv-equiv {f = f} {g} i j H K =
  is-equiv-right-factor'
    ( map-equiv j)
    ( f)
    ( is-equiv-map-equiv j)
    ( is-equiv-comp
      ( map-equiv j ∘ f)
      ( g)
      ( map-equiv i)
      ( H)
      ( is-equiv-map-equiv i)
      ( K))

is-equiv-equiv' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y} (i : A ≃ X) (j : B ≃ Y)
  (H : (map-equiv j ∘ f) ~ (g ∘ map-equiv i)) → is-equiv f → is-equiv g
is-equiv-equiv' {f = f} {g} i j H K =
  is-equiv-left-factor'
    ( g)
    ( map-equiv i)
    ( is-equiv-comp
      ( g ∘ map-equiv i)
      ( map-equiv j)
      ( f)
      ( inv-htpy H)
      ( K)
      ( is-equiv-map-equiv j))
    ( is-equiv-map-equiv i)

concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} → Id y z → Id x y → Id x z
concat' x q p = p ∙ q

inv-concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} → Id y z →
  Id x z → Id x y
inv-concat' x q = concat' x (inv q)

isretr-inv-concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} (q : Id y z) →
  ((inv-concat' x q) ∘ (concat' x q)) ~ id
isretr-inv-concat' x refl refl = refl

issec-inv-concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} (q : Id y z) →
  ((concat' x q) ∘ (inv-concat' x q)) ~ id
issec-inv-concat' x refl refl = refl

is-equiv-concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} (q : Id y z) →
  is-equiv (concat' x q)
is-equiv-concat' x q =
  is-equiv-has-inverse
    ( inv-concat' x q)
    ( issec-inv-concat' x q)
    ( isretr-inv-concat' x q)

equiv-concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} (q : Id y z) →
  Id x y ≃ Id x z
equiv-concat' x q = pair (concat' x q) (is-equiv-concat' x q)

inv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
  (Id x z) → (Id y z)
inv-concat p = concat (inv p)

isretr-inv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
  ((inv-concat p z) ∘ (concat p z)) ~ id
isretr-inv-concat refl z q = refl

issec-inv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
  ((concat p z) ∘ (inv-concat p z)) ~ id
issec-inv-concat refl z refl = refl

is-equiv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
  is-equiv (concat p z)
is-equiv-concat p z =
  is-equiv-has-inverse
    ( inv-concat p z)
    ( issec-inv-concat p z)
    ( isretr-inv-concat p z)

equiv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
  Id y z ≃ Id x z
equiv-concat p z = pair (concat p z) (is-equiv-concat p z)

convert-eq-values-htpy :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} (H : f ~ g)
  (x y : A) → Id (f x) (f y) ≃ Id (g x) (g y)
convert-eq-values-htpy {f = f} {g} H x y =
  ( equiv-concat' (g x) (H y)) ∘e (equiv-concat (inv (H x)) (f y))

is-equiv-htpy :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} (g : A → B) →
  f ~ g → is-equiv g → is-equiv f
is-equiv-htpy g H (pair (pair gs issec) (pair gr isretr)) =
  pair
    ( pair gs ((H ·r gs) ∙h issec))
    ( pair gr ((gr ·l H) ∙h isretr))

is-equiv-htpy-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} (e : A ≃ B) →
  f ~ map-equiv e → is-equiv f
is-equiv-htpy-equiv e H = is-equiv-htpy (map-equiv e) H (is-equiv-map-equiv e)

map-left-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : A → UU l3) →
  Σ A (λ x → coprod (B x) (C x)) → coprod (Σ A B) (Σ A C)
map-left-distributive-Σ-coprod A B C (pair x (inl y)) = inl (pair x y)
map-left-distributive-Σ-coprod A B C (pair x (inr z)) = inr (pair x z)

map-inv-left-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : A → UU l3) →
  coprod (Σ A B) (Σ A C) → Σ A (λ x → coprod (B x) (C x))
map-inv-left-distributive-Σ-coprod A B C (inl (pair x y)) = pair x (inl y)
map-inv-left-distributive-Σ-coprod A B C (inr (pair x z)) = pair x (inr z)

issec-map-inv-left-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : A → UU l3) →
  ( ( map-left-distributive-Σ-coprod A B C) ∘
    ( map-inv-left-distributive-Σ-coprod A B C)) ~ id
issec-map-inv-left-distributive-Σ-coprod A B C (inl (pair x y)) = refl
issec-map-inv-left-distributive-Σ-coprod A B C (inr (pair x z)) = refl

isretr-map-inv-left-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : A → UU l3) →
  ( ( map-inv-left-distributive-Σ-coprod A B C) ∘
    ( map-left-distributive-Σ-coprod A B C)) ~ id
isretr-map-inv-left-distributive-Σ-coprod A B C (pair x (inl y)) = refl
isretr-map-inv-left-distributive-Σ-coprod A B C (pair x (inr z)) = refl

is-equiv-map-left-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : A → UU l3) →
  is-equiv (map-left-distributive-Σ-coprod A B C)
is-equiv-map-left-distributive-Σ-coprod A B C =
  is-equiv-has-inverse
    ( map-inv-left-distributive-Σ-coprod A B C)
    ( issec-map-inv-left-distributive-Σ-coprod A B C)
    ( isretr-map-inv-left-distributive-Σ-coprod A B C)

left-distributive-Σ-coprod :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : A → UU l3) →
  Σ A (λ x → coprod (B x) (C x)) ≃ coprod (Σ A B) (Σ A C)
left-distributive-Σ-coprod A B C =
  pair ( map-left-distributive-Σ-coprod A B C)
       ( is-equiv-map-left-distributive-Σ-coprod A B C)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : A → B → UU l3}
  where

  map-left-swap-Σ : Σ A (λ x → Σ B (C x)) → Σ B (λ y → Σ A (λ x → C x y))
  map-left-swap-Σ t = pair (pr1 (pr2 t)) (pair (pr1 t) (pr2 (pr2 t)))
  
  map-inv-left-swap-Σ :
    Σ B (λ y → Σ A (λ x → C x y)) → Σ A (λ x → Σ B (C x))
  map-inv-left-swap-Σ t = pair (pr1 (pr2 t)) (pair (pr1 t) (pr2 (pr2 t)))
  
  isretr-map-inv-left-swap-Σ : (map-inv-left-swap-Σ ∘ map-left-swap-Σ) ~ id
  isretr-map-inv-left-swap-Σ (pair x (pair y z)) = refl

  issec-map-inv-left-swap-Σ : (map-left-swap-Σ ∘ map-inv-left-swap-Σ) ~ id
  issec-map-inv-left-swap-Σ (pair x (pair y z)) = refl
  
  is-equiv-map-left-swap-Σ : is-equiv map-left-swap-Σ
  is-equiv-map-left-swap-Σ =
    is-equiv-has-inverse
      ( map-inv-left-swap-Σ)
      ( issec-map-inv-left-swap-Σ)
      ( isretr-map-inv-left-swap-Σ)
  
  equiv-left-swap-Σ : Σ A (λ a → Σ B (C a)) ≃ Σ B (λ b → Σ A (λ a → C a b))
  equiv-left-swap-Σ = pair map-left-swap-Σ is-equiv-map-left-swap-Σ

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  map-right-swap-Σ : Σ (Σ A B) (C ∘ pr1) → Σ (Σ A C) (B ∘ pr1)
  map-right-swap-Σ t = pair (pair (pr1 (pr1 t)) (pr2 t)) (pr2 (pr1 t))

  map-inv-right-swap-Σ : Σ (Σ A C) (B ∘ pr1) → Σ (Σ A B) (C ∘ pr1)
  map-inv-right-swap-Σ t = pair (pair (pr1 (pr1 t)) (pr2 t)) (pr2 (pr1 t))

  issec-map-inv-right-swap-Σ : (map-right-swap-Σ ∘ map-inv-right-swap-Σ) ~ id
  issec-map-inv-right-swap-Σ (pair (pair x y) z) = refl

  isretr-map-inv-right-swap-Σ : (map-inv-right-swap-Σ ∘ map-right-swap-Σ) ~ id
  isretr-map-inv-right-swap-Σ (pair (pair x z) y) = refl

  is-equiv-map-right-swap-Σ : is-equiv map-right-swap-Σ
  is-equiv-map-right-swap-Σ =
    is-equiv-has-inverse
      map-inv-right-swap-Σ
      issec-map-inv-right-swap-Σ
      isretr-map-inv-right-swap-Σ

  equiv-right-swap-Σ : Σ (Σ A B) (C ∘ pr1) ≃ Σ (Σ A C) (B ∘ pr1)
  equiv-right-swap-Σ = pair map-right-swap-Σ is-equiv-map-right-swap-Σ

--------------------------------------------------------------------------------

-- Contractible types

is-contr :
  {l : Level} → UU l → UU l
is-contr A = Σ A (λ a → (x : A) → Id a x)

center :
  {l : Level} {A : UU l} → is-contr A → A
center (pair c is-contr-A) = c

eq-is-contr' :
  {l : Level} {A : UU l} → is-contr A → (x y : A) → Id x y
eq-is-contr' (pair c C) x y = (inv (C x)) ∙ (C y)

eq-is-contr :
  {l : Level} {A : UU l} → is-contr A → {x y : A} → Id x y
eq-is-contr (pair c C) {x} {y} = (inv (C x)) ∙ (C y)

contraction :
  {l : Level} {A : UU l} (is-contr-A : is-contr A) →
  (const A A (center is-contr-A) ~ id)
contraction (pair c C) x = eq-is-contr (pair c C)

coh-contraction :
  {l : Level} {A : UU l} (is-contr-A : is-contr A) →
  Id (contraction is-contr-A (center is-contr-A)) refl
coh-contraction (pair c C) = left-inv (C c)

ev-pt :
  {l1 l2 : Level} {A : UU l1} (a : A) (B : A → UU l2) → ((x : A) → B x) → B a
ev-pt a B f = f a

is-singleton :
  (l : Level) {i : Level} (A : UU i) → A → UU (lsuc l ⊔ i)
is-singleton l A a = (B : A → UU l) → sec (ev-pt a B)

ind-singleton-is-contr :
  {i j : Level} {A : UU i} (a : A) (is-contr-A : is-contr A) (B : A → UU j) →
  B a → (x : A) → B x
ind-singleton-is-contr a is-contr-A B b x =
  tr B ((inv (contraction is-contr-A a)) ∙ (contraction is-contr-A x)) b

comp-singleton-is-contr :
  {i j : Level} {A : UU i} (a : A) (is-contr-A : is-contr A) (B : A → UU j) →
  ((ev-pt a B) ∘ (ind-singleton-is-contr a is-contr-A B)) ~ id
comp-singleton-is-contr a is-contr-A B b =
  ap (λ ω → tr B ω b) (left-inv (contraction is-contr-A a))

is-contr-ind-singleton :
  {i : Level} (A : UU i) (a : A) →
  ({l : Level} (P : A → UU l) → P a → (x : A) → P x) → is-contr A
is-contr-ind-singleton A a S = pair a (S (λ x → Id a x) refl)

is-contr-is-singleton :
  {i : Level} (A : UU i) (a : A) →
  ({l : Level} → is-singleton l A a) → is-contr A
is-contr-is-singleton A a S = is-contr-ind-singleton A a (λ P → pr1 (S P))

is-singleton-is-contr :
  {l1 l2 : Level} {A : UU l1} (a : A) → is-contr A → is-singleton l2 A a
is-singleton-is-contr a is-contr-A B =
  pair
    ( ind-singleton-is-contr a is-contr-A B)
    ( comp-singleton-is-contr a is-contr-A B)

is-singleton-unit : {l : Level} → is-singleton l unit star
is-singleton-unit B = pair ind-unit (λ b → refl)

is-contr-unit : is-contr unit
is-contr-unit = is-contr-is-singleton unit star (is-singleton-unit)

is-singleton-total-path :
  {i l : Level} (A : UU i) (a : A) →
  is-singleton l (Σ A (λ x → Id a x)) (pair a refl)
is-singleton-total-path A a B = pair (ind-Σ ∘ (ind-Id a _)) (λ b → refl)

is-contr-total-path :
  {i : Level} {A : UU i} (a : A) → is-contr (Σ A (λ x → Id a x))
is-contr-total-path {A = A} a =
  is-contr-is-singleton _ _ (is-singleton-total-path A a)

fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (b : B) → UU (i ⊔ j)
fib f b = Σ _ (λ x → Id (f x) b)

is-contr-map :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
is-contr-map f = (y : _) → is-contr (fib f y)

map-inv-is-contr-map :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-contr-map f → B → A
map-inv-is-contr-map is-contr-f y = pr1 (center (is-contr-f y))

issec-map-inv-is-contr-map :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B}
  (is-contr-f : is-contr-map f) → (f ∘ (map-inv-is-contr-map is-contr-f)) ~ id
issec-map-inv-is-contr-map is-contr-f y = pr2 (center (is-contr-f y))

isretr-map-inv-is-contr-map :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B}
  (is-contr-f : is-contr-map f) → ((map-inv-is-contr-map is-contr-f) ∘ f) ~ id
isretr-map-inv-is-contr-map {_} {_} {A} {B} {f} is-contr-f x =
  ap ( pr1 {B = λ z → Id (f z) (f x)})
     ( ( inv
         ( contraction
           ( is-contr-f (f x))
           ( pair
             ( map-inv-is-contr-map is-contr-f (f x))
             ( issec-map-inv-is-contr-map is-contr-f (f x))))) ∙
       ( contraction (is-contr-f (f x)) (pair x refl)))

is-equiv-is-contr-map :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-contr-map f → is-equiv f
is-equiv-is-contr-map is-contr-f =
  is-equiv-has-inverse
    ( map-inv-is-contr-map is-contr-f)
    ( issec-map-inv-is-contr-map is-contr-f)
    ( isretr-map-inv-is-contr-map is-contr-f)

coherence-is-coherently-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  (G : (f ∘ g) ~ id) (H : (g ∘ f) ~ id) → UU (l1 ⊔ l2)
coherence-is-coherently-invertible f g G H = (G ·r f) ~ (f ·l H)

is-coherently-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → UU (l1 ⊔ l2)
is-coherently-invertible {l1} {l2} {A} {B} f =
  Σ ( B → A)
    ( λ g → Σ ((f ∘ g) ~ id)
      ( λ G → Σ ((g ∘ f) ~ id)
        (λ H → ((G ·r f) ~ (f ·l H)))))

inv-is-coherently-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-coherently-invertible f → B → A
inv-is-coherently-invertible = pr1

issec-inv-is-coherently-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  (H : is-coherently-invertible f) → (f ∘ inv-is-coherently-invertible H) ~ id
issec-inv-is-coherently-invertible H = pr1 (pr2 H)

isretr-inv-is-coherently-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  (H : is-coherently-invertible f) → (inv-is-coherently-invertible H ∘ f) ~ id
isretr-inv-is-coherently-invertible H = pr1 (pr2 (pr2 H))

coh-inv-is-coherently-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  (H : is-coherently-invertible f) →
  coherence-is-coherently-invertible f
    ( inv-is-coherently-invertible H)
    ( issec-inv-is-coherently-invertible H)
    ( isretr-inv-is-coherently-invertible H)
coh-inv-is-coherently-invertible H = pr2 (pr2 (pr2 H))

center-fib-is-coherently-invertible :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-coherently-invertible f → (y : B) → fib f y
center-fib-is-coherently-invertible {i} {j} {A} {B} {f} H y =
  pair
    ( inv-is-coherently-invertible H y)
    ( issec-inv-is-coherently-invertible H y)

Eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  fib f y → fib f y → UU (i ⊔ j)
Eq-fib f y s t =
  Σ (Id (pr1 s) (pr1 t)) (λ α → Id ((ap f α) ∙ (pr2 t)) (pr2 s))

reflexive-Eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  (s : fib f y) → Eq-fib f y s s
reflexive-Eq-fib f y s = pair refl refl

Eq-fib-eq :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  {s t : fib f y} → (Id s t) → Eq-fib f y s t
Eq-fib-eq f y {s} refl = reflexive-Eq-fib f y s

eq-Eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  {s t : fib f y} → Eq-fib f y s t → Id s t
eq-Eq-fib f y {pair x p} {pair .x .p} (pair refl refl) = refl

contraction-fib-is-coherently-invertible :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (H : is-coherently-invertible f) → (y : B) → (t : fib f y) →
  Id (center-fib-is-coherently-invertible H y) t
contraction-fib-is-coherently-invertible {f = f} H y (pair x refl) =
  eq-Eq-fib f y
    ( pair 
      ( isretr-inv-is-coherently-invertible H x)
      ( ( right-unit) ∙
        ( inv ( coh-inv-is-coherently-invertible H x))))

is-contr-map-is-coherently-invertible : 
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-coherently-invertible f → is-contr-map f
is-contr-map-is-coherently-invertible H y =
  pair
    ( center-fib-is-coherently-invertible H y)
    ( contraction-fib-is-coherently-invertible H y)

htpy-nat :
  {i j : Level} {A : UU i} {B : UU j} {f g : A → B} (H : f ~ g)
  {x y : A} (p : Id x y) →
  Id ((H x) ∙ (ap g p)) ((ap f p) ∙ (H y))
htpy-nat H refl = right-unit

left-unwhisk :
  {i : Level} {A : UU i} {x y z : A} (p : Id x y) {q r : Id y z} →
  Id (p ∙ q) (p ∙ r) → Id q r
left-unwhisk refl s = (inv left-unit) ∙ (s ∙ left-unit)

right-unwhisk :
  {i : Level} {A : UU i} {x y z : A} {p q : Id x y}
  (r : Id y z) → Id (p ∙ r) (q ∙ r) → Id p q
right-unwhisk refl s = (inv right-unit) ∙ (s ∙ right-unit)

htpy-red :
  {i : Level} {A : UU i} {f : A → A} (H : f ~ id) →
  (x : A) → Id (H (f x)) (ap f (H x))
htpy-red {_} {A} {f} H x =
  right-unwhisk (H x)
    ( ( ap (concat (H (f x)) x) (inv (ap-id (H x)))) ∙
      ( htpy-nat H (H x)))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : has-inverse f)
  where
  
  inv-has-inverse : B → A
  inv-has-inverse = pr1 H
  
  issec-inv-has-inverse : (f ∘ inv-has-inverse) ~ id
  issec-inv-has-inverse y =
    ( inv (pr1 (pr2 H) (f (inv-has-inverse y)))) ∙
    ( ap f (pr2 (pr2 H) (inv-has-inverse y)) ∙ (pr1 (pr2 H) y))
  
  isretr-inv-has-inverse : (inv-has-inverse ∘ f) ~ id
  isretr-inv-has-inverse = pr2 (pr2 H)
  
  coherence-inv-has-inverse :
    (issec-inv-has-inverse ·r f) ~ (f ·l isretr-inv-has-inverse)
  coherence-inv-has-inverse x =
    inv
      ( inv-con
        ( pr1 (pr2 H) (f (inv-has-inverse (f x))))
        ( ap f (pr2 (pr2 H) x))
        ( (ap f (pr2 (pr2 H) (inv-has-inverse (f x)))) ∙ (pr1 (pr2 H) (f x)))
        ( sq-top-whisk
          ( pr1 (pr2 H) (f (inv-has-inverse (f x))))
          ( ap f (pr2 (pr2 H) x))
          ( (ap (f ∘ (inv-has-inverse ∘ f)) (pr2 (pr2 H) x)))
          ( ( ap-comp f (inv-has-inverse ∘ f) (pr2 (pr2 H) x)) ∙
            ( inv (ap (ap f) (htpy-red (pr2 (pr2 H)) x))))
          ( pr1 (pr2 H) (f x))
          ( htpy-nat (htpy-right-whisk (pr1 (pr2 H)) f) (pr2 (pr2 H) x))))

  is-coherently-invertible-has-inverse : is-coherently-invertible f
  is-coherently-invertible-has-inverse =
    pair
      ( inv-has-inverse)
      ( pair
        ( issec-inv-has-inverse)
        ( pair
          ( isretr-inv-has-inverse)
          ( coherence-inv-has-inverse)))

is-contr-map-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-equiv f → is-contr-map f
is-contr-map-is-equiv =
  is-contr-map-is-coherently-invertible ∘
    ( is-coherently-invertible-has-inverse ∘
      has-inverse-is-equiv)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : is-equiv f)
  where

  issec-map-inv-is-equiv : (f ∘ map-inv-is-equiv H) ~ id
  issec-map-inv-is-equiv = issec-inv-has-inverse (has-inverse-is-equiv H)

  isretr-map-inv-is-equiv : (map-inv-is-equiv H ∘ f) ~ id
  isretr-map-inv-is-equiv =
    isretr-inv-has-inverse (has-inverse-is-equiv H)
  
  coherence-map-inv-is-equiv :
    ( issec-map-inv-is-equiv ·r f) ~ (f ·l isretr-map-inv-is-equiv)
  coherence-map-inv-is-equiv =
    coherence-inv-has-inverse (has-inverse-is-equiv H)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  map-inv-equiv : B → A
  map-inv-equiv = map-inv-is-equiv (is-equiv-map-equiv e)

  issec-map-inv-equiv : ((map-equiv e) ∘ map-inv-equiv) ~ id
  issec-map-inv-equiv = issec-map-inv-is-equiv (is-equiv-map-equiv e)

  isretr-map-inv-equiv : (map-inv-equiv ∘ (map-equiv e)) ~ id
  isretr-map-inv-equiv =
    isretr-map-inv-is-equiv (is-equiv-map-equiv e)
  
  coherence-map-inv-equiv :
    ( issec-map-inv-equiv ·r (map-equiv e)) ~
    ( (map-equiv e) ·l isretr-map-inv-equiv)
  coherence-map-inv-equiv =
    coherence-map-inv-is-equiv (is-equiv-map-equiv e)

is-contr-is-equiv-const :
  {i : Level} {A : UU i} → is-equiv (terminal-map {A = A}) → is-contr A
is-contr-is-equiv-const (pair (pair g issec) (pair h isretr)) =
  pair (h star) isretr

is-equiv-terminal-map-is-contr :
  {i : Level} {A : UU i} → is-contr A → is-equiv (terminal-map {A = A})
is-equiv-terminal-map-is-contr {i} {A} is-contr-A =
  pair
    ( pair (ind-unit (center is-contr-A)) (ind-unit refl))
    ( pair (const unit A (center is-contr-A)) (contraction is-contr-A))

is-contr-is-equiv :
  {i j : Level} {A : UU i} (B : UU j) (f : A → B) →
  is-equiv f → is-contr B → is-contr A
is-contr-is-equiv B f is-equiv-f is-contr-B =
  is-contr-is-equiv-const
    ( is-equiv-comp'
      ( terminal-map)
      ( f)
      ( is-equiv-f)
      ( is-equiv-terminal-map-is-contr is-contr-B))

is-contr-is-equiv' :
  {i j : Level} (A : UU i) {B : UU j} (f : A → B) →
  is-equiv f → is-contr A → is-contr B
is-contr-is-equiv' A f is-equiv-f is-contr-A =
  is-contr-is-equiv A
    ( map-inv-is-equiv is-equiv-f)
    ( is-equiv-map-inv-is-equiv is-equiv-f)
    ( is-contr-A)

is-equiv-is-contr :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
  is-contr A → is-contr B → is-equiv f
is-equiv-is-contr {i} {j} {A} {B} f is-contr-A is-contr-B =
  is-equiv-has-inverse
    ( const B A (center is-contr-A))
    ( ind-singleton-is-contr _ is-contr-B _
      ( inv (contraction is-contr-B (f (center is-contr-A)))))
    ( contraction is-contr-A)

equiv-is-contr :
  {i j : Level} {A : UU i} {B : UU j} →
  is-contr A → is-contr B → A ≃ B
equiv-is-contr is-contr-A is-contr-B =
  pair
    ( λ a → center is-contr-B)
    ( is-equiv-is-contr _ is-contr-A is-contr-B)
    
is-contr-equiv :
  {i j : Level} {A : UU i} (B : UU j) (e : A ≃ B) → is-contr B → is-contr A
is-contr-equiv B (pair e is-equiv-e) is-contr-B =
  is-contr-is-equiv B e is-equiv-e is-contr-B

is-contr-equiv' :
  {i j : Level} (A : UU i) {B : UU j} (e : A ≃ B) → is-contr A → is-contr B
is-contr-equiv' A (pair e is-equiv-e) is-contr-A =
  is-contr-is-equiv' A e is-equiv-e is-contr-A

contraction-is-prop-is-contr :
  {i : Level} {A : UU i} (H : is-contr A) {x y : A} →
  (p : Id x y) → Id (eq-is-contr H) p
contraction-is-prop-is-contr (pair c C) {x} refl = left-inv (C x)

is-prop-is-contr : {i : Level} {A : UU i} → is-contr A →
  (x y : A) → is-contr (Id x y)
is-prop-is-contr {i} {A} is-contr-A x y =
  pair
    ( eq-is-contr is-contr-A)
    ( contraction-is-prop-is-contr is-contr-A)

is-contr-raise-unit :
  {l1 : Level} → is-contr (raise-unit l1)
is-contr-raise-unit {l1} =
  is-contr-equiv' unit (equiv-raise l1 unit) is-contr-unit

map-fib-pr1 :
  {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
  fib (pr1 {B = B}) a → B a
map-fib-pr1 B a (pair (pair x y) p) = tr B p y

map-inv-fib-pr1 :
  {i j : Level} {A : UU i} (B : A → UU j)
  (a : A) → B a → fib (pr1 {B = B}) a
map-inv-fib-pr1 B a b = pair (pair a b) refl

issec-map-inv-fib-pr1 :
  {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
  ((map-inv-fib-pr1 B a) ∘ (map-fib-pr1 B a)) ~ id
issec-map-inv-fib-pr1 B a (pair (pair .a y) refl) = refl

isretr-map-inv-fib-pr1 :
  {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
  ((map-fib-pr1 B a) ∘ (map-inv-fib-pr1 B a)) ~ id
isretr-map-inv-fib-pr1 B a b = refl

is-equiv-map-fib-pr1 :
  {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
  is-equiv (map-fib-pr1 B a)
is-equiv-map-fib-pr1 B a =
  is-equiv-has-inverse
    ( map-inv-fib-pr1 B a)
    ( isretr-map-inv-fib-pr1 B a)
    ( issec-map-inv-fib-pr1 B a)

equiv-fib-pr1 :
  {i j : Level} {A : UU i} {B : A → UU j} (a : A) → fib (pr1 {B = B}) a ≃ B a
equiv-fib-pr1 {B = B} a =
  pair (map-fib-pr1 B a) (is-equiv-map-fib-pr1 B a)

map-equiv-total-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → (Σ B (fib f)) → A
map-equiv-total-fib f t = pr1 (pr2 t)

triangle-map-equiv-total-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
  pr1 ~ (f ∘ (map-equiv-total-fib f))
triangle-map-equiv-total-fib f t = inv (pr2 (pr2 t))

map-inv-equiv-total-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → A → Σ B (fib f)
map-inv-equiv-total-fib f x = pair (f x) (pair x refl)

isretr-map-inv-equiv-total-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
  ((map-inv-equiv-total-fib f) ∘ (map-equiv-total-fib f)) ~ id
isretr-map-inv-equiv-total-fib f (pair .(f x) (pair x refl)) = refl

issec-map-inv-equiv-total-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
  ((map-equiv-total-fib f) ∘ (map-inv-equiv-total-fib f)) ~ id
issec-map-inv-equiv-total-fib f x = refl

is-equiv-map-equiv-total-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
  is-equiv (map-equiv-total-fib f)
is-equiv-map-equiv-total-fib f =
  is-equiv-has-inverse
    ( map-inv-equiv-total-fib f)
    ( issec-map-inv-equiv-total-fib f)
    ( isretr-map-inv-equiv-total-fib f)

is-equiv-map-inv-equiv-total-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
  is-equiv (map-inv-equiv-total-fib f)
is-equiv-map-inv-equiv-total-fib f =
  is-equiv-has-inverse
    ( map-equiv-total-fib f)
    ( isretr-map-inv-equiv-total-fib f)
    ( issec-map-inv-equiv-total-fib f)

equiv-total-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B ) → Σ B (fib f) ≃ A
equiv-total-fib f =
  pair (map-equiv-total-fib f) (is-equiv-map-equiv-total-fib f)

inv-equiv-total-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → A ≃ Σ B (fib f)
inv-equiv-total-fib f =
  pair (map-inv-equiv-total-fib f) (is-equiv-map-inv-equiv-total-fib f)

is-equiv-pr1-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  ((a : A) → is-contr (B a)) → is-equiv (pr1 {B = B})
is-equiv-pr1-is-contr {B = B} is-contr-B =
  is-equiv-is-contr-map
    ( λ x → is-contr-equiv
      ( B x)
      ( equiv-fib-pr1 x)
      ( is-contr-B x))

equiv-pr1 :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  ((a : A) → is-contr (B a)) → (Σ A B) ≃ A
equiv-pr1 is-contr-B = pair pr1 (is-equiv-pr1-is-contr is-contr-B)

right-unit-law-Σ-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  ((a : A) → is-contr (B a)) → (Σ A B) ≃ A
right-unit-law-Σ-is-contr = equiv-pr1

right-unit-law-prod-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-contr B → (A × B) ≃ A
right-unit-law-prod-is-contr {l1} {l2} {A} {B} H =
  right-unit-law-Σ-is-contr (λ a → H)

is-contr-is-equiv-pr1 :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (is-equiv (pr1 {B = B})) → ((a : A) → is-contr (B a))
is-contr-is-equiv-pr1 {B = B} is-equiv-pr1-B a =
  is-contr-equiv'
    ( fib pr1 a)
    ( equiv-fib-pr1 a)
    ( is-contr-map-is-equiv is-equiv-pr1-B a)
      
is-equiv-map-inv-fib-pr1 :
  {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
  is-equiv (map-inv-fib-pr1 B a)
is-equiv-map-inv-fib-pr1 B a =
  is-equiv-has-inverse
    ( map-fib-pr1 B a)
    ( issec-map-inv-fib-pr1 B a)
    ( isretr-map-inv-fib-pr1 B a)

inv-equiv-fib-pr1 :
  {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
  B a ≃ fib (pr1 {B = B}) a
inv-equiv-fib-pr1 B a =
  pair (map-inv-fib-pr1 B a) (is-equiv-map-inv-fib-pr1 B a)

map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  ((x : A) → B x) → (A → Σ A B)
map-section b a = pair a (b a)

htpy-map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  (pr1 ∘ map-section b) ~ id
htpy-map-section b a = refl

is-equiv-map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  ((x : A) → is-contr (B x)) → is-equiv (map-section b)
is-equiv-map-section b C =
  is-equiv-right-factor
    ( id)
    ( pr1)
    ( map-section b)
    ( htpy-map-section b)
    ( is-equiv-pr1-is-contr C)
    ( is-equiv-id)

equiv-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  ((x : A) → is-contr (B x)) → A ≃ Σ A B
equiv-section b C = pair (map-section b) (is-equiv-map-section b C)

is-contr-fam-is-equiv-map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  is-equiv (map-section b) → ((x : A) → is-contr (B x))
is-contr-fam-is-equiv-map-section b H =
  is-contr-is-equiv-pr1
    ( is-equiv-left-factor id pr1
      ( map-section b)
      ( htpy-map-section b)
      ( is-equiv-id)
      ( H))

--------------------------------------------------------------------------------

-- The fundamental theorem of identity types

tot :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  ((x : A) → B x → C x) → ( Σ A B → Σ A C)
tot f t = pair (pr1 t) (f (pr1 t) (pr2 t))

tot-htpy :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k}
  {f g : (x : A) → B x → C x} → (H : (x : A) → f x ~ g x) → tot f ~ tot g
tot-htpy H (pair x y) = eq-pair-Σ refl (H x y)

tot-id :
  {i j : Level} {A : UU i} (B : A → UU j) →
  (tot (λ x (y : B x) → y)) ~ id
tot-id B (pair x y) = refl

tot-comp :
  {i j j' j'' : Level}
  {A : UU i} {B : A → UU j} {B' : A → UU j'} {B'' : A → UU j''}
  (f : (x : A) → B x → B' x) (g : (x : A) → B' x → B'' x) →
  tot (λ x → (g x) ∘ (f x)) ~ ((tot g) ∘ (tot f))
tot-comp f g (pair x y) = refl

fib-ftr-fib-tot :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → (t : Σ A C) →
  fib (tot f) t → fib (f (pr1 t)) (pr2 t)
fib-ftr-fib-tot f .(pair x (f x y)) (pair (pair x y) refl) = pair y refl

fib-tot-fib-ftr :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → (t : Σ A C) →
  fib (f (pr1 t)) (pr2 t) → fib (tot f) t
fib-tot-fib-ftr F (pair a .(F a y)) (pair y refl) = pair (pair a y) refl

issec-fib-tot-fib-ftr :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → (t : Σ A C) →
  ((fib-ftr-fib-tot f t) ∘ (fib-tot-fib-ftr f t)) ~ id
issec-fib-tot-fib-ftr f (pair x .(f x y)) (pair y refl) = refl

isretr-fib-tot-fib-ftr :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → (t : Σ A C) →
  ((fib-tot-fib-ftr f t) ∘ (fib-ftr-fib-tot f t)) ~ id
isretr-fib-tot-fib-ftr f .(pair x (f x y)) (pair (pair x y) refl) = refl

is-equiv-fib-ftr-fib-tot :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → (t : Σ A C) →
  is-equiv (fib-ftr-fib-tot f t)
is-equiv-fib-ftr-fib-tot f t =
  is-equiv-has-inverse
    ( fib-tot-fib-ftr f t)
    ( issec-fib-tot-fib-ftr f t)
    ( isretr-fib-tot-fib-ftr f t)

is-equiv-fib-tot-fib-ftr :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → (t : Σ A C) →
  is-equiv (fib-tot-fib-ftr f t)
is-equiv-fib-tot-fib-ftr f t =
  is-equiv-has-inverse
    ( fib-ftr-fib-tot f t)
    ( isretr-fib-tot-fib-ftr f t)
    ( issec-fib-tot-fib-ftr f t)

is-fiberwise-equiv :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  ((x : A) → B x → C x) → UU (i ⊔ (j ⊔ k))
is-fiberwise-equiv f = (x : _) → is-equiv (f x)

is-equiv-tot-is-fiberwise-equiv :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  {f : (x : A) → B x → C x} → is-fiberwise-equiv f →
  is-equiv (tot f )
is-equiv-tot-is-fiberwise-equiv {f = f} H =
  is-equiv-is-contr-map
    ( λ t → is-contr-is-equiv _
      ( fib-ftr-fib-tot f t)
      ( is-equiv-fib-ftr-fib-tot f t)
      ( is-contr-map-is-equiv (H _) (pr2 t)))

is-fiberwise-equiv-is-equiv-tot :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → is-equiv (tot f) →
  is-fiberwise-equiv f
is-fiberwise-equiv-is-equiv-tot {A = A} {B} {C} f is-equiv-tot-f x =
  is-equiv-is-contr-map
    ( λ z → is-contr-is-equiv'
      ( fib (tot f) (pair x z))
      ( fib-ftr-fib-tot f (pair x z))
      ( is-equiv-fib-ftr-fib-tot f (pair x z))
      ( is-contr-map-is-equiv is-equiv-tot-f (pair x z)))

equiv-tot :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  ((x : A) → B x ≃ C x) → (Σ A B) ≃ (Σ A C)
equiv-tot e =
  pair
    ( tot (λ x → map-equiv (e x)))
    ( is-equiv-tot-is-fiberwise-equiv (λ x → is-equiv-map-equiv (e x)))

fundamental-theorem-id :
  {i j : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
  is-contr (Σ A B) → (f : (x : A) → Id a x → B x) → is-fiberwise-equiv f
fundamental-theorem-id {A = A} a b is-contr-AB f =
  is-fiberwise-equiv-is-equiv-tot f
    ( is-equiv-is-contr (tot f) (is-contr-total-path a) is-contr-AB)

fundamental-theorem-id' :
  {i j : Level} {A : UU i} {B : A → UU j}
  (a : A) (b : B a) (f : (x : A) → Id a x → B x) →
  is-fiberwise-equiv f → is-contr (Σ A B)
fundamental-theorem-id' {A = A} {B = B} a b f is-fiberwise-equiv-f =
  is-contr-is-equiv'
    ( Σ A (Id a))
    ( tot f)
    ( is-equiv-tot-is-fiberwise-equiv is-fiberwise-equiv-f)
    ( is-contr-total-path a)

is-emb :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
is-emb f = (x y : _) → is-equiv (ap f {x} {y})

_↪_ :
  {i j : Level} → UU i → UU j → UU (i ⊔ j)
A ↪ B = Σ (A → B) is-emb

map-emb :
  {i j : Level} {A : UU i} {B : UU j} → A ↪ B → A → B
map-emb f = pr1 f

is-emb-map-emb :
  { i j : Level} {A : UU i} {B : UU j} (f : A ↪ B) → is-emb (map-emb f)
is-emb-map-emb f = pr2 f

equiv-ap-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ↪ B) {x y : A} →
  Id x y ≃ Id (map-emb e x) (map-emb e y)
equiv-ap-emb e {x} {y} = pair (ap (map-emb e)) (is-emb-map-emb e x y)

is-injective-is-emb : {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-emb f → is-injective f
is-injective-is-emb is-emb-f {x} {y} = map-inv-is-equiv (is-emb-f x y)

is-injective-emb :
  {i j : Level} {A : UU i} {B : UU j} (e : A ↪ B) → is-injective (map-emb e)
is-injective-emb e {x} {y} = map-inv-is-equiv (is-emb-map-emb e x y)

is-emb-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} → is-equiv f → is-emb f
is-emb-is-equiv {i} {j} {A} {B} {f} is-equiv-f x =
  fundamental-theorem-id x refl
    ( is-contr-equiv
      ( fib f (f x))
      ( equiv-tot (λ y → equiv-inv (f x) (f y)))
      ( is-contr-map-is-equiv is-equiv-f (f x)))
    ( λ y p → ap f p)

emb-equiv :
  {i j : Level} {A : UU i} {B : UU j} → (A ≃ B) → (A ↪ B)
emb-equiv e =
  pair (map-equiv e) (is-emb-is-equiv (is-equiv-map-equiv e))

emb-id :
  {i : Level} {A : UU i} → (A ↪ A)
emb-id {i} {A} = emb-equiv equiv-id

is-emb-id : {l : Level} {A : UU l} → is-emb (id {A = A})
is-emb-id = is-emb-map-emb emb-id

equiv-ap :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) (x y : A) →
  (Id x y) ≃ (Id (map-equiv e x) (map-equiv e y))
equiv-ap e x y =
  pair
    ( ap (map-equiv e) {x} {y})
    ( is-emb-is-equiv (is-equiv-map-equiv e) x y)

is-contr-retract-of : {i j : Level} {A : UU i} (B : UU j) →
  A retract-of B → is-contr B → is-contr A
is-contr-retract-of B (pair i (pair r isretr)) is-contr-B =
  pair
    ( r (center is-contr-B))
    ( λ x → (ap r (contraction is-contr-B (i x))) ∙ (isretr x))

is-contr-left-factor-prod :
  {i j : Level} (A : UU i) (B : UU j) → is-contr (A × B) → is-contr A
is-contr-left-factor-prod A B is-contr-AB =
  is-contr-retract-of
    ( A × B)
    ( pair
      ( λ x → pair x (pr2 (center is-contr-AB)))
      ( pair pr1 (λ x → refl)))
    ( is-contr-AB)

is-contr-right-factor-prod :
  {i j : Level} (A : UU i) (B : UU j) → is-contr (A × B) → is-contr B
is-contr-right-factor-prod A B is-contr-AB =
  is-contr-left-factor-prod B A
    ( is-contr-equiv
      ( A × B)
      ( equiv-swap-prod B A)
      ( is-contr-AB))

is-contr-prod :
  {i j : Level} {A : UU i} {B : UU j} →
  is-contr A → is-contr B → is-contr (A × B)
is-contr-prod {A = A} {B = B} (pair a C) (pair b D) =
  pair (pair a b) α
  where
  α : (z : A × B) → Id (pair a b) z
  α (pair x y) = eq-pair (C x) (D y)

map-inv-left-unit-law-Σ-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-contr A → (a : A) →
  B a → Σ A B
map-inv-left-unit-law-Σ-is-contr C a = pair a

map-left-unit-law-Σ-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-contr A → (a : A) →
  Σ A B → B a
map-left-unit-law-Σ-is-contr {B = B} C a =
  ind-Σ
    ( ind-singleton-is-contr a C
      ( λ x → B x → B a)
      ( id))

issec-map-inv-left-unit-law-Σ-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (C : is-contr A) (a : A) →
  ( ( map-left-unit-law-Σ-is-contr {B = B} C a) ∘
    ( map-inv-left-unit-law-Σ-is-contr {B = B} C a)) ~ id
issec-map-inv-left-unit-law-Σ-is-contr {B = B} C a b =
  ap ( λ (f : B a → B a) → f b)
     ( comp-singleton-is-contr a C (λ x → B x → B a) id)

isretr-map-inv-left-unit-law-Σ-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (C : is-contr A) (a : A) →
  ( ( map-inv-left-unit-law-Σ-is-contr {B = B} C a) ∘
    ( map-left-unit-law-Σ-is-contr {B = B} C a)) ~ id
isretr-map-inv-left-unit-law-Σ-is-contr {B = B} C a = 
  ind-Σ
    ( ind-singleton-is-contr a C
      ( λ x → (y : B x) →
        Id ( ( ( map-inv-left-unit-law-Σ-is-contr C a) ∘
               ( map-left-unit-law-Σ-is-contr C a))
             ( pair x y))
           ( id (pair x y)))
      ( λ y → ap
        ( map-inv-left-unit-law-Σ-is-contr C a)
        ( ap ( λ f → f y)
             ( comp-singleton-is-contr a C (λ x → B x → B a) id))))

is-equiv-map-left-unit-law-Σ-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (C : is-contr A) (a : A) →
  is-equiv (map-left-unit-law-Σ-is-contr {B = B} C a)
is-equiv-map-left-unit-law-Σ-is-contr C a =
  is-equiv-has-inverse
    ( map-inv-left-unit-law-Σ-is-contr C a)
    ( issec-map-inv-left-unit-law-Σ-is-contr C a)
    ( isretr-map-inv-left-unit-law-Σ-is-contr C a)

left-unit-law-Σ-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (C : is-contr A) (a : A) →
  Σ A B ≃ B a
left-unit-law-Σ-is-contr C a =
  pair
    ( map-left-unit-law-Σ-is-contr C a)
    ( is-equiv-map-left-unit-law-Σ-is-contr C a)

left-unit-law-prod-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (C : is-contr A) → (A × B) ≃ B
left-unit-law-prod-is-contr C =
  left-unit-law-Σ-is-contr C (center C)

is-equiv-map-inv-left-unit-law-Σ-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (C : is-contr A) (a : A) →
  is-equiv (map-inv-left-unit-law-Σ-is-contr {B = B} C a)
is-equiv-map-inv-left-unit-law-Σ-is-contr C a =
  is-equiv-has-inverse
    ( map-left-unit-law-Σ-is-contr C a)
    ( isretr-map-inv-left-unit-law-Σ-is-contr C a)
    ( issec-map-inv-left-unit-law-Σ-is-contr C a)

inv-left-unit-law-Σ-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (C : is-contr A) (a : A) →
  B a ≃ Σ A B
inv-left-unit-law-Σ-is-contr C a =
  pair
    ( map-inv-left-unit-law-Σ-is-contr C a)
    ( is-equiv-map-inv-left-unit-law-Σ-is-contr C a)

is-path-split :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-path-split {A = A} {B = B} f =
  sec f × ((x y : A) → sec (ap f {x = x} {y = y}))

is-path-split-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-equiv f → is-path-split f
is-path-split-is-equiv f is-equiv-f =
  pair (pr1 is-equiv-f) (λ x y → pr1 (is-emb-is-equiv is-equiv-f x y))

is-coherently-invertible-is-path-split :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-path-split f → is-coherently-invertible f
is-coherently-invertible-is-path-split {A = A} {B = B} f
  ( pair (pair g issec-g) sec-ap-f) =
  let φ : ((x : A) → fib (ap f) (issec-g (f x))) →
              Σ ((g ∘ f) ~ id)
              ( λ H → (htpy-right-whisk issec-g f) ~ (htpy-left-whisk f H))
      φ =  ( tot (λ H' → inv-htpy)) ∘
             ( λ s → pair (λ x → pr1 (s x)) (λ x → pr2 (s x)))
  in
  pair g
    ( pair issec-g
      ( φ (λ x → pair
        ( pr1 (sec-ap-f (g (f x)) x) (issec-g (f x)))
        ( pr2 (sec-ap-f (g (f x)) x) (issec-g (f x))))))

is-equiv-is-coherently-invertible :
  { l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) → is-coherently-invertible f → is-equiv f
is-equiv-is-coherently-invertible f (pair g (pair G (pair H K))) =
  is-equiv-has-inverse g G H

is-equiv-is-path-split :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-path-split f → is-equiv f
is-equiv-is-path-split f =
  ( is-equiv-is-coherently-invertible f) ∘
  ( is-coherently-invertible-is-path-split f)

is-coherently-invertible-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-equiv f → is-coherently-invertible f
is-coherently-invertible-is-equiv f =
  ( is-coherently-invertible-is-path-split f) ∘ (is-path-split-is-equiv f)

swap-total-Eq-structure :
  {l1 l2 l3 l4 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3)
  (D : (x : A) → B x → C x → UU l4) →
  Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t))) →
  Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t)))
swap-total-Eq-structure B C D (pair (pair a b) (pair c d)) =
  pair (pair a c) (pair b d)

htpy-swap-total-Eq-structure :
  {l1 l2 l3 l4 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3)
  (D : (x : A) → B x → C x → UU l4) →
  ( ( swap-total-Eq-structure B C D) ∘
    ( swap-total-Eq-structure C B (λ x z y → D x y z))) ~ id
htpy-swap-total-Eq-structure B C D (pair (pair a b) (pair c d)) = refl

is-equiv-swap-total-Eq-structure :
  {l1 l2 l3 l4 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3)
  (D : (x : A) → B x → C x → UU l4) →
  is-equiv (swap-total-Eq-structure B C D)
is-equiv-swap-total-Eq-structure B C D =
  is-equiv-has-inverse
    ( swap-total-Eq-structure C B (λ x z y → D x y z))
    ( htpy-swap-total-Eq-structure B C D)
    ( htpy-swap-total-Eq-structure C B (λ x z y → D x y z))

is-contr-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-contr A → ((x : A) → is-contr (B x)) → is-contr (Σ A B)
is-contr-Σ {A = A} {B = B} is-contr-A is-contr-B =
  is-contr-equiv
    ( B (center is-contr-A))
    ( left-unit-law-Σ-is-contr is-contr-A (center is-contr-A))
    ( is-contr-B (center is-contr-A))

is-contr-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-contr A → (a : A) → is-contr (B a) → is-contr (Σ A B)
is-contr-Σ' {A = A} {B} is-contr-A a is-contr-B =
  is-contr-equiv
    ( B a)
    ( left-unit-law-Σ-is-contr is-contr-A a)
    ( is-contr-B)

is-contr-total-Eq-structure :
  { l1 l2 l3 l4 : Level} { A : UU l1} {B : A → UU l2} {C : A → UU l3}
  ( D : (x : A) → B x → C x → UU l4) →
  ( is-contr-AC : is-contr (Σ A C)) →
  ( t : Σ A C) →
  is-contr (Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t))) →
  is-contr (Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t))))
is-contr-total-Eq-structure
  {A = A} {B = B} {C = C} D is-contr-AC t is-contr-BD =
  is-contr-is-equiv
    ( Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t))))
    ( swap-total-Eq-structure B C D)
    ( is-equiv-swap-total-Eq-structure B C D)
    ( is-contr-Σ' is-contr-AC t is-contr-BD)

IND-identity-system :
  {i j : Level} (k : Level) {A : UU i} (B : A → UU j) (a : A) (b : B a) → UU _
IND-identity-system k {A} B a b =
  ( P : (x : A) (y : B x) → UU k) →
    sec (λ (h : (x : A) (y : B x) → P x y) → h a b)

fam-Σ :
  {i j k : Level} {A : UU i} {B : A → UU j} (C : (x : A) → B x → UU k) →
  Σ A B → UU k
fam-Σ C (pair x y) = C x y

ind-identity-system :
  {i j k : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
  (is-contr-AB : is-contr (Σ A B)) (P : (x : A) → B x → UU k) →
  P a b → (x : A) (y : B x) → P x y
ind-identity-system a b is-contr-AB P p x y =
  tr ( fam-Σ P)
     ( eq-is-contr is-contr-AB)
     ( p)

comp-identity-system :
  {i j k : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
  (is-contr-AB : is-contr (Σ A B)) →
  (P : (x : A) → B x → UU k) (p : P a b) →
  Id (ind-identity-system a b is-contr-AB P p a b) p
comp-identity-system a b is-contr-AB P p =
  ap ( λ t → tr (fam-Σ P) t p)
     ( eq-is-contr'
       ( is-prop-is-contr is-contr-AB (pair a b) (pair a b))
       ( eq-is-contr is-contr-AB)
       ( refl))

Ind-identity-system :
  {i j : Level} (k : Level) {A : UU i} {B : A → UU j} (a : A) (b : B a) →
  (is-contr-AB : is-contr (Σ A B)) →
  IND-identity-system k B a b
Ind-identity-system k a b is-contr-AB P =
  pair
    ( ind-identity-system a b is-contr-AB P)
    ( comp-identity-system a b is-contr-AB P)

is-contr-total-Eq-coprod-inl :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (x : A) →
  is-contr (Σ (coprod A B) (Eq-coprod A B (inl x)))
is-contr-total-Eq-coprod-inl A B x =
  is-contr-equiv
    ( coprod
      ( Σ A (λ y → Eq-coprod A B (inl x) (inl y)))
      ( Σ B (λ y → Eq-coprod A B (inl x) (inr y))))
    ( right-distributive-Σ-coprod A B (Eq-coprod A B (inl x)))
    ( is-contr-equiv'
      ( coprod
        ( Σ A (Id x))
        ( Σ B (λ y → empty)))
      ( equiv-coprod
        ( equiv-tot (λ y → equiv-raise _ (Id x y)))
        ( equiv-tot (λ y → equiv-raise _ empty)))
      ( is-contr-equiv
        ( coprod (Σ A (Id x)) empty)
        ( equiv-coprod equiv-id (right-absorption-Σ B))
        ( is-contr-equiv'
          ( Σ A (Id x))
          ( inv-right-unit-law-coprod (Σ A (Id x)))
          ( is-contr-total-path x))))

is-contr-total-Eq-coprod-inr :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (x : B) →
  is-contr (Σ (coprod A B) (Eq-coprod A B (inr x)))
is-contr-total-Eq-coprod-inr A B x =
  is-contr-equiv
    ( coprod
      ( Σ A (λ y → Eq-coprod A B (inr x) (inl y)))
      ( Σ B (λ y → Eq-coprod A B (inr x) (inr y))))
    ( right-distributive-Σ-coprod A B (Eq-coprod A B (inr x)))
    ( is-contr-equiv'
      ( coprod (Σ A (λ y → empty)) (Σ B (Id x)))
      ( equiv-coprod
        ( equiv-tot (λ y → equiv-raise _ empty))
        ( equiv-tot (λ y → equiv-raise _ (Id x y))))
      ( is-contr-equiv
        ( coprod empty (Σ B (Id x)))
        ( equiv-coprod (right-absorption-Σ A) equiv-id)
        ( is-contr-equiv'
          ( Σ B (Id x))
          ( inv-left-unit-law-coprod (Σ B (Id x)))
          ( is-contr-total-path x))))

is-equiv-Eq-eq-coprod-inl :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (x : A) →
  is-fiberwise-equiv (Eq-eq-coprod A B (inl x))
is-equiv-Eq-eq-coprod-inl A B x =
  fundamental-theorem-id
    ( inl x)
    ( reflexive-Eq-coprod A B (inl x))
    ( is-contr-total-Eq-coprod-inl A B x)
    ( Eq-eq-coprod A B (inl x))

is-equiv-Eq-eq-coprod-inr :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (x : B) →
  is-fiberwise-equiv (Eq-eq-coprod A B (inr x))
is-equiv-Eq-eq-coprod-inr A B x =
  fundamental-theorem-id
    ( inr x)
    ( reflexive-Eq-coprod A B (inr x))
    ( is-contr-total-Eq-coprod-inr A B x)
    ( Eq-eq-coprod A B (inr x))

is-equiv-Eq-eq-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  (s : coprod A B) → is-fiberwise-equiv (Eq-eq-coprod A B s)
is-equiv-Eq-eq-coprod A B (inl x) = is-equiv-Eq-eq-coprod-inl A B x
is-equiv-Eq-eq-coprod A B (inr x) = is-equiv-Eq-eq-coprod-inr A B x

equiv-Eq-eq-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (x y : coprod A B) →
  Id x y ≃ Eq-coprod A B x y
equiv-Eq-eq-coprod A B x y =
  pair (Eq-eq-coprod A B x y) (is-equiv-Eq-eq-coprod A B x y)

map-compute-eq-coprod-inl-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (x x' : A) → Id (inl {B = B} x) (inl {B = B} x') → Id x x'
map-compute-eq-coprod-inl-inl x x' =
  ( map-inv-is-equiv (is-equiv-map-raise _ (Id x x'))) ∘
    ( Eq-eq-coprod _ _ (inl x) (inl x')) 

is-equiv-map-compute-eq-coprod-inl-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (x x' : A) → is-equiv (map-compute-eq-coprod-inl-inl {B = B} x x')
is-equiv-map-compute-eq-coprod-inl-inl x x' =
  is-equiv-comp
    ( map-compute-eq-coprod-inl-inl x x')
    ( map-inv-is-equiv (is-equiv-map-raise _ (Id x x')))
    ( Eq-eq-coprod _ _ (inl x) (inl x'))
    ( refl-htpy)
    ( is-equiv-Eq-eq-coprod _ _ (inl x) (inl x'))
    ( is-equiv-map-inv-is-equiv (is-equiv-map-raise _ (Id x x')))

compute-eq-coprod-inl-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (x x' : A) → (Id (inl {B = B} x) (inl x')) ≃ (Id x x')
compute-eq-coprod-inl-inl x x' =
  pair
    ( map-compute-eq-coprod-inl-inl x x')
    ( is-equiv-map-compute-eq-coprod-inl-inl x x')

map-compute-eq-coprod-inl-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (x : A) (y' : B) → Id (inl x) (inr y') → empty
map-compute-eq-coprod-inl-inr x y' =
  ( map-inv-is-equiv (is-equiv-map-raise _ empty)) ∘
    ( Eq-eq-coprod _ _ (inl x) (inr y'))

is-equiv-map-compute-eq-coprod-inl-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (x : A) (y' : B) → is-equiv (map-compute-eq-coprod-inl-inr x y')
is-equiv-map-compute-eq-coprod-inl-inr x y' =
  is-equiv-comp
    ( map-compute-eq-coprod-inl-inr x y')
    ( map-inv-is-equiv (is-equiv-map-raise _ empty))
    ( Eq-eq-coprod _ _ (inl x) (inr y'))
    ( refl-htpy)
    ( is-equiv-Eq-eq-coprod _ _ (inl x) (inr y'))
    ( is-equiv-map-inv-is-equiv (is-equiv-map-raise _ empty))
  
compute-eq-coprod-inl-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (x : A) (y' : B) → (Id (inl x) (inr y')) ≃ empty
compute-eq-coprod-inl-inr x y' =
  pair
    ( map-compute-eq-coprod-inl-inr x y')
    ( is-equiv-map-compute-eq-coprod-inl-inr x y')

map-compute-eq-coprod-inr-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (y : B) (x' : A) → (Id (inr {A = A} y) (inl x')) → empty
map-compute-eq-coprod-inr-inl y x' =
   ( map-inv-is-equiv (is-equiv-map-raise _ empty)) ∘
     ( Eq-eq-coprod _ _ (inr y) (inl x'))

is-equiv-map-compute-eq-coprod-inr-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (y : B) (x' : A) → is-equiv (map-compute-eq-coprod-inr-inl y x')
is-equiv-map-compute-eq-coprod-inr-inl y x' =
  is-equiv-comp
    ( map-compute-eq-coprod-inr-inl y x')
    ( map-inv-is-equiv (is-equiv-map-raise _ empty))
    ( Eq-eq-coprod _ _ (inr y) (inl x'))
    ( refl-htpy)
    ( is-equiv-Eq-eq-coprod _ _ (inr y) (inl x'))
    ( is-equiv-map-inv-is-equiv (is-equiv-map-raise _ empty))

compute-eq-coprod-inr-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (y : B) (x' : A) → (Id (inr y) (inl x')) ≃ empty
compute-eq-coprod-inr-inl y x' =
  pair
    ( map-compute-eq-coprod-inr-inl y x')
    ( is-equiv-map-compute-eq-coprod-inr-inl y x')

map-compute-eq-coprod-inr-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (y y' : B) → (Id (inr {A = A} y) (inr y')) → Id y y'
map-compute-eq-coprod-inr-inr y y' =
  ( map-inv-is-equiv (is-equiv-map-raise _ (Id y y'))) ∘
    ( Eq-eq-coprod _ _ (inr y) (inr y'))

is-equiv-map-compute-eq-coprod-inr-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (y y' : B) → is-equiv (map-compute-eq-coprod-inr-inr {A = A} y y')
is-equiv-map-compute-eq-coprod-inr-inr y y' =
  is-equiv-comp
    ( map-compute-eq-coprod-inr-inr y y')
    ( map-inv-is-equiv (is-equiv-map-raise _ (Id y y')))
    ( Eq-eq-coprod _ _ (inr y) (inr y'))
    ( refl-htpy)
    ( is-equiv-Eq-eq-coprod _ _ (inr y) (inr y'))
    ( is-equiv-map-inv-is-equiv (is-equiv-map-raise _ (Id y y')))

compute-eq-coprod-inr-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (y y' : B) → (Id (inr {A = A} y) (inr y')) ≃ (Id y y')
compute-eq-coprod-inr-inr y y' =
  pair
    ( map-compute-eq-coprod-inr-inr y y')
    ( is-equiv-map-compute-eq-coprod-inr-inr y y')

map-Σ-map-base :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  Σ A (λ x → C (f x)) → Σ B C
map-Σ-map-base f C s = pair (f (pr1 s)) (pr2 s)

fib-map-Σ-map-base-fib :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ( t : Σ B C) → fib f (pr1 t) → fib (map-Σ-map-base f C) t
fib-map-Σ-map-base-fib f C (pair .(f x) z) (pair x refl) =
  pair (pair x z) refl

fib-fib-map-Σ-map-base :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ( t : Σ B C) → fib (map-Σ-map-base f C) t → fib f (pr1 t)
fib-fib-map-Σ-map-base f C .(pair (f x) z) (pair (pair x z) refl) =
  pair x refl

issec-fib-fib-map-Σ-map-base :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ( t : Σ B C) →
  ( (fib-map-Σ-map-base-fib f C t) ∘ (fib-fib-map-Σ-map-base f C t)) ~ id
issec-fib-fib-map-Σ-map-base f C .(pair (f x) z) (pair (pair x z) refl) =
  refl

isretr-fib-fib-map-Σ-map-base :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ( t : Σ B C) →
  ( (fib-fib-map-Σ-map-base f C t) ∘ (fib-map-Σ-map-base-fib f C t)) ~ id
isretr-fib-fib-map-Σ-map-base f C (pair .(f x) z) (pair x refl) = refl

is-equiv-fib-map-Σ-map-base-fib :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ( t : Σ B C) → is-equiv (fib-map-Σ-map-base-fib f C t)
is-equiv-fib-map-Σ-map-base-fib f C t =
  is-equiv-has-inverse
    ( fib-fib-map-Σ-map-base f C t)
    ( issec-fib-fib-map-Σ-map-base f C t)
    ( isretr-fib-fib-map-Σ-map-base f C t)

equiv-fib-map-Σ-map-base-fib :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ( t : Σ B C) → (fib f (pr1 t)) ≃ (fib (map-Σ-map-base f C) t)
equiv-fib-map-Σ-map-base-fib f C t =
  pair ( fib-map-Σ-map-base-fib f C t)
       ( is-equiv-fib-map-Σ-map-base-fib f C t)

is-contr-map-map-Σ-map-base :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3) (f : A → B) →
  is-contr-map f → is-contr-map (map-Σ-map-base f C)
is-contr-map-map-Σ-map-base C f is-contr-f (pair y z) =
  is-contr-is-equiv'
    ( fib f y)
    ( fib-map-Σ-map-base-fib f C (pair y z))
    ( is-equiv-fib-map-Σ-map-base-fib f C (pair y z))
    ( is-contr-f y)

is-equiv-map-Σ-map-base :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3) (f : A → B) →
  is-equiv f → is-equiv (map-Σ-map-base f C)
is-equiv-map-Σ-map-base C f is-equiv-f =
  is-equiv-is-contr-map
    ( is-contr-map-map-Σ-map-base C f (is-contr-map-is-equiv is-equiv-f))

equiv-Σ-equiv-base :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3) (e : A ≃ B) →
  Σ A (C ∘ (map-equiv e)) ≃ Σ B C
equiv-Σ-equiv-base C (pair f is-equiv-f) =
  pair (map-Σ-map-base f C) (is-equiv-map-Σ-map-base C f is-equiv-f)

map-equiv-Fin-one-ℕ : Fin one-ℕ → unit
map-equiv-Fin-one-ℕ (inr star) = star

inv-map-equiv-Fin-one-ℕ : unit → Fin one-ℕ
inv-map-equiv-Fin-one-ℕ star = inr star

issec-inv-map-equiv-Fin-one-ℕ :
  ( map-equiv-Fin-one-ℕ ∘ inv-map-equiv-Fin-one-ℕ) ~ id
issec-inv-map-equiv-Fin-one-ℕ star = refl

isretr-inv-map-equiv-Fin-one-ℕ :
  ( inv-map-equiv-Fin-one-ℕ ∘ map-equiv-Fin-one-ℕ) ~ id
isretr-inv-map-equiv-Fin-one-ℕ (inr star) = refl

is-equiv-map-equiv-Fin-one-ℕ : is-equiv map-equiv-Fin-one-ℕ
is-equiv-map-equiv-Fin-one-ℕ =
  is-equiv-has-inverse
    inv-map-equiv-Fin-one-ℕ
    issec-inv-map-equiv-Fin-one-ℕ
    isretr-inv-map-equiv-Fin-one-ℕ

equiv-Fin-one-ℕ : Fin one-ℕ ≃ unit
equiv-Fin-one-ℕ = pair map-equiv-Fin-one-ℕ is-equiv-map-equiv-Fin-one-ℕ

is-contr-Fin-one-ℕ : is-contr (Fin one-ℕ)
is-contr-Fin-one-ℕ = is-contr-equiv unit equiv-Fin-one-ℕ is-contr-unit

is-contr-total-path' :
  {i : Level} {A : UU i} (a : A) → is-contr (Σ A (λ x → Id x a))
is-contr-total-path' a = is-contr-map-is-equiv is-equiv-id a
  
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-decidable-map : (A → B) → UU (l1 ⊔ l2)
  is-decidable-map f = (y : B) → is-decidable (fib f y)

  is-decidable-retract-of :
    A retract-of B → is-decidable B → is-decidable A
  is-decidable-retract-of (pair i (pair r H)) (inl b) = inl (r b)
  is-decidable-retract-of (pair i (pair r H)) (inr f) = inr (f ∘ i)

  is-decidable-is-equiv :
    {f : A → B} → is-equiv f → is-decidable B → is-decidable A
  is-decidable-is-equiv {f} (pair (pair g G) (pair h H)) =
    is-decidable-retract-of (pair f (pair h H))

  is-decidable-equiv :
    (e : A ≃ B) → is-decidable B → is-decidable A
  is-decidable-equiv e = is-decidable-iff (map-inv-equiv e) (map-equiv e)

is-decidable-equiv' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-decidable A → is-decidable B
is-decidable-equiv' e = is-decidable-equiv (inv-equiv e)

has-decidable-equality-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  has-decidable-equality B → has-decidable-equality A
has-decidable-equality-equiv e dB x y =
  is-decidable-equiv (equiv-ap e x y) (dB (map-equiv e x) (map-equiv e y))

has-decidable-equality-equiv' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  has-decidable-equality A → has-decidable-equality B
has-decidable-equality-equiv' e = has-decidable-equality-equiv (inv-equiv e)

fundamental-theorem-id-retr :
  {i j : Level} {A : UU i} {B : A → UU j} (a : A) →
  (i : (x : A) → B x → Id a x) → (R : (x : A) → retr (i x)) →
  is-fiberwise-equiv i
fundamental-theorem-id-retr {_} {_} {A} {B} a i R =
  is-fiberwise-equiv-is-equiv-tot i
    ( is-equiv-is-contr (tot i)
      ( is-contr-retract-of (Σ _ (λ y → Id a y))
        ( pair (tot i)
          ( pair (tot λ x → pr1 (R x))
            ( ( inv-htpy (tot-comp i (λ x → pr1 (R x)))) ∙h
              ( ( tot-htpy λ x → pr2 (R x)) ∙h (tot-id B)))))
        ( is-contr-total-path a))
      ( is-contr-total-path a))

map-Σ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4) (f : A → B) (g : (x : A) → C x → D (f x)) →
  Σ A C → Σ B D
map-Σ D f g t = pair (f (pr1 t)) (g (pr1 t) (pr2 t))

triangle-map-Σ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4) (f : A → B) (g : (x : A) → C x → D (f x)) →
  (map-Σ D f g) ~ ((map-Σ-map-base f D) ∘ (tot g))
triangle-map-Σ D f g t = refl

is-fiberwise-equiv-is-equiv-map-Σ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4) (f : A → B) (g : (x : A) → C x → D (f x)) →
  is-equiv f → is-equiv (map-Σ D f g) → is-fiberwise-equiv g
is-fiberwise-equiv-is-equiv-map-Σ
  D f g is-equiv-f is-equiv-map-Σ-fg =
  is-fiberwise-equiv-is-equiv-tot g
    ( is-equiv-right-factor
      ( map-Σ D f g)
      ( map-Σ-map-base f D)
      ( tot g)
      ( triangle-map-Σ D f g)
      ( is-equiv-map-Σ-map-base D f is-equiv-f)
      ( is-equiv-map-Σ-fg))

is-equiv-map-Σ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4) (f : A → B) (g : (x : A) → C x → D (f x)) →
  is-equiv f → (is-fiberwise-equiv g) →
  is-equiv (map-Σ D f g)
is-equiv-map-Σ
  D f g is-equiv-f is-fiberwise-equiv-g =
  is-equiv-comp
    ( map-Σ D f g)
    ( map-Σ-map-base f D)
    ( tot g)
    ( triangle-map-Σ D f g)
    ( is-equiv-tot-is-fiberwise-equiv is-fiberwise-equiv-g)
    ( is-equiv-map-Σ-map-base D f is-equiv-f)

equiv-Σ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4) (e : A ≃ B) (g : (x : A) → C x ≃ D (map-equiv e x)) →
  Σ A C ≃ Σ B D
equiv-Σ D e g =
  pair
    ( map-Σ D (map-equiv e) (λ x → map-equiv (g x)))
    ( is-equiv-map-Σ D
      ( map-equiv e)
      ( λ x → map-equiv (g x))
      ( is-equiv-map-equiv e)
      ( λ x → is-equiv-map-equiv (g x)))

is-equiv-top-is-equiv-left-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h)) →
  is-equiv i → is-equiv f → is-equiv g → is-equiv h
is-equiv-top-is-equiv-left-square f g h i H is-equiv-i is-equiv-f is-equiv-g =
  is-equiv-right-factor (i ∘ f) g h H is-equiv-g
    ( is-equiv-comp' i f is-equiv-f is-equiv-i)

is-emb-htpy :
  {i j : Level} {A : UU i} {B : UU j} (f g : A → B) → (f ~ g) →
  is-emb g → is-emb f
is-emb-htpy f g H is-emb-g x y =
  is-equiv-top-is-equiv-left-square
    ( ap g)
    ( concat' (f x) (H y))
    ( ap f)
    ( concat (H x) (g y))
    ( htpy-nat H)
    ( is-equiv-concat (H x) (g y))
    ( is-emb-g x y)
    ( is-equiv-concat' (f x) (H y))

is-emb-htpy' :
  {i j : Level} {A : UU i} {B : UU j} (f g : A → B) → (f ~ g) →
  is-emb f → is-emb g
is-emb-htpy' f g H is-emb-f =
  is-emb-htpy g f (inv-htpy H) is-emb-f

is-emb-comp :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) → is-emb g →
  is-emb h → is-emb f
is-emb-comp f g h H is-emb-g is-emb-h =
  is-emb-htpy f (g ∘ h) H
    ( λ x y → is-equiv-comp (ap (g ∘ h)) (ap g) (ap h) (ap-comp g h)
      ( is-emb-h x y)
      ( is-emb-g (h x) (h y)))

is-emb-comp' :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (g : B → X) (h : A → B) → is-emb g → is-emb h → is-emb (g ∘ h)
is-emb-comp' g h = is-emb-comp (g ∘ h) g h refl-htpy

comp-emb :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k} →
  (B ↪ C) → (A ↪ B) → (A ↪ C)
comp-emb (pair g H) (pair f K) = pair (g ∘ f) (is-emb-comp' g f H K)

is-emb-inl :
  {i j : Level} (A : UU i) (B : UU j) → is-emb (inl {A = A} {B = B})
is-emb-inl A B x =
  fundamental-theorem-id x refl
    ( is-contr-is-equiv
      ( Σ A (λ y → Eq-coprod A B (inl x) (inl y)))
      ( tot (λ y → Eq-eq-coprod A B (inl x) (inl y)))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ y → is-equiv-Eq-eq-coprod A B (inl x) (inl y)))
      ( is-contr-equiv'
        ( Σ A (Id x))
        ( equiv-tot (λ y → equiv-raise _ (Id x y)))
        ( is-contr-total-path x)))
    ( λ y → ap inl)

emb-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → A ↪ coprod A B
emb-inl {l1} {l2} {A} {B} = pair inl (is-emb-inl A B)

is-emb-inr :
  {i j : Level} (A : UU i) (B : UU j) → is-emb (inr {A = A} {B = B})
is-emb-inr A B x =
  fundamental-theorem-id x refl
    ( is-contr-is-equiv
      ( Σ B (λ y → Eq-coprod A B (inr x) (inr y)))
      ( tot (λ y → Eq-eq-coprod A B (inr x) (inr y)))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ y → is-equiv-Eq-eq-coprod A B (inr x) (inr y)))
      ( is-contr-equiv'
        ( Σ B (Id x))
        ( equiv-tot (λ y → equiv-raise _ (Id x y)))
        ( is-contr-total-path x)))
    ( λ y → ap inr)

emb-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → B ↪ coprod A B
emb-inr {l1} {l2} {A} {B} = pair inr (is-emb-inr A B)

is-emb-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {f : A → C} {g : B → C} → is-emb f → is-emb g → ((a : A) (b : B) →
  ¬ (Id (f a) (g b))) → is-emb (ind-coprod (λ x → C) f g)
is-emb-coprod {A = A} {B} {C} {f} {g} H K L (inl a) (inl a') =
  is-equiv-left-factor
    ( ap f)
    ( ap (ind-coprod (λ x → C) f g))
    ( ap inl)
    ( λ p → ap-comp (ind-coprod (λ x → C) f g) inl p)
    ( H a a')
    ( is-emb-inl A B a a')
is-emb-coprod {A = A} {B} {C} {f} {g} H K L (inl a) (inr b') =
  is-equiv-is-empty (ap (ind-coprod (λ x → C) f g)) (L a b')
is-emb-coprod {A = A} {B} {C} {f} {g} H K L (inr b) (inl a') =
  is-equiv-is-empty (ap (ind-coprod (λ x → C) f g)) (L a' b ∘ inv)
is-emb-coprod {A = A} {B} {C} {f} {g} H K L (inr b) (inr b') =
  is-equiv-left-factor
    ( ap g)
    ( ap (ind-coprod (λ x → C) f g))
    ( ap inr)
    ( λ p → ap-comp (ind-coprod (λ x → C) f g) inr p)
    ( K b b')
    ( is-emb-inr A B b b')

is-emb-right-factor :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) → is-emb g →
  is-emb f → is-emb h
is-emb-right-factor f g h H is-emb-g is-emb-f x y =
  is-equiv-right-factor
    ( ap (g ∘ h))
    ( ap g)
    ( ap h)
    ( ap-comp g h)
    ( is-emb-g (h x) (h y))
    ( is-emb-htpy (g ∘ h) f (inv-htpy H) is-emb-f x y)

--------------------------------------------------------------------------------

-- Propositions, sets, and truncation levels

is-prop :
  {i : Level} (A : UU i) → UU i
is-prop A = (x y : A) → is-contr (Id x y)

is-prop-map : {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → UU (l1 ⊔ l2)
is-prop-map f = (b : _) → is-prop (fib f b)

is-subtype : {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → UU (l1 ⊔ l2)
is-subtype B = (x : _) → is-prop (B x)

UU-Prop :
  (l : Level) → UU (lsuc l)
UU-Prop l = Σ (UU l) is-prop

type-Prop :
  {l : Level} → UU-Prop l → UU l
type-Prop P = pr1 P

is-prop-type-Prop :
  {l : Level} (P : UU-Prop l) → is-prop (type-Prop P)
is-prop-type-Prop P = pr2 P

all-elements-equal :
  {i : Level} (A : UU i) → UU i
all-elements-equal A = (x y : A) → Id x y

is-prop-all-elements-equal :
  {i : Level} {A : UU i} → all-elements-equal A → is-prop A
is-prop-all-elements-equal {i} {A} H x y =
  pair
    ( (inv (H x x)) ∙ (H x y))
    ( λ { refl → left-inv (H x x)})

is-proof-irrelevant :
  {l1 : Level} → UU l1 → UU l1
is-proof-irrelevant A = A → is-contr A

is-subterminal :
  {l1 : Level} → UU l1 → UU l1
is-subterminal A = is-emb (terminal-map {A = A})

eq-is-prop' :
  {i : Level} {A : UU i} → is-prop A → all-elements-equal A
eq-is-prop' H x y = pr1 (H x y)

eq-is-prop :
  {i : Level} {A : UU i} → is-prop A → {x y : A} → Id x y
eq-is-prop H {x} {y} = eq-is-prop' H x y

is-proof-irrelevant-all-elements-equal :
  {l1 : Level} {A : UU l1} → all-elements-equal A → is-proof-irrelevant A
is-proof-irrelevant-all-elements-equal H a = pair a (H a)

is-proof-irrelevant-is-prop :
  {i : Level} {A : UU i} → is-prop A → is-proof-irrelevant A
is-proof-irrelevant-is-prop =
  is-proof-irrelevant-all-elements-equal ∘ eq-is-prop'

is-prop-is-proof-irrelevant :
  {i : Level} {A : UU i} → is-proof-irrelevant A → is-prop A
is-prop-is-proof-irrelevant H x y = is-prop-is-contr (H x) x y

eq-is-proof-irrelevant :
  {l1 : Level} {A : UU l1} → is-proof-irrelevant A → all-elements-equal A
eq-is-proof-irrelevant H =
  eq-is-prop' (is-prop-is-proof-irrelevant H)

is-equiv-is-prop : {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-prop A →
  is-prop B → {f : A → B} → (B → A) → is-equiv f
is-equiv-is-prop is-prop-A is-prop-B {f} g =
  is-equiv-has-inverse
    ( g)
    ( λ y → center (is-prop-B (f (g y)) y))
    ( λ x → center (is-prop-A (g (f x)) x))

equiv-prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-prop A → is-prop B →
  (A → B) → (B → A) → A ≃ B
equiv-prop is-prop-A is-prop-B f g =
  pair f (is-equiv-is-prop is-prop-A is-prop-B g)

is-set :
  {i : Level} → UU i → UU i
is-set A = (x y : A) → is-prop (Id x y)

UU-Set :
  (i : Level) → UU (lsuc i)
UU-Set i = Σ (UU i) is-set

type-Set :
  {l : Level} → UU-Set l → UU l
type-Set X = pr1 X

is-set-type-Set :
  {l : Level} (X : UU-Set l) → is-set (type-Set X)
is-set-type-Set X = pr2 X

Id-Prop :
  {l : Level} (X : UU-Set l) (x y : type-Set X) → UU-Prop l
Id-Prop X x y = pair (Id x y) (is-set-type-Set X x y)

data 𝕋 : UU lzero where
  neg-two-𝕋 : 𝕋
  succ-𝕋 : 𝕋 → 𝕋

neg-one-𝕋 : 𝕋
neg-one-𝕋 = succ-𝕋 (neg-two-𝕋)

zero-𝕋 : 𝕋
zero-𝕋 = succ-𝕋 (neg-one-𝕋)

is-trunc : {i : Level} (k : 𝕋) → UU i → UU i
is-trunc neg-two-𝕋 A = is-contr A
is-trunc (succ-𝕋 k) A = (x y : A) → is-trunc k (Id x y)

is-trunc-map :
  {i j : Level} (k : 𝕋) {A : UU i} {B : UU j} → (A → B) → UU (i ⊔ j)
is-trunc-map k f = (y : _) → is-trunc k (fib f y)

trunc-map : {i j : Level} (k : 𝕋) (A : UU i) (B : UU j) → UU (i ⊔ j)
trunc-map k A B = Σ (A → B) (is-trunc-map k)

UU-Truncated-Type : 𝕋 → (l : Level) → UU (lsuc l)
UU-Truncated-Type k l = Σ (UU l) (is-trunc k)

type-Truncated-Type :
  {k : 𝕋} {l : Level} → UU-Truncated-Type k l → UU l
type-Truncated-Type = pr1

is-trunc-type-Truncated-Type :
  {k : 𝕋} {l : Level} (A : UU-Truncated-Type k l) →
  is-trunc k (type-Truncated-Type A)
is-trunc-type-Truncated-Type = pr2

is-trunc-is-equiv :
  {i j : Level} (k : 𝕋) {A : UU i} (B : UU j) (f : A → B) → is-equiv f →
  is-trunc k B → is-trunc k A
is-trunc-is-equiv neg-two-𝕋 B f is-equiv-f H =
  is-contr-is-equiv B f is-equiv-f H
is-trunc-is-equiv (succ-𝕋 k) B f is-equiv-f H x y =
  is-trunc-is-equiv k (Id (f x) (f y)) (ap f {x} {y})
    ( is-emb-is-equiv is-equiv-f x y) (H (f x) (f y))
                                                  
is-set-is-equiv :
  {i j : Level} {A : UU i} (B : UU j) (f : A → B) → is-equiv f →
  is-set B → is-set A
is-set-is-equiv = is-trunc-is-equiv zero-𝕋

is-trunc-equiv :
  {i j : Level} (k : 𝕋) {A : UU i} (B : UU  j) (e : A ≃ B) →
  is-trunc k B → is-trunc k A
is-trunc-equiv k B (pair f is-equiv-f) =
  is-trunc-is-equiv k B f is-equiv-f

is-set-equiv :
  {i j : Level} {A : UU i} (B : UU j) (e : A ≃ B) →
  is-set B → is-set A
is-set-equiv = is-trunc-equiv zero-𝕋

is-trunc-is-equiv' :
  {i j : Level} (k : 𝕋) (A : UU i) {B : UU j} (f : A → B) →
  is-equiv f → is-trunc k A → is-trunc k B
is-trunc-is-equiv' k A  f is-equiv-f is-trunc-A =
  is-trunc-is-equiv k A
    ( map-inv-is-equiv is-equiv-f)
    ( is-equiv-map-inv-is-equiv is-equiv-f)
    ( is-trunc-A)

is-set-is-equiv' :
  {i j : Level} (A : UU i) {B : UU j} (f : A → B) → is-equiv f →
  is-set A → is-set B
is-set-is-equiv' = is-trunc-is-equiv' zero-𝕋

is-trunc-equiv' :
  {i j : Level} (k : 𝕋) (A : UU i) {B : UU j} (e : A ≃ B) →
  is-trunc k A → is-trunc k B
is-trunc-equiv' k A (pair f is-equiv-f) =
  is-trunc-is-equiv' k A f is-equiv-f

is-set-equiv' :
  {i j : Level} (A : UU i) {B : UU j} (e : A ≃ B) →
  is-set A → is-set B
is-set-equiv' = is-trunc-equiv' zero-𝕋

is-trunc-Σ : {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
  is-trunc k A → ((x : A) → is-trunc k (B x)) → is-trunc k (Σ A B)
is-trunc-Σ neg-two-𝕋 is-trunc-A is-trunc-B =
  is-contr-Σ is-trunc-A is-trunc-B
is-trunc-Σ (succ-𝕋 k) {B = B} is-trunc-A is-trunc-B s t =
  is-trunc-is-equiv k
    ( Σ (Id (pr1 s) (pr1 t)) (λ p → Id (tr B p (pr2 s)) (pr2 t)))
    ( pair-eq-Σ)
    ( is-equiv-pair-eq-Σ s t)
    ( is-trunc-Σ k
      ( is-trunc-A (pr1 s) (pr1 t))
      ( λ p → is-trunc-B (pr1 t) (tr B p (pr2 s)) (pr2 t)))

is-trunc-prod :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-trunc k A → is-trunc k B → is-trunc k (A × B)
is-trunc-prod k is-trunc-A is-trunc-B =
  is-trunc-Σ k is-trunc-A (λ x → is-trunc-B)

is-trunc-prod' :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  (B → is-trunc (succ-𝕋 k) A) → (A → is-trunc (succ-𝕋 k) B) →
  is-trunc (succ-𝕋 k) (A × B)
is-trunc-prod' k f g (pair a b) (pair a' b') =
  is-trunc-equiv k
    ( Eq-prod (pair a b) (pair a' b'))
    ( equiv-pair-eq (pair a b) (pair a' b'))
    ( is-trunc-prod k (f b a a') (g a b b'))

is-trunc-left-factor-prod :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-trunc k (A × B) → B → is-trunc k A
is-trunc-left-factor-prod neg-two-𝕋 {A} {B} H b =
  is-contr-left-factor-prod A B H
is-trunc-left-factor-prod (succ-𝕋 k) H b a a' =
  is-trunc-left-factor-prod k {A = Id a a'} {B = Id b b}
    ( is-trunc-equiv' k
      ( Id (pair a b) (pair a' b))
      ( equiv-pair-eq (pair a b) (pair a' b))
      ( H (pair a b) (pair a' b)))
    ( refl)

is-trunc-right-factor-prod :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-trunc k (A × B) → A → is-trunc k B
is-trunc-right-factor-prod neg-two-𝕋 {A} {B} H a =
  is-contr-right-factor-prod A B H
is-trunc-right-factor-prod (succ-𝕋 k) {A} {B} H a b b' =
  is-trunc-right-factor-prod k {A = Id a a} {B = Id b b'}
    ( is-trunc-equiv' k
      ( Id (pair a b) (pair a b'))
      ( equiv-pair-eq (pair a b) (pair a b'))
      ( H (pair a b) (pair a b')))
    ( refl)

is-prop-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-prop A → is-prop B → is-prop (A × B)
is-prop-prod = is-trunc-prod neg-one-𝕋

prod-Prop : {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU-Prop (l1 ⊔ l2)
prod-Prop P Q =
  pair
    ( type-Prop P × type-Prop Q)
    ( is-prop-prod (is-prop-type-Prop P) (is-prop-type-Prop Q))

is-set-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-set A → is-set B → is-set (A × B)
is-set-prod = is-trunc-prod zero-𝕋

is-prop-is-equiv :
  {l1 l2 : Level} {A : UU l1} (B : UU l2) (f : A → B) (E : is-equiv f) →
  is-prop B → is-prop A
is-prop-is-equiv B f E H x y =
  is-contr-is-equiv _ (ap f {x} {y}) (is-emb-is-equiv E x y) (H (f x) (f y))

is-prop-equiv :
  {l1 l2 : Level} {A : UU l1} (B : UU l2) (e : A ≃ B) → is-prop B → is-prop A
is-prop-equiv B (pair f is-equiv-f) = is-prop-is-equiv B f is-equiv-f

is-prop-is-equiv' :
  {l1 l2 : Level} (A : UU l1) {B : UU l2} (f : A → B) (E : is-equiv f) →
  is-prop A → is-prop B
is-prop-is-equiv' A f E H =
  is-prop-is-equiv _ (map-inv-is-equiv E) (is-equiv-map-inv-is-equiv E) H

is-prop-equiv' :
  {l1 l2 : Level} (A : UU l1) {B : UU l2} (e : A ≃ B) → is-prop A → is-prop B
is-prop-equiv' A (pair f is-equiv-f) = is-prop-is-equiv' A f is-equiv-f

equiv-double-structure :
  {l1 l2 l3 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3) →
  Σ (Σ A B) (λ t → C (pr1 t)) ≃ Σ (Σ A C) (λ t → B (pr1 t))
equiv-double-structure {A = A} B C =
  ( ( inv-assoc-Σ A C (λ t → B (pr1 t))) ∘e
    ( equiv-tot (λ x → commutative-prod))) ∘e
  ( assoc-Σ A B (λ t → C (pr1 t)))

map-equiv-double-structure :
  {l1 l2 l3 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3) →
  Σ (Σ A B) (λ t → C (pr1 t)) → Σ (Σ A C) (λ t → B (pr1 t))
map-equiv-double-structure B C = map-equiv (equiv-double-structure B C)

is-equiv-map-equiv-double-structure :
  {l1 l2 l3 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3) →
  is-equiv (map-equiv-double-structure B C)
is-equiv-map-equiv-double-structure B C =
  is-equiv-map-equiv (equiv-double-structure B C)
  
is-contr-total-Eq-substructure :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {P : A → UU l3} →
  is-contr (Σ A B) → (is-subtype P) → (a : A) (b : B a) (p : P a) →
  is-contr (Σ (Σ A P) (λ t → B (pr1 t)))
is-contr-total-Eq-substructure {A = A} {B} {P}
  is-contr-AB is-subtype-P a b p =
  is-contr-equiv
    ( Σ (Σ A B) (λ t → P (pr1 t)))
    ( equiv-double-structure P B)
    ( is-contr-equiv
      ( P a)
      ( left-unit-law-Σ-is-contr
        ( is-contr-AB)
        ( pair a b))
      ( is-proof-irrelevant-is-prop (is-subtype-P a) p))

Eq-total-subtype :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-subtype B →
  (Σ A B) → (Σ A B) → UU l1
Eq-total-subtype is-subtype-B p p' = Id (pr1 p) (pr1 p') 

reflexive-Eq-total-subtype :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (is-subtype-B : is-subtype B) →
  (p : Σ A B) → Eq-total-subtype is-subtype-B p p
reflexive-Eq-total-subtype is-subtype-B (pair x y) = refl

Eq-total-subtype-eq :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (is-subtype-B : is-subtype B) →
  (p p' : Σ A B) → Id p p' → Eq-total-subtype is-subtype-B p p'
Eq-total-subtype-eq is-subtype-B p .p refl =
  reflexive-Eq-total-subtype is-subtype-B p

is-contr-total-Eq-total-subtype :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (is-subtype-B : is-subtype B) →
  (p : Σ A B) → is-contr (Σ (Σ A B) (Eq-total-subtype is-subtype-B p))
is-contr-total-Eq-total-subtype is-subtype-B (pair x y) =
  is-contr-total-Eq-substructure
    ( is-contr-total-path x)
    ( is-subtype-B)
    x refl y

is-equiv-Eq-total-subtype-eq :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (is-subtype-B : is-subtype B) →
  (p p' : Σ A B) → is-equiv (Eq-total-subtype-eq is-subtype-B p p')
is-equiv-Eq-total-subtype-eq is-subtype-B p =
  fundamental-theorem-id p
    ( reflexive-Eq-total-subtype is-subtype-B p)
    ( is-contr-total-Eq-total-subtype is-subtype-B p)
    ( Eq-total-subtype-eq is-subtype-B p)

equiv-Eq-total-subtype-eq :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (is-subtype-B : is-subtype B) →
  (p p' : Σ A B) → (Id p p') ≃ (Eq-total-subtype is-subtype-B p p')
equiv-Eq-total-subtype-eq is-subtype-B p p' =
  pair
    ( Eq-total-subtype-eq is-subtype-B p p')
    ( is-equiv-Eq-total-subtype-eq is-subtype-B p p')

eq-subtype :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (is-subtype-B : is-subtype B) →
  {p p' : Σ A B} → Eq-total-subtype is-subtype-B p p' → Id p p'
eq-subtype is-subtype-B {p} {p'} =
  map-inv-is-equiv (is-equiv-Eq-total-subtype-eq is-subtype-B p p')

is-trunc-succ-is-trunc :
  (k : 𝕋) {i : Level} {A : UU i} →
  is-trunc k A → is-trunc (succ-𝕋 k) A
is-trunc-succ-is-trunc neg-two-𝕋 H =
  is-prop-is-contr H
is-trunc-succ-is-trunc (succ-𝕋 k) H x y =
  is-trunc-succ-is-trunc k (H x y)

is-set-is-prop :
  {l : Level} {P : UU l} → is-prop P → is-set P
is-set-is-prop = is-trunc-succ-is-trunc neg-one-𝕋

is-trunc-map-succ-is-trunc-map :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  (f : A → B) → is-trunc-map k f → is-trunc-map (succ-𝕋 k) f
is-trunc-map-succ-is-trunc-map k f is-trunc-f b =
  is-trunc-succ-is-trunc k (is-trunc-f b)

truncated-type-succ-Truncated-Type :
  (k : 𝕋) {l : Level} → UU-Truncated-Type k l → UU-Truncated-Type (succ-𝕋 k) l
truncated-type-succ-Truncated-Type k A =
  pair
    ( type-Truncated-Type A)
    ( is-trunc-succ-is-trunc k (is-trunc-type-Truncated-Type A))

set-Prop :
  {l : Level} → UU-Prop l → UU-Set l
set-Prop P = truncated-type-succ-Truncated-Type neg-one-𝕋 P

is-trunc-is-contr :
  { l : Level} (k : 𝕋) {A : UU l} → is-contr A → is-trunc k A
is-trunc-is-contr neg-two-𝕋 is-contr-A = is-contr-A
is-trunc-is-contr (succ-𝕋 k) is-contr-A =
  is-trunc-succ-is-trunc k (is-trunc-is-contr k is-contr-A)

is-set-is-contr :
  {l : Level} {A : UU l} → is-contr A → is-set A
is-set-is-contr = is-trunc-is-contr zero-𝕋

is-trunc-is-prop :
  { l : Level} (k : 𝕋) {A : UU l} → is-prop A → is-trunc (succ-𝕋 k) A
is-trunc-is-prop k is-prop-A x y = is-trunc-is-contr k (is-prop-A x y)

is-trunc-succ-empty : (k : 𝕋) → is-trunc (succ-𝕋 k) empty
is-trunc-succ-empty k = ind-empty

is-trunc-is-empty :
  {l : Level} (k : 𝕋) {A : UU l} → is-empty A → is-trunc (succ-𝕋 k) A
is-trunc-is-empty k f = is-trunc-is-prop k (λ x → ex-falso (f x))

is-trunc-coprod : {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-trunc (succ-𝕋 (succ-𝕋 k)) A → is-trunc (succ-𝕋 (succ-𝕋 k)) B →
  is-trunc (succ-𝕋 (succ-𝕋 k)) (coprod A B)
is-trunc-coprod k {A} {B} is-trunc-A is-trunc-B (inl x) (inl y) =
  is-trunc-equiv (succ-𝕋 k)
    ( Eq-coprod A B (inl x) (inl y))
    ( equiv-Eq-eq-coprod A B (inl x) (inl y))
    ( is-trunc-equiv' (succ-𝕋 k)
      ( Id x y)
      ( equiv-raise _ (Id x y))
      ( is-trunc-A x y))
is-trunc-coprod k {A} {B} is-trunc-A is-trunc-B (inl x) (inr y) =
  is-trunc-equiv (succ-𝕋 k)
    ( Eq-coprod A B (inl x) (inr y))
    ( equiv-Eq-eq-coprod A B (inl x) (inr y))
    ( is-trunc-equiv' (succ-𝕋 k)
      ( empty)
      ( equiv-raise _ empty)
      ( is-trunc-succ-empty k))
is-trunc-coprod k {A} {B} is-trunc-A is-trunc-B (inr x) (inl y) =
  is-trunc-equiv (succ-𝕋 k)
    ( Eq-coprod A B (inr x) (inl y))
    ( equiv-Eq-eq-coprod A B (inr x) (inl y))
    ( is-trunc-equiv' (succ-𝕋 k)
      ( empty)
      ( equiv-raise _ empty)
      ( is-trunc-succ-empty k))
is-trunc-coprod k {A} {B} is-trunc-A is-trunc-B (inr x) (inr y) =
  is-trunc-equiv (succ-𝕋 k)
    ( Eq-coprod A B (inr x) (inr y))
    ( equiv-Eq-eq-coprod A B (inr x) (inr y))
    ( is-trunc-equiv' (succ-𝕋 k)
      ( Id x y)
      ( equiv-raise _ (Id x y))
      ( is-trunc-B x y))

is-set-coprod : {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-set A → is-set B → is-set (coprod A B)
is-set-coprod = is-trunc-coprod neg-two-𝕋

coprod-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2) → UU-Set (l1 ⊔ l2)
coprod-Set (pair A is-set-A) (pair B is-set-B) =
  pair (coprod A B) (is-set-coprod is-set-A is-set-B)

is-prop-unit : is-prop unit
is-prop-unit = is-prop-is-contr is-contr-unit

unit-Prop : UU-Prop lzero
unit-Prop = pair unit is-prop-unit

is-prop-empty : is-prop empty
is-prop-empty ()

empty-Prop : UU-Prop lzero
empty-Prop = pair empty is-prop-empty

is-set-unit : is-set unit
is-set-unit = is-trunc-succ-is-trunc neg-one-𝕋 is-prop-unit

unit-Set : UU-Set lzero
unit-Set = pair unit is-set-unit

is-set-empty : is-set empty
is-set-empty ()

empty-Set : UU-Set lzero
empty-Set = pair empty is-set-empty

is-set-Fin :
  (n : ℕ) → is-set (Fin n)
is-set-Fin zero-ℕ = is-set-empty
is-set-Fin (succ-ℕ n) =
  is-set-coprod (is-set-Fin n) is-set-unit

Fin-Set :
  (n : ℕ) → UU-Set lzero
Fin-Set n = pair (Fin n) (is-set-Fin n)

is-equiv-prop-in-id :
  {i j : Level} {A : UU i}
  (R : A → A → UU j)
  (p : (x y : A) → is-prop (R x y))
  (ρ : (x : A) → R x x)
  (i : (x y : A) → R x y → Id x y) →
  (x y : A) → is-equiv (i x y)
is-equiv-prop-in-id R p ρ i x =
  fundamental-theorem-id-retr x (i x)
    ( λ y → pair
      ( ind-Id x (λ z p → R x z) (ρ x) y)
      ( λ r → eq-is-prop (p x y)))

is-set-prop-in-id :
  {i j : Level} {A : UU i} (R : A → A → UU j)
  (p : (x y : A) → is-prop (R x y))
  (ρ : (x : A) → R x x)
  (i : (x y : A) → R x y → Id x y) →
  is-set A
is-set-prop-in-id R p ρ i x y =
  is-prop-is-equiv'
    ( R x y)
    ( i x y)
    ( is-equiv-prop-in-id R p ρ i x y) (p x y)

Eq-has-decidable-equality' :
  {l : Level} {A : UU l} (x y : A) → is-decidable (Id x y) → UU lzero
Eq-has-decidable-equality' x y (inl p) = unit
Eq-has-decidable-equality' x y (inr f) = empty

Eq-has-decidable-equality :
  {l : Level} {A : UU l} (d : has-decidable-equality A) → A → A → UU lzero
Eq-has-decidable-equality d x y = Eq-has-decidable-equality' x y (d x y)

is-prop-Eq-has-decidable-equality' :
  {l : Level} {A : UU l} (x y : A) (t : is-decidable (Id x y)) →
  is-prop (Eq-has-decidable-equality' x y t)
is-prop-Eq-has-decidable-equality' x y (inl p) = is-prop-unit
is-prop-Eq-has-decidable-equality' x y (inr f) = is-prop-empty

is-prop-Eq-has-decidable-equality :
  {l : Level} {A : UU l} (d : has-decidable-equality A)
  {x y : A} → is-prop (Eq-has-decidable-equality d x y)
is-prop-Eq-has-decidable-equality d {x} {y} =
  is-prop-Eq-has-decidable-equality' x y (d x y)

reflexive-Eq-has-decidable-equality :
  {l : Level} {A : UU l} (d : has-decidable-equality A) (x : A) →
  Eq-has-decidable-equality d x x 
reflexive-Eq-has-decidable-equality d x with d x x
... | inl α = star
... | inr f = f refl

Eq-has-decidable-equality-eq :
  {l : Level} {A : UU l} (d : has-decidable-equality A) {x y : A} →
  Id x y → Eq-has-decidable-equality d x y
Eq-has-decidable-equality-eq {l} {A} d {x} {.x} refl =
  reflexive-Eq-has-decidable-equality d x

eq-Eq-has-decidable-equality' :
  {l : Level} {A : UU l} (x y : A) (t : is-decidable (Id x y)) →
  Eq-has-decidable-equality' x y t → Id x y
eq-Eq-has-decidable-equality' x y (inl p) t = p
eq-Eq-has-decidable-equality' x y (inr f) t = ex-falso t

eq-Eq-has-decidable-equality :
  {l : Level} {A : UU l} (d : has-decidable-equality A) {x y : A} →
  Eq-has-decidable-equality d x y → Id x y
eq-Eq-has-decidable-equality d {x} {y} =
  eq-Eq-has-decidable-equality' x y (d x y)

is-set-has-decidable-equality :
  {l : Level} {A : UU l} → has-decidable-equality A → is-set A
is-set-has-decidable-equality d =
  is-set-prop-in-id
    ( λ x y → Eq-has-decidable-equality d x y)
    ( λ x y → is-prop-Eq-has-decidable-equality d)
    ( λ x → reflexive-Eq-has-decidable-equality d x)
    ( λ x y → eq-Eq-has-decidable-equality d)

is-prop-Σ : {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-prop A → is-subtype B → is-prop (Σ A B)
is-prop-Σ = is-trunc-Σ neg-one-𝕋
                       
Σ-Prop :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : type-Prop P → UU-Prop l2) →
  UU-Prop (l1 ⊔ l2)
Σ-Prop P Q =
  pair
    ( Σ (type-Prop P) (λ p → type-Prop (Q p)))
    ( is-prop-Σ
      ( is-prop-type-Prop P)
      ( λ p → is-prop-type-Prop (Q p)))

is-set-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-set A → ((x : A) → is-set (B x)) → is-set (Σ A B)
is-set-Σ = is-trunc-Σ zero-𝕋

Σ-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : pr1 A → UU-Set l2) → UU-Set (l1 ⊔ l2)
Σ-Set A B =
  pair
    ( Σ (type-Set A) (λ x → (type-Set (B x))))
    ( is-set-Σ (is-set-type-Set A) (λ x → is-set-type-Set (B x)))

prod-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2) → UU-Set (l1 ⊔ l2)
prod-Set A B = Σ-Set A (λ x → B)

is-trunc-is-emb : {i j : Level} (k : 𝕋) {A : UU i} {B : UU j}
  (f : A → B) → is-emb f → is-trunc (succ-𝕋 k) B → is-trunc (succ-𝕋 k) A
is-trunc-is-emb k f Ef H x y =
  is-trunc-is-equiv k (Id (f x) (f y)) (ap f {x} {y}) (Ef x y) (H (f x) (f y))

is-trunc-emb : {i j : Level} (k : 𝕋) {A : UU i} {B : UU j} →
  (f : A ↪ B) → is-trunc (succ-𝕋 k) B → is-trunc (succ-𝕋 k) A
is-trunc-emb k f = is-trunc-is-emb k (map-emb f) (is-emb-map-emb f)

total-subtype :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) → UU (l1 ⊔ l2)
total-subtype {A = A} P = Σ A (λ x → pr1 (P x))

is-prop-raise-unit :
  {l1 : Level} → is-prop (raise-unit l1)
is-prop-raise-unit {l1} =
  is-prop-equiv' unit (equiv-raise l1 unit) is-prop-unit

is-emb-is-prop-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-prop-map f → is-emb f
is-emb-is-prop-map {f = f} is-prop-map-f x =
  fundamental-theorem-id x refl
    ( is-contr-equiv
      ( fib f (f x))
      ( equiv-tot (λ y → equiv-inv (f x) (f y)))
      ( is-proof-irrelevant-is-prop (is-prop-map-f (f x)) (pair x refl)))
    ( λ y → ap f)

is-prop-map-is-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-emb f → is-prop-map f
is-prop-map-is-emb {f = f} is-emb-f y =
  is-prop-is-proof-irrelevant α
  where
  α : (t : fib f y) → is-contr (fib f y)
  α (pair x refl) =
    fundamental-theorem-id' x refl
      ( λ y → inv ∘ ap f)
      ( λ y →
        is-equiv-comp' inv (ap f)
          ( is-emb-f x y)
          ( is-equiv-inv (f x) (f y)))

is-prop-map-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : B ↪ A) → is-prop-map (map-emb f)
is-prop-map-emb f = is-prop-map-is-emb (is-emb-map-emb f)

is-emb-is-injective' : {l1 l2 : Level} {A : UU l1} (is-set-A : is-set A)
  {B : UU l2} (is-set-B : is-set B) (f : A → B) →
  is-injective f → is-emb f
is-emb-is-injective' is-set-A is-set-B f is-injective-f x y =
  is-equiv-is-prop
    ( is-set-A x y)
    ( is-set-B (f x) (f y))
    ( is-injective-f)

is-set-is-injective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-set B → is-injective f → is-set A
is-set-is-injective {f = f} H I =
  is-set-prop-in-id
    ( λ x y → Id (f x) (f y))
    ( λ x y → H (f x) (f y))
    ( λ x → refl)
    ( λ x y → I)

is-emb-is-injective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-set B → is-injective f → is-emb f
is-emb-is-injective {f = f} H I =
  is-emb-is-injective' (is-set-is-injective H I) H f I

is-prop-map-is-injective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-set B → is-injective f → is-prop-map f
is-prop-map-is-injective {f = f} H I =
  is-prop-map-is-emb (is-emb-is-injective H I)

is-prop-Eq-ℕ :
  (n m : ℕ) → is-prop (Eq-ℕ n m)
is-prop-Eq-ℕ zero-ℕ zero-ℕ = is-prop-unit
is-prop-Eq-ℕ zero-ℕ (succ-ℕ m) = is-prop-empty
is-prop-Eq-ℕ (succ-ℕ n) zero-ℕ = is-prop-empty
is-prop-Eq-ℕ (succ-ℕ n) (succ-ℕ m) = is-prop-Eq-ℕ n m

is-set-ℕ : is-set ℕ
is-set-ℕ =
  is-set-prop-in-id
    Eq-ℕ
    is-prop-Eq-ℕ
    refl-Eq-ℕ
    eq-Eq-ℕ

ℕ-Set : UU-Set lzero
ℕ-Set = pair ℕ is-set-ℕ

is-set-ℤ : is-set ℤ
is-set-ℤ = is-set-coprod is-set-ℕ (is-set-coprod is-set-unit is-set-ℕ)

ℤ-Set : UU-Set lzero
ℤ-Set = pair ℤ is-set-ℤ

fiber-inclusion :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (x : A) → B x → Σ A B
fiber-inclusion B x = pair x

fib-fiber-inclusion :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (a : A) (t : Σ A B) →
  fib (fiber-inclusion B a) t ≃ Id a (pr1 t)
fib-fiber-inclusion B a t =
  ( ( right-unit-law-Σ-is-contr
      ( λ p → is-contr-map-is-equiv (is-equiv-tr B p) (pr2 t))) ∘e
    ( equiv-left-swap-Σ)) ∘e
  ( equiv-tot (λ b → equiv-pair-eq-Σ (pair a b) t))

is-trunc-is-trunc-map-fiber-inclusion :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} →
  ((B : A → UU l2) (a : A) → is-trunc-map k (fiber-inclusion B a)) →
  is-trunc (succ-𝕋 k) A
is-trunc-is-trunc-map-fiber-inclusion {l1} {l2} k {A} H x y =
  is-trunc-equiv' k
    ( fib (fiber-inclusion B x) (pair y raise-star))
    ( fib-fiber-inclusion B x (pair y raise-star))
    ( H B x (pair y raise-star))
  where
  B : A → UU l2
  B a = raise-unit l2

is-trunc-map-fiber-inclusion-is-trunc :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} (B : A → UU l2) (a : A) →
  is-trunc (succ-𝕋 k) A → is-trunc-map k (fiber-inclusion B a)
is-trunc-map-fiber-inclusion-is-trunc k B a H t =
  is-trunc-equiv k
    ( Id a (pr1 t))
    ( fib-fiber-inclusion B a t)
    ( H a (pr1 t))

is-emb-fiber-inclusion :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
  is-set A → (x : A) → is-emb (fiber-inclusion B x)
is-emb-fiber-inclusion B H x =
  is-emb-is-prop-map (is-trunc-map-fiber-inclusion-is-trunc neg-one-𝕋 B x H)

emb-fiber-inclusion :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → is-set A → (x : A) → B x ↪ Σ A B
emb-fiber-inclusion B H x =
  pair (fiber-inclusion B x) (is-emb-fiber-inclusion B H x)
  
--------------------------------------------------------------------------------

-- Function extenxionality

htpy-eq :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (Id f g) → (f ~ g)
htpy-eq refl = refl-htpy

FUNEXT :
  {i j : Level} {A : UU i} {B : A → UU j} →
  (f : (x : A) → B x) → UU (i ⊔ j)
FUNEXT f = is-fiberwise-equiv (λ g → htpy-eq {f = f} {g = g})

WEAK-FUNEXT :
  {i j : Level} (A : UU i) (B : A → UU j) → UU (i ⊔ j)
WEAK-FUNEXT A B =
  ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)

WEAK-FUNEXT-FUNEXT :
  {l1 l2 : Level} →
  ((A : UU l1) (B : A → UU l2) (f : (x : A) → B x) → FUNEXT f) →
  ((A : UU l1) (B : A → UU l2) → WEAK-FUNEXT A B)
WEAK-FUNEXT-FUNEXT funext A B is-contr-B =
  let pi-center = (λ x → center (is-contr-B x)) in
  pair
    ( pi-center)
    ( λ f → map-inv-is-equiv (funext A B pi-center f)
      ( λ x → contraction (is-contr-B x) (f x)))

postulate funext : {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) → FUNEXT f

equiv-funext : {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (Id f g) ≃ (f ~ g)
equiv-funext {f = f} {g} = pair htpy-eq (funext f g) 

eq-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (f ~ g) → Id f g
eq-htpy = map-inv-is-equiv (funext _ _)
  
issec-eq-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  ((htpy-eq {f = f} {g = g}) ∘ (eq-htpy {f = f} {g = g})) ~ id
issec-eq-htpy = issec-map-inv-is-equiv (funext _ _)
  
isretr-eq-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  ((eq-htpy {f = f} {g = g}) ∘ (htpy-eq {f = f} {g = g})) ~ id
isretr-eq-htpy = isretr-map-inv-is-equiv (funext _ _)

is-equiv-eq-htpy :
  {i j : Level} {A : UU i} {B : A → UU j}
  (f g : (x : A) → B x) → is-equiv (eq-htpy {f = f} {g = g})
is-equiv-eq-htpy f g = is-equiv-map-inv-is-equiv (funext _ _)

eq-htpy-refl-htpy :
  {i j : Level} {A : UU i} {B : A → UU j}
  (f : (x : A) → B x) → Id (eq-htpy (refl-htpy {f = f})) refl
eq-htpy-refl-htpy f = isretr-eq-htpy refl

equiv-eq-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (f ~ g) ≃ Id f g
equiv-eq-htpy {f = f} {g} = pair eq-htpy (is-equiv-eq-htpy f g)

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

is-contr-total-htpy-FUNEXT :
  {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) →
  FUNEXT f → is-contr (Σ ((x : A) → B x) (λ g → f ~ g))
is-contr-total-htpy-FUNEXT f funext-f =
  fundamental-theorem-id' f refl-htpy (λ g → htpy-eq {g = g}) funext-f

IND-HTPY-FUNEXT :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
  FUNEXT f → IND-HTPY {l3 = l3} f
IND-HTPY-FUNEXT {l3 = l3} {A = A} {B = B} f funext-f =
  Ind-identity-system l3 f
    ( refl-htpy)
    ( is-contr-total-htpy-FUNEXT f funext-f)

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

is-contr-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)
is-contr-Π {A = A} {B = B} = WEAK-FUNEXT-FUNEXT (λ X Y → funext) A B

is-trunc-Π :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
  ((x : A) → is-trunc k (B x)) → is-trunc k ((x : A) → B x)
is-trunc-Π neg-two-𝕋 is-trunc-B = is-contr-Π is-trunc-B
is-trunc-Π (succ-𝕋 k) is-trunc-B f g =
  is-trunc-is-equiv k (f ~ g) htpy-eq
    ( funext f g)
    ( is-trunc-Π k (λ x → is-trunc-B x (f x) (g x)))

is-prop-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-subtype B → is-prop ((x : A) → B x)
is-prop-Π = is-trunc-Π neg-one-𝕋

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

type-function-Prop :
  {l1 l2 : Level} → UU l1 → UU-Prop l2 → UU (l1 ⊔ l2)
type-function-Prop A P = A → type-Prop P

is-trunc-function-type :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-trunc k B → is-trunc k (A → B)
is-trunc-function-type k {A} {B} is-trunc-B =
  is-trunc-Π k {B = λ (x : A) → B} (λ x → is-trunc-B)
                                          
is-prop-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-prop B → is-prop (A → B)
is-prop-function-type = is-trunc-function-type neg-one-𝕋

is-set-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-set B → is-set (A → B)
is-set-function-type = is-trunc-function-type zero-𝕋

is-prop-type-function-Prop :
  {l1 l2 : Level} (A : UU l1) (P : UU-Prop l2) →
  is-prop (type-function-Prop A P)
is-prop-type-function-Prop A P =
  is-prop-function-type (is-prop-type-Prop P)

function-Prop :
  {l1 l2 : Level} → UU l1 → UU-Prop l2 → UU-Prop (l1 ⊔ l2)
function-Prop A P =
  pair (type-function-Prop A P) (is-prop-type-function-Prop A P)

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

is-prop-Π' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-subtype B → is-prop ({x : A} → B x)
is-prop-Π' {l1} {l2} {A} {B} H =
  is-prop-equiv
    ( (x : A) → B x)
    ( pair
      ( λ f x → f {x})
      ( is-equiv-has-inverse
        ( λ g {x} → g x)
        ( refl-htpy)
        ( refl-htpy)))
    ( is-prop-Π H)

is-set-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  ((x : A) → is-set (B x)) → is-set ((x : A) → (B x))
is-set-Π = is-trunc-Π zero-𝕋

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

Π-total-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (C : (x : A) → B x → UU l3) → UU (l1 ⊔ (l2 ⊔ l3))
Π-total-fam {A = A} {B} C = (x : A) → Σ (B x) (C x)

type-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (C : (x : A) → B x → UU l3) → UU (l1 ⊔ (l2 ⊔ l3))
type-choice-∞ {A = A} {B} C = Σ ((x : A) → B x) (λ f → (x : A) → C x (f x))

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
  map-inv-is-equiv (is-equiv-Eq-type-choice-∞-eq C t t')

choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  Π-total-fam C → type-choice-∞ C
choice-∞ φ = pair (λ x → pr1 (φ x)) (λ x → pr2 (φ x))

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
  eq-htpy (λ x → eq-pair-Σ refl refl)

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

distributive-Π-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  Π-total-fam C ≃ type-choice-∞ C
distributive-Π-Σ = equiv-choice-∞

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

inv-distributive-Π-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3) →
  (type-choice-∞ C) ≃ (Π-total-fam C)
inv-distributive-Π-Σ = equiv-inv-choice-∞

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

precomp-Π :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ((b : B) → C b) → ((a : A) → C (f a))
precomp-Π f C h a = h (f a)

tr-precompose-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
  (f : A → B) {x y : A} (p : Id x y) → tr C (ap f p) ~ tr (λ x → C (f x)) p
tr-precompose-fam C f refl = refl-htpy

is-equiv-precomp-Π-is-coherently-invertible :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-coherently-invertible f →
  (C : B → UU l3) → is-equiv (precomp-Π f C)
is-equiv-precomp-Π-is-coherently-invertible f
  ( pair g (pair issec-g (pair isretr-g coh))) C = 
  is-equiv-has-inverse
    (λ s y → tr C (issec-g y) (s (g y)))
    ( λ s → eq-htpy (λ x → 
      ( ap (λ t → tr C t (s (g (f x)))) (coh x)) ∙
      ( ( tr-precompose-fam C f (isretr-g x) (s (g (f x)))) ∙
        ( apd s (isretr-g x)))))
    ( λ s → eq-htpy λ y → apd s (issec-g y))

is-equiv-precomp-Π-is-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) → is-equiv f →
  (C : B → UU l3) → is-equiv (precomp-Π f C)
is-equiv-precomp-Π-is-equiv f is-equiv-f =
  is-equiv-precomp-Π-is-coherently-invertible f
    ( is-coherently-invertible-is-path-split f
      ( is-path-split-is-equiv f is-equiv-f))

equiv-precomp-Π :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  (C : B → UU l3) → ((b : B) → C b) ≃ ((a : A) → C (map-equiv e a))
equiv-precomp-Π e C =
  pair
    ( precomp-Π (map-equiv e) C)
    ( is-equiv-precomp-Π-is-equiv (map-equiv e) (is-equiv-map-equiv e) C)

ind-is-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  (C : B → UU l3) (f : A → B) (is-equiv-f : is-equiv f) →
  ((x : A) → C (f x)) → ((y : B) → C y)
ind-is-equiv C f is-equiv-f =
  map-inv-is-equiv (is-equiv-precomp-Π-is-equiv f is-equiv-f C)
  
comp-is-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
  (f : A → B) (is-equiv-f : is-equiv f) (h : (x : A) → C (f x)) →
  Id (λ x → (ind-is-equiv C f is-equiv-f h) (f x)) h
comp-is-equiv C f is-equiv-f h =
  issec-map-inv-is-equiv (is-equiv-precomp-Π-is-equiv f is-equiv-f C) h
  
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

is-equiv-precomp-is-equiv-precomp-Π :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  ((C : B → UU l3) → is-equiv (precomp-Π f C)) →
  ((C : UU l3) → is-equiv (precomp f C))
is-equiv-precomp-is-equiv-precomp-Π f is-equiv-precomp-Π-f C =
  is-equiv-precomp-Π-f (λ y → C)

is-equiv-precomp-is-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) → is-equiv f →
  (C : UU l3) → is-equiv (precomp f C)
is-equiv-precomp-is-equiv f is-equiv-f =
  is-equiv-precomp-is-equiv-precomp-Π f
    ( is-equiv-precomp-Π-is-equiv f is-equiv-f)

equiv-precomp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) (C : UU l3) →
  (B → C) ≃ (A → C)
equiv-precomp e C =
  pair
    ( precomp (map-equiv e) C)
    ( is-equiv-precomp-is-equiv (map-equiv e) (is-equiv-map-equiv e) C)

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
    ( htpy-eq
      ( ap ( pr1)
           ( eq-is-contr'
             ( is-contr-map-is-equiv (is-equiv-precomp-f _ B) f)
               ( pair
                 ( f ∘ (pr1 retr-f))
                 ( ap (λ (g : pr1 A → pr1 A) → f ∘ g) (pr2 retr-f)))
               ( pair id refl))))
    ( htpy-eq (pr2 retr-f))

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

is-equiv-is-equiv-precomp-Prop :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2)
  (f : type-Prop P → type-Prop Q) →
  ({l : Level} (R : UU-Prop l) → is-equiv (precomp f (type-Prop R))) →
  is-equiv f
is-equiv-is-equiv-precomp-Prop P Q f H =
  is-equiv-is-equiv-precomp-subuniverse id (λ l → is-prop) P Q f (λ l → H {l})

is-equiv-is-equiv-precomp-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2)
  (f : type-Set A → type-Set B) →
  ({l : Level} (C : UU-Set l) → is-equiv (precomp f (type-Set C))) →
  is-equiv f
is-equiv-is-equiv-precomp-Set A B f H =
  is-equiv-is-equiv-precomp-subuniverse id (λ l → is-set) A B f (λ l → H {l})

is-equiv-is-equiv-precomp-Truncated-Type :
  {l1 l2 : Level} (k : 𝕋)
  (A : UU-Truncated-Type k l1) (B : UU-Truncated-Type k l2)
  (f : type-Truncated-Type A → type-Truncated-Type B) →
  ({l : Level} (C : UU-Truncated-Type k l) → is-equiv (precomp f (pr1 C))) →
  is-equiv f
is-equiv-is-equiv-precomp-Truncated-Type k A B f H =
    is-equiv-is-equiv-precomp-subuniverse id (λ l → is-trunc k) A B f
      ( λ l → H {l})

postcomp :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (A : UU l3) →
  (X → Y) → (A → X) → (A → Y)
postcomp A f h = f ∘ h

map-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) →
  ((i : I) → A i) → ((i : I) → B i)
map-Π f h i = f i (h i)

htpy-map-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {f f' : (i : I) → A i → B i} (H : (i : I) → (f i) ~ (f' i)) →
  (map-Π f) ~ (map-Π f')
htpy-map-Π H h = eq-htpy (λ i → H i (h i))

map-Π' :
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {J : UU l4} (α : J → I) → 
  ((i : I) → A i → B i) → ((j : J) → A (α j)) → ((j : J) → B (α j))
map-Π' α f = map-Π (λ j → f (α j))

htpy-map-Π' :
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {J : UU l4} (α : J → I) {f f' : (i : I) → A i → B i} →
  ((i : I) → (f i) ~ (f' i)) → (map-Π' α f ~ map-Π' α f')
htpy-map-Π' α H = htpy-map-Π (λ j → H (α j))

equiv-fib-map-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) (h : (i : I) → B i) →
  ((i : I) → fib (f i) (h i)) ≃ fib (map-Π f) h
equiv-fib-map-Π f h =
  equiv-tot (λ x → equiv-eq-htpy) ∘e equiv-choice-∞

is-trunc-map-map-Π :
  (k : 𝕋) {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) →
  ((i : I) → is-trunc-map k (f i)) → is-trunc-map k (map-Π f)
is-trunc-map-map-Π k {I = I} f H h =
  is-trunc-equiv' k
    ( (i : I) → fib (f i) (h i))
    ( equiv-fib-map-Π f h)
    ( is-trunc-Π k (λ i → H i (h i)))

is-equiv-map-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) (is-equiv-f : is-fiberwise-equiv f) →
  is-equiv (map-Π f)
is-equiv-map-Π f is-equiv-f =
  is-equiv-is-contr-map
    ( is-trunc-map-map-Π neg-two-𝕋 f
      ( λ i → is-contr-map-is-equiv (is-equiv-f i)))

equiv-map-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (e : (i : I) → (A i) ≃ (B i)) → ((i : I) → A i) ≃ ((i : I) → B i)
equiv-map-Π e =
  pair
    ( map-Π (λ i → map-equiv (e i)))
    ( is-equiv-map-Π _ (λ i → is-equiv-map-equiv (e i)))

module _
  { l1 l2 l3 l4 : Level}
  { A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
  ( e : A' ≃ A) (f : (a' : A') → B' a' ≃ B (map-equiv e a'))
  where
  
  map-equiv-Π : ((a' : A') → B' a') → ((a : A) → B a)
  map-equiv-Π =
    ( map-Π
      ( λ a →
        ( tr B (issec-map-inv-equiv e a)) ∘
        ( map-equiv (f (map-inv-equiv e a))))) ∘
    ( precomp-Π (map-inv-equiv e) B')

  compute-map-equiv-Π :
    (h : (a' : A') → B' a') (a' : A') →
    Id ( map-equiv-Π h (map-equiv e a')) (map-equiv (f a') (h a'))
  compute-map-equiv-Π h a' =
    ( ap
      ( λ t →
        tr B t ( map-equiv
                 ( f (map-inv-equiv e (map-equiv e a')))
                 ( h (map-inv-equiv e (map-equiv e a')))))
      ( coherence-map-inv-equiv e a')) ∙
    ( ( tr-ap
        ( map-equiv e)
        ( λ _ → id)
        ( isretr-map-inv-equiv e a')
        ( map-equiv
          ( f (map-inv-equiv e (map-equiv e a')))
          ( h (map-inv-equiv e (map-equiv e a'))))) ∙
      ( α ( map-inv-equiv e (map-equiv e a'))
          ( isretr-map-inv-equiv e a')))
    where
    α : (x : A') (p : Id x a') →
        Id ( tr (B ∘ map-equiv e) p (map-equiv (f x) (h x)))
           ( map-equiv (f a') (h a'))
    α x refl = refl

  is-equiv-map-equiv-Π : is-equiv map-equiv-Π
  is-equiv-map-equiv-Π =
    is-equiv-comp'
      ( map-Π (λ a →
        ( tr B (issec-map-inv-is-equiv (is-equiv-map-equiv e) a)) ∘
        ( map-equiv (f (map-inv-is-equiv (is-equiv-map-equiv e) a)))))
      ( precomp-Π (map-inv-is-equiv (is-equiv-map-equiv e)) B')
      ( is-equiv-precomp-Π-is-equiv
        ( map-inv-is-equiv (is-equiv-map-equiv e))
        ( is-equiv-map-inv-is-equiv (is-equiv-map-equiv e))
        ( B'))
      ( is-equiv-map-Π _
        ( λ a → is-equiv-comp'
          ( tr B (issec-map-inv-is-equiv (is-equiv-map-equiv e) a))
          ( map-equiv (f (map-inv-is-equiv (is-equiv-map-equiv e) a)))
          ( is-equiv-map-equiv
            ( f (map-inv-is-equiv (is-equiv-map-equiv e) a)))
          ( is-equiv-tr B (issec-map-inv-is-equiv (is-equiv-map-equiv e) a))))

  equiv-Π : ((a' : A') → B' a') ≃ ((a : A) → B a)
  equiv-Π = pair map-equiv-Π is-equiv-map-equiv-Π

id-map-equiv-Π :
  { l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
  ( map-equiv-Π B (equiv-id {A = A}) (λ a → equiv-id {A = B a})) ~ id
id-map-equiv-Π B = refl-htpy

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  ev-inl-inr :
    {l3 : Level} (P : coprod A B → UU l3) →
    ((t : coprod A B) → P t) → ((x : A) → P (inl x)) × ((y : B) → P (inr y))
  ev-inl-inr P s = pair (λ x → s (inl x)) (λ y → s (inr y))

  dependent-universal-property-coprod :
    {l3 : Level} (P : coprod A B → UU l3) → is-equiv (ev-inl-inr P)
  dependent-universal-property-coprod P =
    is-equiv-has-inverse
      ( λ p → ind-coprod P (pr1 p) (pr2 p))
      ( ind-Σ (λ f g → eq-pair refl refl))
      ( λ s → eq-htpy (ind-coprod _ (λ x → refl) λ y → refl))

  equiv-dependent-universal-property-coprod :
    {l3 : Level} (P : coprod A B → UU l3) →
    ((x : coprod A B) → P x) ≃ (((a : A) → P (inl a)) × ((b : B) → P (inr b)))
  equiv-dependent-universal-property-coprod P =
    pair (ev-inl-inr P) (dependent-universal-property-coprod P)

  universal-property-coprod :
    {l3 : Level} (X : UU l3) →
    is-equiv (ev-inl-inr (λ (t : coprod A B) → X))
  universal-property-coprod X = dependent-universal-property-coprod (λ t → X)
  
  equiv-universal-property-coprod :
    {l3 : Level} (X : UU l3) →
    (coprod A B → X) ≃ ((A → X) × (B → X))
  equiv-universal-property-coprod X =
    equiv-dependent-universal-property-coprod (λ t → X)
  
  uniqueness-coprod :
    {l3 : Level} {Y : UU l3} (i : A → Y) (j : B → Y) →
    ((l : Level) (X : UU l) →
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

  universal-property-coprod-is-equiv-ind-coprod :
    {l3 : Level} (X : UU l3) (i : A → X) (j : B → X) →
    is-equiv (ind-coprod (λ t → X) i j) →
    (l4 : Level) (Y : UU l4) →
      is-equiv (λ (s : X → Y) → pair' (s ∘ i) (s ∘ j))
  universal-property-coprod-is-equiv-ind-coprod X i j H l Y =
    is-equiv-comp
      ( λ s → pair (s ∘ i) (s ∘ j))
      ( ev-inl-inr (λ t → Y))
      ( precomp (ind-coprod (λ t → X) i j) Y)
      ( λ s → refl)
      ( is-equiv-precomp-is-equiv
        ( ind-coprod (λ t → X) i j)
        ( H)
        ( Y))
      ( universal-property-coprod Y)

fib-emb-Prop :
  {i j : Level} {A : UU i} {B : UU j} (f : A ↪ B) → B → UU-Prop (i ⊔ j)
fib-emb-Prop f y =
  pair ( fib (map-emb f) y)
       ( is-prop-map-is-emb (is-emb-map-emb f) y)

is-emb-pr1 :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-subtype B → is-emb (pr1 {B = B})
is-emb-pr1 {B = B} H =
  is-emb-is-prop-map (λ x → is-prop-equiv (B x) (equiv-fib-pr1 x) (H x))

equiv-ap-pr1 : {i j : Level} {A : UU i} {B : A → UU j} →
  is-subtype B → {s t : Σ A B} → Id s t ≃ Id (pr1 s) (pr1 t)
equiv-ap-pr1 is-subtype-B {s} {t} =
  pair (ap pr1) (is-emb-pr1 is-subtype-B s t)

is-subtype-is-emb-pr1 : {i j : Level} {A : UU i} {B : A → UU j} →
  is-emb (pr1 {B = B}) → is-subtype B
is-subtype-is-emb-pr1 H x =
  is-prop-equiv' (fib pr1 x) (equiv-fib-pr1 x) (is-prop-map-is-emb H x)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-contr-sec-is-equiv : {f : A → B} → is-equiv f → is-contr (sec f)
  is-contr-sec-is-equiv {f} is-equiv-f =
    is-contr-equiv'
      ( (b : B) → fib f b)
      ( equiv-choice-∞) 
      ( is-contr-Π (is-contr-map-is-equiv is-equiv-f))

  is-contr-retr-is-equiv : {f : A → B} → is-equiv f → is-contr (retr f)
  is-contr-retr-is-equiv {f} is-equiv-f =
    is-contr-is-equiv'
      ( Σ (B → A) (λ h → Id (h ∘ f) id))
      ( tot (λ h → htpy-eq))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ h → funext (h ∘ f) id))
      ( is-contr-map-is-equiv (is-equiv-precomp-is-equiv f is-equiv-f A) id)

  is-contr-is-equiv-is-equiv : {f : A → B} → is-equiv f → is-contr (is-equiv f)
  is-contr-is-equiv-is-equiv is-equiv-f =
    is-contr-prod
      ( is-contr-sec-is-equiv is-equiv-f)
      ( is-contr-retr-is-equiv is-equiv-f)

  is-subtype-is-equiv : is-subtype (is-equiv {A = A} {B = B})
  is-subtype-is-equiv f = is-prop-is-proof-irrelevant
    ( λ is-equiv-f → is-contr-prod
      ( is-contr-sec-is-equiv is-equiv-f)
      ( is-contr-retr-is-equiv is-equiv-f))

  is-equiv-Prop : (f : A → B) → UU-Prop (l1 ⊔ l2)
  is-equiv-Prop f =
    pair (is-equiv f) (is-subtype-is-equiv f)

  is-emb-map-equiv :
    is-emb (map-equiv {A = A} {B = B})
  is-emb-map-equiv = is-emb-pr1 is-subtype-is-equiv

  htpy-equiv : A ≃ B → A ≃ B → UU (l1 ⊔ l2)
  htpy-equiv e e' = (map-equiv e) ~ (map-equiv e')

  refl-htpy-equiv : (e : A ≃ B) → htpy-equiv e e
  refl-htpy-equiv e = refl-htpy

  htpy-eq-equiv : {e e' : A ≃ B} (p : Id e e') → htpy-equiv e e'
  htpy-eq-equiv {e = e} {.e} refl =
    refl-htpy-equiv e

  is-contr-total-htpy-equiv :
    (e : A ≃ B) → is-contr (Σ (A ≃ B) (λ e' → htpy-equiv e e'))
  is-contr-total-htpy-equiv (pair f is-equiv-f) =
    is-contr-total-Eq-substructure
      ( is-contr-total-htpy f)
      ( is-subtype-is-equiv)
      ( f)
      ( refl-htpy)
      ( is-equiv-f)

  is-equiv-htpy-eq-equiv :
    (e e' : A ≃ B) → is-equiv (htpy-eq-equiv {e = e} {e'})
  is-equiv-htpy-eq-equiv e =
    fundamental-theorem-id e
      ( refl-htpy-equiv e)
      ( is-contr-total-htpy-equiv e)
      ( λ e' → htpy-eq-equiv {e = e} {e'})

  equiv-htpy-eq-equiv :
    (e e' : A ≃ B) → Id e e' ≃ (htpy-equiv e e')
  equiv-htpy-eq-equiv e e' =
    pair htpy-eq-equiv (is-equiv-htpy-eq-equiv e e')

  eq-htpy-equiv : {e e' : A ≃ B} → ( htpy-equiv e e') → Id e e'
  eq-htpy-equiv {e = e} {e'} = map-inv-is-equiv (is-equiv-htpy-eq-equiv e e')

  Ind-htpy-equiv :
    {l3 : Level} (e : A ≃ B)
    (P : (e' : A ≃ B) (H : htpy-equiv e e') → UU l3) →
    sec ( λ (h : (e' : A ≃ B) (H : htpy-equiv e e') → P e' H) →
          h e (refl-htpy-equiv e))
  Ind-htpy-equiv {l3 = l3} e =
    Ind-identity-system l3 e
      ( refl-htpy-equiv e)
      ( is-contr-total-htpy-equiv e)
  
  ind-htpy-equiv :
    {l3 : Level} (e : A ≃ B) (P : (e' : A ≃ B) (H : htpy-equiv e e') → UU l3) →
    P e (refl-htpy-equiv e) → (e' : A ≃ B) (H : htpy-equiv e e') → P e' H
  ind-htpy-equiv e P = pr1 (Ind-htpy-equiv e P)
  
  comp-htpy-equiv :
    {l3 : Level} (e : A ≃ B) (P : (e' : A ≃ B) (H : htpy-equiv e e') → UU l3)
    (p : P e (refl-htpy-equiv e)) →
    Id (ind-htpy-equiv e P p e (refl-htpy-equiv e)) p
  comp-htpy-equiv e P = pr2 (Ind-htpy-equiv e P)

  is-contr-equiv-is-contr :
    is-contr A → is-contr B → is-contr (A ≃ B)
  is-contr-equiv-is-contr is-contr-A is-contr-B =
    pair
      ( equiv-is-contr is-contr-A is-contr-B)
      ( λ e → eq-htpy-equiv (λ x → eq-is-contr is-contr-B))

  is-trunc-equiv-is-trunc :
    (k : 𝕋) → is-trunc k A → is-trunc k B → is-trunc k (A ≃ B)
  is-trunc-equiv-is-trunc neg-two-𝕋 is-trunc-A is-trunc-B =
    is-contr-equiv-is-contr is-trunc-A is-trunc-B
  is-trunc-equiv-is-trunc (succ-𝕋 k) is-trunc-A is-trunc-B = 
    is-trunc-Σ (succ-𝕋 k)
      ( is-trunc-Π (succ-𝕋 k) (λ x → is-trunc-B))
      ( λ x → is-trunc-is-prop k (is-subtype-is-equiv x))

  is-prop-equiv-is-prop : is-prop A → is-prop B → is-prop (A ≃ B)
  is-prop-equiv-is-prop = is-trunc-equiv-is-trunc neg-one-𝕋

  is-set-equiv-is-set : is-set A → is-set B → is-set (A ≃ B)
  is-set-equiv-is-set = is-trunc-equiv-is-trunc zero-𝕋

type-equiv-Prop :
  { l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) → UU (l1 ⊔ l2)
type-equiv-Prop P Q = (type-Prop P) ≃ (type-Prop Q)

equiv-Prop :
  { l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU-Prop (l1 ⊔ l2)
equiv-Prop P Q =
  pair
    ( type-equiv-Prop P Q)
    ( is-prop-equiv-is-prop (is-prop-type-Prop P) (is-prop-type-Prop Q))

type-equiv-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2) → UU (l1 ⊔ l2)
type-equiv-Set A B = type-Set A ≃ type-Set B

equiv-Set :
  { l1 l2 : Level} → UU-Set l1 → UU-Set l2 → UU-Set (l1 ⊔ l2)
equiv-Set A B =
  pair
    ( type-equiv-Set A B)
    ( is-set-equiv-is-set (is-set-type-Set A) (is-set-type-Set B))

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

compose-inv-equiv-compose-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (f : B ≃ C) (e : A ≃ B) →
  Id (inv-equiv f ∘e (f ∘e e)) e
compose-inv-equiv-compose-equiv f e =
  eq-htpy-equiv (λ x → isretr-map-inv-equiv f (map-equiv e x))

compose-equiv-compose-inv-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (f : B ≃ C) (e : A ≃ C) →
  Id (f ∘e (inv-equiv f ∘e e)) e
compose-equiv-compose-inv-equiv f e =
  eq-htpy-equiv (λ x → issec-map-inv-equiv f (map-equiv e x))

is-equiv-comp-equiv :
  {l1 l2 l3 : Level} {B : UU l2} {C : UU l3}
  (f : B ≃ C) (A : UU l1) → is-equiv (λ (e : A ≃ B) → f ∘e e)
is-equiv-comp-equiv f A =
  is-equiv-has-inverse
    ( λ e → inv-equiv f ∘e e)
    ( compose-equiv-compose-inv-equiv f)
    ( compose-inv-equiv-compose-equiv f)

equiv-postcomp-equiv :
  {l1 l2 l3 : Level} {B : UU l2} {C : UU l3} →
  (f : B ≃ C) → (A : UU l1) → (A ≃ B) ≃ (A ≃ C)
equiv-postcomp-equiv f A = pair (λ e → f ∘e e) (is-equiv-comp-equiv f A)

_⇔_ :
  {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU (l1 ⊔ l2)
P ⇔ Q = (pr1 P → pr1 Q) × (pr1 Q → pr1 P)

equiv-iff' :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  (P ⇔ Q) → (pr1 P ≃ pr1 Q)
equiv-iff' P Q t = pair (pr1 t) (is-equiv-is-prop (pr2 P) (pr2 Q) (pr2 t))

equiv-iff :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  (type-hom-Prop P Q) → (type-hom-Prop Q P) → pr1 P ≃ pr1 Q
equiv-iff P Q f g = equiv-iff' P Q (pair f g)

iff-equiv :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  (pr1 P ≃ pr1 Q) → (P ⇔ Q)
iff-equiv P Q equiv-PQ = pair (pr1 equiv-PQ) (map-inv-is-equiv (pr2 equiv-PQ))

is-prop-iff :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) → is-prop (P ⇔ Q)
is-prop-iff P Q =
  is-prop-prod
    ( is-prop-function-type (pr2 Q))
    ( is-prop-function-type (pr2 P))

is-prop-equiv-Prop :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  is-prop ((pr1 P) ≃ (pr1 Q))
is-prop-equiv-Prop P Q =
  is-prop-equiv-is-prop (pr2 P) (pr2 Q)

is-equiv-equiv-iff :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  is-equiv (equiv-iff' P Q)
is-equiv-equiv-iff P Q =
  is-equiv-is-prop
    ( is-prop-iff P Q)
    ( is-prop-equiv-Prop P Q)
    ( iff-equiv P Q)

equiv-equiv-iff :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  (P ⇔ Q) ≃ (type-Prop P ≃ type-Prop Q)
equiv-equiv-iff P Q =
  pair (equiv-iff' P Q) (is-equiv-equiv-iff P Q)

is-prop-is-contr-endomaps :
  {l : Level} (P : UU l) → is-contr (P → P) → is-prop P
is-prop-is-contr-endomaps P H =
  is-prop-all-elements-equal (λ x → htpy-eq (eq-is-contr H))

is-contr-endomaps-is-prop :
  {l : Level} (P : UU l) → is-prop P → is-contr (P → P)
is-contr-endomaps-is-prop P is-prop-P =
  is-proof-irrelevant-is-prop (is-prop-function-type is-prop-P) id

is-prop-is-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → is-prop (is-emb f)
is-prop-is-emb f =
  is-prop-Π (λ x → is-prop-Π (λ y → is-subtype-is-equiv (ap f)))

is-emb-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU-Prop (l1 ⊔ l2)
is-emb-Prop f = pair (is-emb f) (is-prop-is-emb f)

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

is-prop-is-trunc :
  {l : Level} (k : 𝕋) (A : UU l) → is-prop (is-trunc k A)
is-prop-is-trunc neg-two-𝕋 = is-subtype-is-contr
is-prop-is-trunc (succ-𝕋 k) A =
  is-prop-Π (λ x → is-prop-Π (λ y → is-prop-is-trunc k (Id x y)))

is-trunc-Prop : {l : Level} (k : 𝕋) (A : UU l) → UU-Prop l
is-trunc-Prop k A = pair (is-trunc k A) (is-prop-is-trunc k A)

is-prop-is-prop :
  {l : Level} (A : UU l) → is-prop (is-prop A)
is-prop-is-prop = is-prop-is-trunc neg-one-𝕋

is-prop-Prop : {l : Level} (A : UU l) → UU-Prop l
is-prop-Prop A = pair (is-prop A) (is-prop-is-prop A)

is-prop-is-set :
  {l : Level} (A : UU l) → is-prop (is-set A)
is-prop-is-set = is-prop-is-trunc zero-𝕋

is-set-Prop : {l : Level} → UU l → UU-Prop l
is-set-Prop A = pair (is-set A) (is-prop-is-set A)

is-prop-is-trunc-map :
  (k : 𝕋) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-prop (is-trunc-map k f)
is-prop-is-trunc-map k f = is-prop-Π (λ x → is-prop-is-trunc k (fib f x))

is-prop-is-contr-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-prop (is-contr-map f)
is-prop-is-contr-map f = is-prop-is-trunc-map neg-two-𝕋 f

is-prop-is-prop-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → is-prop (is-prop-map f)
is-prop-is-prop-map f = is-prop-is-trunc-map neg-one-𝕋 f

is-trunc-map-Prop :
  (k : 𝕋) {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU-Prop (l1 ⊔ l2)
is-trunc-map-Prop k f = pair (is-trunc-map k f) (is-prop-is-trunc-map k f)

is-contr-map-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU-Prop (l1 ⊔ l2)
is-contr-map-Prop f = pair (is-contr-map f) (is-prop-is-contr-map f)

is-prop-map-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU-Prop (l1 ⊔ l2)
is-prop-map-Prop f = pair (is-prop-map f) (is-prop-is-prop-map f)

equiv-is-equiv-is-contr-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-contr-map f ≃ is-equiv f
equiv-is-equiv-is-contr-map f =
  equiv-iff
    ( is-contr-map-Prop f)
    ( is-equiv-Prop f)
    ( is-equiv-is-contr-map)
    ( is-contr-map-is-equiv)

equiv-is-contr-map-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-equiv f ≃ is-contr-map f
equiv-is-contr-map-is-equiv f =
  equiv-iff
    ( is-equiv-Prop f)
    ( is-contr-map-Prop f)
    ( is-contr-map-is-equiv)
    ( is-equiv-is-contr-map)

equiv-is-emb-is-prop-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-prop-map f ≃ is-emb f
equiv-is-emb-is-prop-map f =
  equiv-iff
    ( is-prop-map-Prop f)
    ( is-emb-Prop f)
    ( is-emb-is-prop-map)
    ( is-prop-map-is-emb)

equiv-is-prop-map-is-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-emb f ≃ is-prop-map f
equiv-is-prop-map-is-emb f =
  equiv-iff
    ( is-emb-Prop f)
    ( is-prop-map-Prop f)
    ( is-prop-map-is-emb)
    ( is-emb-is-prop-map)

equiv-subtype-equiv :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} (e : A ≃ B)
  (C : A → UU-Prop l3) (D : B → UU-Prop l4) →
  ((x : A) → type-Prop (C x) ↔ type-Prop (D (map-equiv e x))) →
  total-subtype C ≃ total-subtype D
equiv-subtype-equiv e C D H =
  equiv-Σ (λ y → type-Prop (D y)) e
    ( λ x → equiv-iff' (C x) (D (map-equiv e x)) (H x))

equiv-precomp-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → (C : UU l3) → (B ≃ C) ≃ (A ≃ C)
equiv-precomp-equiv e C =
  equiv-subtype-equiv
    ( equiv-precomp e C)
    ( is-equiv-Prop)
    ( is-equiv-Prop)
    ( λ g →
      pair
        ( is-equiv-comp' g (map-equiv e) (is-equiv-map-equiv e))
        ( λ is-equiv-eg →
          is-equiv-left-factor'
            g (map-equiv e) is-equiv-eg (is-equiv-map-equiv e)))

module _
  {l1 : Level} {A : UU l1}
  where

  ev-point : {l2 : Level} (a : A) {P : A → UU l2} → ((x : A) → P x) → P a
  ev-point a f = f a

  ev-point' : {l2 : Level} (a : A) {X : UU l2} → (A → X) → X
  ev-point' a f = f a

  dependent-universal-property-contr : (l : Level) (a : A) → UU (l1 ⊔ lsuc l)
  dependent-universal-property-contr l a =
    (P : A → UU l) → is-equiv (ev-point a {P})

  universal-property-contr : (l : Level) (a : A) → UU (l1 ⊔ lsuc l)
  universal-property-contr l a =
    (X : UU l) → is-equiv (ev-point' a {X})

  universal-property-dependent-universal-property-contr :
    (a : A) →
    ({l : Level} → dependent-universal-property-contr l a) →
    ({l : Level} → universal-property-contr l a)
  universal-property-dependent-universal-property-contr a dup-contr {l} X =
    dup-contr {l} (λ x → X)

  is-equiv-ev-point-universal-property-contr :
    (a : A) → ({l : Level} → universal-property-contr l a) →
    is-equiv (ev-point' a {A})
  is-equiv-ev-point-universal-property-contr a up-contr =
    up-contr A

  is-contr-is-equiv-ev-point :
    (a : A) → is-equiv (ev-point' a) → is-contr A
  is-contr-is-equiv-ev-point a H =
    pair a ( htpy-eq
             ( ap
               ( pr1)
               ( eq-is-contr'
                 ( is-contr-map-is-equiv H a)
                 ( pair (λ x → a) refl)
                 ( pair id refl))))

  is-contr-universal-property-contr :
    (a : A) →
    ({l : Level} → universal-property-contr l a) → is-contr A
  is-contr-universal-property-contr a up-contr =
    is-contr-is-equiv-ev-point a
      ( is-equiv-ev-point-universal-property-contr a up-contr)

  is-contr-dependent-universal-property-contr :
    (a : A) →
    ({l : Level} → dependent-universal-property-contr l a) → is-contr A
  is-contr-dependent-universal-property-contr a dup-contr =
    is-contr-universal-property-contr a
      ( universal-property-dependent-universal-property-contr a dup-contr)

  dependent-universal-property-contr-is-contr :
    (a : A) → is-contr A →
    {l : Level} → dependent-universal-property-contr l a
  dependent-universal-property-contr-is-contr a H {l} P =
    is-equiv-has-inverse
      ( ind-singleton-is-contr a H P)
      ( comp-singleton-is-contr a H P)
      ( λ f →
        eq-htpy
          ( ind-singleton-is-contr a H
            ( λ x → Id (ind-singleton-is-contr a H P (f a) x) (f x))
            ( comp-singleton-is-contr a H P (f a))))

  universal-property-contr-is-contr :
    (a : A) → is-contr A → {l : Level} → universal-property-contr l a
  universal-property-contr-is-contr a H =
    universal-property-dependent-universal-property-contr a
      ( dependent-universal-property-contr-is-contr a H)

  equiv-universal-property-contr :
    (a : A) → is-contr A → {l : Level} (X : UU l) → (A → X) ≃ X
  equiv-universal-property-contr a H X =
    pair
      ( ev-point' a)
      ( universal-property-contr-is-contr a H X)

  is-equiv-self-diagonal-is-equiv-diagonal :
    ({l : Level} (X : UU l) → is-equiv (λ x → const A X x)) →
    is-equiv (λ x → const A A x)
  is-equiv-self-diagonal-is-equiv-diagonal H = H A

  is-contr-is-equiv-self-diagonal :
    is-equiv (λ x → const A A x) → is-contr A
  is-contr-is-equiv-self-diagonal H =
    tot (λ x → htpy-eq) (center (is-contr-map-is-equiv H id))

  is-contr-is-equiv-diagonal :
    ({l : Level} (X : UU l) → is-equiv (λ x → const A X x)) → is-contr A
  is-contr-is-equiv-diagonal H =
    is-contr-is-equiv-self-diagonal
      ( is-equiv-self-diagonal-is-equiv-diagonal H)

  is-equiv-diagonal-is-contr :
    is-contr A →
    {l : Level} (X : UU l) → is-equiv (λ x → const A X x)
  is-equiv-diagonal-is-contr H X =
    is-equiv-has-inverse
      ( ev-point' (center H))
      ( λ f → eq-htpy (λ x → ap f (contraction H x)))
      ( λ x → refl)

  equiv-diagonal-is-contr :
    {l : Level} (X : UU l) → is-contr A → X ≃ (A → X)
  equiv-diagonal-is-contr X H =
    pair (const A X) (is-equiv-diagonal-is-contr H X)

ev-star :
  {l : Level} (P : unit → UU l) → ((x : unit) → P x) → P star
ev-star P f = f star

ev-star' :
  {l : Level} (Y : UU l) → (unit → Y) → Y
ev-star' Y = ev-star (λ t → Y)

pt : {l1 : Level} {X : UU l1} (x : X) → unit → X
pt x y = x

dependent-universal-property-unit :
  {l : Level} (P : unit → UU l) → is-equiv (ev-star P)
dependent-universal-property-unit =
  dependent-universal-property-contr-is-contr star is-contr-unit

equiv-dependent-universal-property-unit :
  {l : Level} (P : unit → UU l) → ((x : unit) → P x) ≃ P star
equiv-dependent-universal-property-unit P =
  pair (ev-star P) (dependent-universal-property-unit P)

equiv-ev-star :
  {l : Level} (P : unit → UU l) → ((x : unit) → P x) ≃ P star
equiv-ev-star P = pair (ev-star P) (dependent-universal-property-unit P)

universal-property-unit :
  {l : Level} (Y : UU l) → is-equiv (ev-star' Y)
universal-property-unit Y = dependent-universal-property-unit (λ t → Y)

equiv-universal-property-unit :
  {l : Level} (Y : UU l) → (unit → Y) ≃ Y
equiv-universal-property-unit Y =
  pair (ev-star' Y) (universal-property-unit Y)

equiv-ev-star' :
  {l : Level} (Y : UU l) → (unit → Y) ≃ Y
equiv-ev-star' Y = pair (ev-star' Y) (universal-property-unit Y)

is-equiv-pt-is-contr :
  {l1 : Level} {X : UU l1} (x : X) →
  is-contr X → is-equiv (pt x)
is-equiv-pt-is-contr x is-contr-X =
  is-equiv-is-contr (pt x) is-contr-unit is-contr-X

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

universal-property-unit-is-contr :
  {l1 : Level} {X : UU l1} (x : X) →
  is-contr X →
  ({l2 : Level} (Y : UU l2) → is-equiv (λ (f : X → Y) → f x))
universal-property-unit-is-contr x is-contr-X =
  universal-property-unit-is-equiv-pt x
    ( is-equiv-pt-is-contr x is-contr-X)

is-equiv-diagonal-is-equiv-pt :
  {l1 : Level} {X : UU l1} (x : X) →
  is-equiv (pt x) →
  ({l2 : Level} (Y : UU l2) → is-equiv (λ y → const X Y y))
is-equiv-diagonal-is-equiv-pt {X = X} x is-equiv-pt Y =
  is-equiv-is-section-is-equiv
    ( universal-property-unit-is-equiv-pt x is-equiv-pt Y)
    ( refl-htpy)

module _
  {l1 : Level} (A : UU l1)
  where

  dependent-universal-property-empty : (l : Level) → UU (l1 ⊔ lsuc l)
  dependent-universal-property-empty l =
    (P : A → UU l) → is-contr ((x : A) → P x)

  universal-property-empty : (l : Level) → UU (l1 ⊔ lsuc l)
  universal-property-empty l = (X : UU l) → is-contr (A → X)

  universal-property-dependent-universal-property-empty :
    ({l : Level} → dependent-universal-property-empty l) →
    ({l : Level} → universal-property-empty l)
  universal-property-dependent-universal-property-empty dup-empty {l} X =
    dup-empty {l} (λ a → X)

  is-empty-universal-property-empty :
    ({l : Level} → universal-property-empty l) → is-empty A
  is-empty-universal-property-empty up-empty = center (up-empty empty)

  dependent-universal-property-empty-is-empty :
    {l : Level} (H : is-empty A) → dependent-universal-property-empty l
  dependent-universal-property-empty-is-empty {l} H P =
    pair ( λ x → ex-falso (H x))
         ( λ f → eq-htpy (λ x → ex-falso (H x)))

  universal-property-empty-is-empty :
    {l : Level} (H : is-empty A) → universal-property-empty l
  universal-property-empty-is-empty {l} H =
    universal-property-dependent-universal-property-empty
      ( dependent-universal-property-empty-is-empty H)

dependent-universal-property-empty' :
  {l : Level} (P : empty → UU l) → is-contr ((x : empty) → P x)
dependent-universal-property-empty' P =
  pair ( ind-empty {P = P})
       ( λ f → eq-htpy ind-empty)

all-elements-equal-coprod :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  (P → ¬ Q) → all-elements-equal P → all-elements-equal Q →
  all-elements-equal (coprod P Q)
all-elements-equal-coprod
  {P = P} {Q = Q} f is-prop-P is-prop-Q (inl p) (inl p') =
  ap inl (is-prop-P p p')
all-elements-equal-coprod
  {P = P} {Q = Q} f is-prop-P is-prop-Q (inl p) (inr q') =
  ex-falso (f p q')
all-elements-equal-coprod
  {P = P} {Q = Q} f is-prop-P is-prop-Q (inr q) (inl p') =
  ex-falso (f p' q)
all-elements-equal-coprod
  {P = P} {Q = Q} f is-prop-P is-prop-Q (inr q) (inr q') =
  ap inr (is-prop-Q q q')

is-prop-coprod :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  (P → ¬ Q) → is-prop P → is-prop Q → is-prop (coprod P Q)
is-prop-coprod f is-prop-P is-prop-Q =
  is-prop-all-elements-equal
    ( all-elements-equal-coprod f
      ( eq-is-prop' is-prop-P)
      ( eq-is-prop' is-prop-Q))

is-prop-neg : {l : Level} {A : UU l} → is-prop (¬ A)
is-prop-neg {A = A} = is-prop-function-type is-prop-empty

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

module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X)
  where

  htpy-hom-slice : (h h' : hom-slice f g) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-hom-slice h h' =
    Σ ( map-hom-slice f g h ~ map-hom-slice f g h')
      ( λ K →
        ( (triangle-hom-slice f g h) ∙h (g ·l K)) ~
        ( triangle-hom-slice f g h'))

  refl-htpy-hom-slice : (h : hom-slice f g) → htpy-hom-slice h h
  refl-htpy-hom-slice h = pair refl-htpy right-unit-htpy
  
  htpy-eq-hom-slice : (h h' : hom-slice f g) → Id h h' → htpy-hom-slice h h'
  htpy-eq-hom-slice h .h refl = refl-htpy-hom-slice h

  is-contr-total-htpy-hom-slice :
    (h : hom-slice f g) → is-contr (Σ (hom-slice f g) (htpy-hom-slice h))
  is-contr-total-htpy-hom-slice h =
    is-contr-total-Eq-structure
      ( λ h' H' K → ((triangle-hom-slice f g h) ∙h (g ·l K)) ~ H')
      ( is-contr-total-htpy (map-hom-slice f g h))
      ( pair (map-hom-slice f g h) refl-htpy)
      ( is-contr-equiv'
        ( Σ ( f ~ (g ∘ (map-hom-slice f g h)))
            ( λ H' → (triangle-hom-slice f g h) ~ H'))
        ( equiv-tot (equiv-concat-htpy right-unit-htpy))
        ( is-contr-total-htpy (triangle-hom-slice f g h)))

  is-equiv-htpy-eq-hom-slice :
    (h h' : hom-slice f g) → is-equiv (htpy-eq-hom-slice h h')
  is-equiv-htpy-eq-hom-slice h =
    fundamental-theorem-id h
      ( refl-htpy-hom-slice h)
      ( is-contr-total-htpy-hom-slice h)
      ( htpy-eq-hom-slice h)

  equiv-htpy-eq-hom-slice :
    (h h' : hom-slice f g) → Id h h' ≃ htpy-hom-slice h h'
  equiv-htpy-eq-hom-slice h h' =
    pair (htpy-eq-hom-slice h h') (is-equiv-htpy-eq-hom-slice h h')

  eq-htpy-hom-slice :
    (h h' : hom-slice f g) → htpy-hom-slice h h' → Id h h'
  eq-htpy-hom-slice h h' = map-inv-is-equiv (is-equiv-htpy-eq-hom-slice h h')

fib-triangle :
  {i j k : Level} {X : UU i} {A : UU j} {B : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  (x : X) → (fib f x) → (fib g x)
fib-triangle f g h H .(f a) (pair a refl) = pair (h a) (inv (H a))

fib-triangle' :
  {i j k : Level} {X : UU i} {A : UU j} {B : UU k}
  (g : B → X) (h : A → B) (x : X) → (fib (g ∘ h) x) → fib g x
fib-triangle' g h x = fib-triangle (g ∘ h) g h refl-htpy x

square-tot-fib-triangle :
  {i j k : Level} {X : UU i} {A : UU j} {B : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  (h ∘ (map-equiv-total-fib f)) ~
  ((map-equiv-total-fib g) ∘ (tot (fib-triangle f g h H)))
square-tot-fib-triangle f g h H (pair .(f a) (pair a refl)) = refl

is-equiv-top-is-equiv-bottom-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h)) →
  (is-equiv f) → (is-equiv g) → (is-equiv i) → (is-equiv h)
is-equiv-top-is-equiv-bottom-square
  f g h i H is-equiv-f is-equiv-g is-equiv-i =
  is-equiv-right-factor (i ∘ f) g h H is-equiv-g
    ( is-equiv-comp' i f is-equiv-f is-equiv-i)

is-equiv-bottom-is-equiv-top-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h)) →
  (is-equiv f) → (is-equiv g) → (is-equiv h) → (is-equiv i)
is-equiv-bottom-is-equiv-top-square
  f g h i H is-equiv-f is-equiv-g is-equiv-h = 
  is-equiv-left-factor' i f
    ( is-equiv-comp (i ∘ f) g h H is-equiv-h is-equiv-g) is-equiv-f

is-equiv-left-is-equiv-right-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h)) →
  (is-equiv h) → (is-equiv i) → (is-equiv g) → (is-equiv f)
is-equiv-left-is-equiv-right-square
  f g h i H is-equiv-h is-equiv-i is-equiv-g =
  is-equiv-right-factor' i f is-equiv-i
    ( is-equiv-comp (i ∘ f) g h H is-equiv-h is-equiv-g)

is-equiv-right-is-equiv-left-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h)) →
  (is-equiv h) → (is-equiv i) → (is-equiv f) → (is-equiv g)
is-equiv-right-is-equiv-left-square
  f g h i H is-equiv-h is-equiv-i is-equiv-f =
  is-equiv-left-factor (i ∘ f) g h H
    ( is-equiv-comp' i f is-equiv-f is-equiv-i)
    ( is-equiv-h)

is-fiberwise-equiv-is-equiv-triangle :
  {i j k : Level} {X : UU i} {A : UU j} {B : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  (E : is-equiv h) → is-fiberwise-equiv (fib-triangle f g h H)
is-fiberwise-equiv-is-equiv-triangle f g h H E =
  is-fiberwise-equiv-is-equiv-tot
    ( fib-triangle f g h H)
    ( is-equiv-top-is-equiv-bottom-square
      ( map-equiv-total-fib f)
      ( map-equiv-total-fib g)
      ( tot (fib-triangle f g h H))
      ( h)
      ( square-tot-fib-triangle f g h H)
      ( is-equiv-map-equiv-total-fib f)
      ( is-equiv-map-equiv-total-fib g)
      ( E))

is-equiv-triangle-is-fiberwise-equiv :
  {i j k : Level} {X : UU i} {A : UU j} {B : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  (E : is-fiberwise-equiv (fib-triangle f g h H)) → is-equiv h
is-equiv-triangle-is-fiberwise-equiv f g h H E =
  is-equiv-bottom-is-equiv-top-square
    ( map-equiv-total-fib f)
    ( map-equiv-total-fib g)
    ( tot (fib-triangle f g h H))
    ( h)
    ( square-tot-fib-triangle f g h H)
    ( is-equiv-map-equiv-total-fib f)
    ( is-equiv-map-equiv-total-fib g)
    ( is-equiv-tot-is-fiberwise-equiv E)
  
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

is-equiv-fiberwise-hom-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  is-equiv (fiberwise-hom-hom-slice f g)
is-equiv-fiberwise-hom-hom-slice f g =
  is-equiv-has-inverse
    ( hom-slice-fiberwise-hom f g)
    ( issec-hom-slice-fiberwise-hom f g)
    ( isretr-hom-slice-fiberwise-hom f g)

equiv-fiberwise-hom-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  hom-slice f g ≃ ((x : X) → fib f x → fib g x)
equiv-fiberwise-hom-hom-slice f g =
  pair (fiberwise-hom-hom-slice f g) (is-equiv-fiberwise-hom-hom-slice f g)

is-equiv-hom-slice-fiberwise-hom :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  is-equiv (hom-slice-fiberwise-hom f g)
is-equiv-hom-slice-fiberwise-hom f g =
  is-equiv-has-inverse
    ( fiberwise-hom-hom-slice f g)
    ( isretr-hom-slice-fiberwise-hom f g)
    ( issec-hom-slice-fiberwise-hom f g)

equiv-hom-slice-fiberwise-hom :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  ((x : X) → fib f x → fib g x) ≃ hom-slice f g
equiv-hom-slice-fiberwise-hom f g =
  pair (hom-slice-fiberwise-hom f g) (is-equiv-hom-slice-fiberwise-hom f g)

equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → UU (l1 ⊔ (l2 ⊔ l3))
equiv-slice {A = A} {B} f g = Σ (A ≃ B) (λ e → f ~ (g ∘ (map-equiv e)))

hom-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  equiv-slice f g → hom-slice f g
hom-equiv-slice f g e = pair (pr1 (pr1 e)) (pr2 e)

is-equiv-subtype-is-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  {P : A → UU l3} {Q : B → UU l4}
  (is-subtype-P : is-subtype P) (is-subtype-Q : is-subtype Q)
  (f : A → B) (g : (x : A) → P x → Q (f x)) →
  is-equiv f → ((x : A) → (Q (f x)) → P x) → is-equiv (map-Σ Q f g)
is-equiv-subtype-is-equiv {Q = Q} is-subtype-P is-subtype-Q f g is-equiv-f h =
  is-equiv-map-Σ Q f g is-equiv-f
    ( λ x → is-equiv-is-prop (is-subtype-P x) (is-subtype-Q (f x)) (h x))

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
  equiv-slice f g →
  Σ (hom-slice f g) (λ hH → is-equiv (pr1 hH))
swap-equiv-slice {A = A} {B} f g =
  map-equiv-double-structure is-equiv (λ h → f ~ (g ∘ h))

is-equiv-swap-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  is-equiv (swap-equiv-slice f g)
is-equiv-swap-equiv-slice f g =
  is-equiv-map-equiv (equiv-double-structure is-equiv (λ h → f ~ (g ∘ h)))

fiberwise-equiv-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  equiv-slice f g → Σ ((x : X) → (fib f x) → (fib g x)) is-fiberwise-equiv
fiberwise-equiv-equiv-slice {X = X} {A} {B} f g =
  ( left-factor-fiberwise-equiv-equiv-slice f g) ∘
  ( swap-equiv-slice f g)

is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  (t : hom-slice f g) →
  ((x : X) → is-equiv (fiberwise-hom-hom-slice f g t x)) →
  is-equiv (pr1 t)
is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice
  f g (pair h H) =
  is-equiv-triangle-is-fiberwise-equiv f g h H

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

equiv-fiberwise-equiv-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  equiv-slice f g ≃ Σ ((x : X) → (fib f x) → (fib g x)) is-fiberwise-equiv
equiv-fiberwise-equiv-equiv-slice f g =
  pair ( fiberwise-equiv-equiv-slice f g)
       ( is-equiv-fiberwise-equiv-equiv-slice f g)

equiv-fam-equiv-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  equiv-slice f g ≃ ((x : X) → (fib f x) ≃ (fib g x))
equiv-fam-equiv-equiv-slice f g =
  ( equiv-inv-choice-∞ (λ x → is-equiv)) ∘e
  ( equiv-fiberwise-equiv-equiv-slice f g)

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

equiv-fib-map-Π' :
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {J : UU l4} (α : J → I) (f : (i : I) → A i → B i)
  (h : (j : J) → B (α j)) →
  ((j : J) → fib (f (α j)) (h j)) ≃ fib (map-Π' α f) h
equiv-fib-map-Π' α f h =
  equiv-tot (λ x → equiv-eq-htpy) ∘e equiv-choice-∞

is-trunc-map-map-Π-is-trunc-map' :
  (k : 𝕋) {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {J : UU l4} (α : J → I) (f : (i : I) → A i → B i) →
  ((i : I) → is-trunc-map k (f i)) → is-trunc-map k (map-Π' α f)
is-trunc-map-map-Π-is-trunc-map' k {J = J} α f H h =
  is-trunc-equiv' k
    ( (j : J) → fib (f (α j)) (h j))
    ( equiv-fib-map-Π' α f h)
    ( is-trunc-Π k (λ j → H (α j) (h j)))

is-trunc-map-is-trunc-map-map-Π' :
  (k : 𝕋) {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) →
  ({l : Level} {J : UU l} (α : J → I) → is-trunc-map k (map-Π' α f)) →
  (i : I) → is-trunc-map k (f i)
is-trunc-map-is-trunc-map-map-Π' k {A = A} {B} f H i b =
  is-trunc-equiv' k
    ( fib (map-Π (λ (x : unit) → f i)) (const unit (B i) b))
    ( equiv-Σ
      ( λ a → Id (f i a) b)
      ( equiv-universal-property-unit (A i))
      ( λ h → equiv-ap
        ( equiv-universal-property-unit (B i))
        ( map-Π (λ x → f i) h)
        ( const unit (B i) b)))
    ( H (λ x → i) (const unit (B i) b))

is-trunc-map-postcomp-is-trunc-map :
  {l1 l2 l3 : Level} (k : 𝕋) (A : UU l3) {X : UU l1} {Y : UU l2} (f : X → Y) →
  is-trunc-map k f → is-trunc-map k (postcomp A f)
is-trunc-map-postcomp-is-trunc-map k A {X} {Y} f is-trunc-f =
  is-trunc-map-map-Π-is-trunc-map' k
    ( const A unit star)
    ( const unit (X → Y) f)
    ( const unit (is-trunc-map k f) is-trunc-f)

is-trunc-map-is-trunc-map-postcomp :
  {l1 l2 : Level} (k : 𝕋) {X : UU l1} {Y : UU l2} (f : X → Y) →
  ( {l3 : Level} (A : UU l3) → is-trunc-map k (postcomp A f)) →
  is-trunc-map k f
is-trunc-map-is-trunc-map-postcomp k {X} {Y} f is-trunc-post-f =
  is-trunc-map-is-trunc-map-map-Π' k
    ( const unit (X → Y) f)
    ( λ {l} {J} α → is-trunc-post-f {l} J)
    ( star)

is-equiv-is-equiv-postcomp :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) →
  ({l3 : Level} (A : UU l3) → is-equiv (postcomp A f)) → is-equiv f
is-equiv-is-equiv-postcomp {X = X} {Y = Y} f post-comp-equiv-f =
  is-equiv-is-contr-map
    ( is-trunc-map-is-trunc-map-postcomp neg-two-𝕋 f
      ( λ {l} A → is-contr-map-is-equiv (post-comp-equiv-f A)))

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

is-prop-leq-ℕ :
  (m n : ℕ) → is-prop (leq-ℕ m n)
is-prop-leq-ℕ zero-ℕ zero-ℕ = is-prop-unit
is-prop-leq-ℕ zero-ℕ (succ-ℕ n) = is-prop-unit
is-prop-leq-ℕ (succ-ℕ m) zero-ℕ = is-prop-empty
is-prop-leq-ℕ (succ-ℕ m) (succ-ℕ n) = is-prop-leq-ℕ m n

leq-ℕ-Prop : ℕ → ℕ → UU-Prop lzero
leq-ℕ-Prop m n = pair (leq-ℕ m n) (is-prop-leq-ℕ m n)

--------------------------------------------------------------------------------

-- Propositional truncations as higher inductive types

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

postulate type-trunc-Prop : {l : Level} → UU l → UU l

postulate unit-trunc-Prop : {l : Level} {A : UU l} → A → type-trunc-Prop A

postulate
  all-elements-equal-type-trunc-Prop :
    {l : Level} {A : UU l} → all-elements-equal (type-trunc-Prop A)

is-prop-type-trunc-Prop : {l : Level} {A : UU l} → is-prop (type-trunc-Prop A)
is-prop-type-trunc-Prop {l} {A} =
  is-prop-all-elements-equal all-elements-equal-type-trunc-Prop

trunc-Prop : {l : Level} → UU l → UU-Prop l
trunc-Prop A = pair (type-trunc-Prop A) is-prop-type-trunc-Prop

extension-property-propositional-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1} (P : UU-Prop l2) →
  ( A → type-Prop P) → UU (lsuc l ⊔ l1 ⊔ l2)
extension-property-propositional-truncation l {A = A} P f =
  (Q : UU-Prop l) → (A → type-Prop Q) → (type-hom-Prop P Q)

is-propositional-truncation-extension-property :
  { l1 l2 : Level} {A : UU l1} (P : UU-Prop l2)
  ( f : A → type-Prop P) →
  ( {l : Level} → extension-property-propositional-truncation l P f) →
  ( {l : Level} → is-propositional-truncation l P f)
is-propositional-truncation-extension-property P f up-P {l} Q =
  is-equiv-is-prop
    ( is-prop-Π (λ x → is-prop-type-Prop Q))
    ( is-prop-Π (λ x → is-prop-type-Prop Q))
    ( up-P Q)

postulate
  ind-trunc-Prop' :
    {l l1 : Level} {A : UU l1} (P : type-trunc-Prop A → UU l)
    (f : (x : A) → P (unit-trunc-Prop x))
    (g : (x y : type-trunc-Prop A) (u : P x) (v : P y) →
         Id (tr P (all-elements-equal-type-trunc-Prop x y) u) v) →
    (x : type-trunc-Prop A) → P x

is-prop-condition-ind-trunc-Prop' :
  {l1 l2 : Level} {A : UU l1} {P : type-trunc-Prop A → UU l2} →
  ( (x y : type-trunc-Prop A) (u : P x) (v : P y) →
    Id (tr P (all-elements-equal-type-trunc-Prop x y) u) v) →
  (x : type-trunc-Prop A) → is-prop (P x)
is-prop-condition-ind-trunc-Prop' {P = P} H x =
  is-prop-all-elements-equal
    ( λ u v →
      ( ap ( λ γ → tr P γ u)
           ( eq-is-contr (is-prop-type-trunc-Prop x x))) ∙
      ( H x x u v))

ind-trunc-Prop :
  {l l1 : Level} {A : UU l1} (P : type-trunc-Prop A → UU-Prop l) →
  ((x : A) → type-Prop (P (unit-trunc-Prop x))) →
  (( y : type-trunc-Prop A) → type-Prop (P y))
ind-trunc-Prop P f =
  ind-trunc-Prop' (type-Prop ∘ P) f
    ( λ x y u v → eq-is-prop (is-prop-type-Prop (P y))) 

is-propositional-truncation-trunc-Prop :
  {l1 l2 : Level} (A : UU l1) →
  is-propositional-truncation l2 (trunc-Prop A) unit-trunc-Prop
is-propositional-truncation-trunc-Prop A =
  is-propositional-truncation-extension-property
    ( trunc-Prop A)
    ( unit-trunc-Prop)
    ( λ {l} Q → ind-trunc-Prop (λ x → Q))

universal-property-propositional-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1}
  (P : UU-Prop l2) (f : A → type-Prop P) → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-propositional-truncation l {A = A} P f =
  (Q : UU-Prop l) (g : A → type-Prop Q) →
  is-contr (Σ (type-hom-Prop P Q) (λ h → (h ∘ f) ~  g))

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

is-propositional-truncation-prod :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (P : UU-Prop l2) (f : A → type-Prop P)
  {A' : UU l3} (P' : UU-Prop l4) (f' : A' → type-Prop P') →
  ({l : Level} → is-propositional-truncation l P f) →
  ({l : Level} → is-propositional-truncation l P' f') →
  {l : Level} → is-propositional-truncation l (prod-Prop P P') (map-prod f f')
is-propositional-truncation-prod P f P' f' is-ptr-f is-ptr-f' Q =
  is-equiv-top-is-equiv-bottom-square
    ( ev-pair)
    ( ev-pair)
    ( precomp (map-prod f f') (type-Prop Q))
    ( λ h a a' → h (f a) (f' a'))
    ( refl-htpy)
    ( is-equiv-ev-pair)
    ( is-equiv-ev-pair)
    ( is-equiv-comp'
      ( λ h a a' → h a (f' a'))
      ( λ h a p' → h (f a) p')
      ( is-ptr-f (pair (type-hom-Prop P' Q) (is-prop-type-hom-Prop P' Q)))
      ( is-equiv-map-Π
        ( λ a g a' → g (f' a'))
        ( λ a → is-ptr-f' Q)))

is-equiv-is-ptruncation-is-ptruncation :
  {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (P' : UU-Prop l3)
  (f : A → type-Prop P) (f' : A → type-Prop P')
  (h : type-hom-Prop P P') (H : (h ∘ f) ~ f') →
  ({l : Level} → is-propositional-truncation l P f) →
  ({l : Level} → is-propositional-truncation l P' f') →
  is-equiv h
is-equiv-is-ptruncation-is-ptruncation P P' f f' h H is-ptr-P is-ptr-P' =
  is-equiv-is-prop
    ( is-prop-type-Prop P)
    ( is-prop-type-Prop P')
    ( map-inv-is-equiv (is-ptr-P' P) f)

is-ptruncation-is-ptruncation-is-equiv :
  {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (P' : UU-Prop l3)
  (f : A → type-Prop P) (f' : A → type-Prop P') (h : type-hom-Prop P P') →
  is-equiv h → ({l : Level} → is-propositional-truncation l P f) →
  ({l : Level} → is-propositional-truncation l P' f')
is-ptruncation-is-ptruncation-is-equiv P P' f f' h is-equiv-h is-ptr-f =
  is-propositional-truncation-extension-property P' f'
    ( λ R g →
      ( map-is-propositional-truncation P f is-ptr-f R g) ∘
      ( map-inv-is-equiv is-equiv-h))

is-ptruncation-is-equiv-is-ptruncation :
  {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (P' : UU-Prop l3)
  (f : A → type-Prop P) (f' : A → type-Prop P') (h : type-hom-Prop P P') →
  ({l : Level} → is-propositional-truncation l P' f') → is-equiv h →
  ({l : Level} → is-propositional-truncation l P f)
is-ptruncation-is-equiv-is-ptruncation P P' f f' h is-ptr-f' is-equiv-h =
  is-propositional-truncation-extension-property P f
    ( λ R g → (map-is-propositional-truncation P' f' is-ptr-f' R g) ∘ h)

is-uniquely-unique-propositional-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (P' : UU-Prop l3)
  (f : A → type-Prop P) (f' : A → type-Prop P') →
  ({l : Level} → is-propositional-truncation l P f) →
  ({l : Level} → is-propositional-truncation l P' f') →
  is-contr (Σ (type-equiv-Prop P P') (λ e → (map-equiv e ∘ f) ~ f'))
is-uniquely-unique-propositional-truncation P P' f f' is-ptr-f is-ptr-f' =
  is-contr-total-Eq-substructure
    ( universal-property-is-propositional-truncation _ P f is-ptr-f P' f')
    ( is-subtype-is-equiv)
    ( map-is-propositional-truncation P f is-ptr-f P' f')
    ( htpy-is-propositional-truncation P f is-ptr-f P' f')
    ( is-equiv-is-ptruncation-is-ptruncation  P P' f f'
      ( map-is-propositional-truncation P f is-ptr-f P' f')
      ( htpy-is-propositional-truncation P f is-ptr-f P' f')
      ( λ {l} → is-ptr-f)
      ( λ {l} → is-ptr-f'))

equiv-prod-trunc-Prop :
  {l1 l2 : Level} (A : UU l1) (A' : UU l2) →
  type-equiv-Prop
    ( trunc-Prop (A × A'))
    ( prod-Prop (trunc-Prop A) (trunc-Prop A'))
equiv-prod-trunc-Prop A A' =
  pr1
    ( center
      ( is-uniquely-unique-propositional-truncation
        ( trunc-Prop (A × A'))
        ( prod-Prop (trunc-Prop A) (trunc-Prop A'))
        ( unit-trunc-Prop)
        ( map-prod unit-trunc-Prop unit-trunc-Prop)
        ( is-propositional-truncation-trunc-Prop (A × A'))
        ( is-propositional-truncation-prod
          ( trunc-Prop A)
          ( unit-trunc-Prop)
          ( trunc-Prop A')
          ( unit-trunc-Prop)
          ( is-propositional-truncation-trunc-Prop A)
          ( is-propositional-truncation-trunc-Prop A'))))

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

mere-eq-Prop :
  {l : Level} {A : UU l} → A → A → UU-Prop l
mere-eq-Prop x y = trunc-Prop (Id x y)

mere-eq : {l : Level} {A : UU l} → A → A → UU l
mere-eq x y = type-trunc-Prop (Id x y)

refl-mere-eq :
  {l : Level} {A : UU l} {x : A} → mere-eq x x
refl-mere-eq = unit-trunc-Prop refl

symm-mere-eq :
  {l : Level} {A : UU l} {x y : A} → mere-eq x y → mere-eq y x
symm-mere-eq {x = x} {y} =
  functor-trunc-Prop inv

trans-mere-eq :
  {l : Level} {A : UU l} {x y z : A} →
  mere-eq x y → mere-eq y z → mere-eq x z
trans-mere-eq {x = x} {y} {z} p q =
  apply-universal-property-trunc-Prop p
    ( mere-eq-Prop x z)
    ( λ p' → functor-trunc-Prop (λ q' → p' ∙ q') q)

exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) → UU-Prop (l1 ⊔ l2)
exists-Prop {l1} {l2} {A} P = trunc-Prop (Σ A (λ x → type-Prop (P x)))

exists :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) → UU (l1 ⊔ l2)
exists P = type-Prop (exists-Prop P)

is-prop-exists :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) → is-prop (exists P)
is-prop-exists P = is-prop-type-Prop (exists-Prop P)

intro-exists :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) →
  (x : A) → type-Prop (P x) → exists P
intro-exists {A = A} P x p = unit-trunc-Prop (pair x p)

∃-Prop :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → UU-Prop (l1 ⊔ l2)
∃-Prop {A = A} B = trunc-Prop (Σ A B)

∃ :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → UU (l1 ⊔ l2)
∃ B = type-Prop (∃-Prop B)

is-prop-∃ :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → is-prop (∃ B)
is-prop-∃ B = is-prop-type-Prop (∃-Prop B)

intro-∃ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A) (b : B a) →
  ∃ B
intro-∃ a b = unit-trunc-Prop (pair a b)

is-prop-is-decidable :
  {l : Level} {A : UU l} → is-prop A → is-prop (is-decidable A)
is-prop-is-decidable is-prop-A =
  is-prop-coprod intro-dn is-prop-A is-prop-neg

is-decidable-Prop :
  {l : Level} → UU-Prop l → UU-Prop l
is-decidable-Prop P =
  pair (is-decidable (type-Prop P)) (is-prop-is-decidable (is-prop-type-Prop P))

is-empty-type-trunc-Prop :
  {l1 : Level} {X : UU l1} → is-empty X → is-empty (type-trunc-Prop X)
is-empty-type-trunc-Prop f =
  map-universal-property-trunc-Prop empty-Prop f

global-choice : {l : Level} → UU l → UU l
global-choice X = type-trunc-Prop X → X

is-prop-is-lower-bound-ℕ :
  {l1 : Level} {P : ℕ → UU l1} (x : ℕ) → is-prop (is-lower-bound-ℕ P x)
is-prop-is-lower-bound-ℕ x =
  is-prop-Π (λ y → is-prop-function-type (is-prop-leq-ℕ x y))

all-elements-equal-minimal-element-ℕ :
  {l1 : Level} {P : ℕ → UU l1} →
  ((x : ℕ) → is-prop (P x)) → all-elements-equal (minimal-element-ℕ P)
all-elements-equal-minimal-element-ℕ {l1} {P} H (pair x (pair p l)) (pair y (pair q k)) =
  eq-subtype
    ( λ n → is-prop-prod (H n) (is-prop-is-lower-bound-ℕ n))
    ( antisymmetric-leq-ℕ x y (l y q) (k x p))

is-prop-minimal-element-ℕ :
  {l1 : Level} {P : ℕ → UU l1} →
  ((x : ℕ) → is-prop (P x)) → is-prop (minimal-element-ℕ P)
is-prop-minimal-element-ℕ H =
  is-prop-all-elements-equal (all-elements-equal-minimal-element-ℕ H)

minimal-element-ℕ-Prop :
  {l1 : Level} {P : ℕ → UU l1} → ((x : ℕ) → is-prop (P x)) → UU-Prop l1
minimal-element-ℕ-Prop {l1} {P} H =
  pair (minimal-element-ℕ P) (is-prop-minimal-element-ℕ H)

global-choice-decidable-subtype-ℕ :
  {l1 : Level} {P : ℕ → UU l1} (H : (x : ℕ) → is-prop (P x))
  (d : (x : ℕ) → is-decidable (P x)) → global-choice (Σ ℕ P)
global-choice-decidable-subtype-ℕ {l1} {P} H d t =
  tot ( λ x → pr1)
      ( apply-universal-property-trunc-Prop t
        ( minimal-element-ℕ-Prop H)
        ( well-ordering-principle-ℕ P d))

dependent-universal-property-propositional-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1}
  ( P : UU-Prop l2) (f : A → type-Prop P) → UU (lsuc l ⊔ l1 ⊔ l2)
dependent-universal-property-propositional-truncation l {l1} {l2} {A} P f =
  ( Q : type-Prop P → UU-Prop l) → is-equiv (precomp-Π f (type-Prop ∘ Q))

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
  {l1 : Level} {A : UU l1} {l : Level} →
    dependent-universal-property-propositional-truncation l
    ( trunc-Prop A)
    ( unit-trunc-Prop)
dependent-universal-property-trunc-Prop {A = A} =
  dependent-universal-property-is-propositional-truncation
    ( trunc-Prop A)
    ( unit-trunc-Prop)
    ( is-propositional-truncation-trunc-Prop A)

module _
  {l1 l2 : Level} {A : UU l1} (P : type-trunc-Prop A → UU-Prop l2)
  where
  
  equiv-dependent-universal-property-trunc-Prop :
    ((y : type-trunc-Prop A) → type-Prop (P y)) ≃
    ((x : A) → type-Prop (P (unit-trunc-Prop x)))
  equiv-dependent-universal-property-trunc-Prop =
    pair
      ( precomp-Π unit-trunc-Prop (type-Prop ∘ P))
      ( dependent-universal-property-trunc-Prop P)

  apply-dependent-universal-property-trunc-Prop :
    (y : type-trunc-Prop A) → ((x : A) → type-Prop (P (unit-trunc-Prop x))) →
    type-Prop (P y)
  apply-dependent-universal-property-trunc-Prop y f =
    map-inv-equiv equiv-dependent-universal-property-trunc-Prop f y    

--------------------------------------------------------------------------------

-- Image and surjective maps

precomp-emb :
  { l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} ( i : B ↪ X) (q : hom-slice f (map-emb i)) →
  {C : UU l4} ( j : C ↪ X) →
  hom-slice (map-emb i) (map-emb j) → hom-slice f (map-emb j)
precomp-emb f i q j r =
  pair
    ( ( map-hom-slice (map-emb i) (map-emb j) r) ∘
      ( map-hom-slice f (map-emb i) q))
    ( ( triangle-hom-slice f (map-emb i) q) ∙h
      ( ( triangle-hom-slice (map-emb i) (map-emb j) r) ·r
        ( map-hom-slice f (map-emb i) q)))

is-image :
  ( l : Level) {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  { B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  UU (lsuc l ⊔ l1 ⊔ l2 ⊔ l3)
is-image l {X = X} f i q =
  ( C : UU l) (j : C ↪ X) → is-equiv (precomp-emb f i q j)

is-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-surjective {B = B} f = (y : B) → type-trunc-Prop (fib f y)

module _
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  where
    
  im : UU (l1 ⊔ l2)
  im = Σ X (λ x → type-trunc-Prop (fib f x))

  inclusion-im : im → X
  inclusion-im = pr1

  map-unit-im : A → im
  map-unit-im a = pair (f a) (unit-trunc-Prop (pair a refl))

  triangle-unit-im : f ~ (inclusion-im ∘ map-unit-im)
  triangle-unit-im a = refl

  unit-im : hom-slice f inclusion-im
  unit-im = pair map-unit-im triangle-unit-im

  hom-slice-im : hom-slice f inclusion-im
  hom-slice-im = pair map-unit-im triangle-unit-im

  Eq-im : im → im → UU l1
  Eq-im x y = Id (pr1 x) (pr1 y)

  refl-Eq-im : (x : im) → Eq-im x x
  refl-Eq-im x = refl

  Eq-eq-im : (x y : im) → Id x y → Eq-im x y
  Eq-eq-im x .x refl = refl-Eq-im x

  is-contr-total-Eq-im :
    (x : im) → is-contr (Σ im (Eq-im x))
  is-contr-total-Eq-im x =
    is-contr-total-Eq-substructure
      ( is-contr-total-path (pr1 x))
      ( λ x → is-prop-type-trunc-Prop)
      ( pr1 x)
      ( refl)
      ( pr2 x)

  is-equiv-Eq-eq-im : (x y : im) → is-equiv (Eq-eq-im x y)
  is-equiv-Eq-eq-im x =
    fundamental-theorem-id x
      ( refl-Eq-im x)
      ( is-contr-total-Eq-im x)
      ( Eq-eq-im x)

  equiv-Eq-eq-im : (x y : im) → Id x y ≃ Eq-im x y
  equiv-Eq-eq-im x y = pair (Eq-eq-im x y) (is-equiv-Eq-eq-im x y)

  eq-Eq-im : (x y : im) → Eq-im x y → Id x y
  eq-Eq-im x y = map-inv-is-equiv (is-equiv-Eq-eq-im x y)

is-emb-inclusion-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  is-emb (inclusion-im f)
is-emb-inclusion-im f =
  is-emb-pr1 (λ x → is-prop-type-trunc-Prop)

emb-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) → im f ↪ X
emb-im f = pair (inclusion-im f) (is-emb-inclusion-im f)

is-injective-inclusion-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  is-injective (inclusion-im f)
is-injective-inclusion-im f =
  is-injective-is-emb (is-emb-inclusion-im f)

is-trunc-im :
  {l1 l2 : Level} (k : 𝕋) {X : UU l1} {A : UU l2} (f : A → X) →
  is-trunc (succ-𝕋 k) X → is-trunc (succ-𝕋 k) (im f)
is-trunc-im k f = is-trunc-emb k (emb-im f) 

is-prop-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  is-prop X → is-prop (im f)
is-prop-im = is-trunc-im neg-two-𝕋

is-set-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  is-set X → is-set (im f)
is-set-im = is-trunc-im neg-one-𝕋

is-surjective-is-image :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  ({l : Level} → is-image l f i q) →
  is-surjective (map-hom-slice f (map-emb i) q)
is-surjective-is-image {A = A} {B} {X} f i q up-i b =
  apply-universal-property-trunc-Prop β
    ( trunc-Prop (fib (map-hom-slice f (map-emb i) q) b))
    ( γ)
  where
  g : Σ B (λ b → type-trunc-Prop (fib (map-hom-slice f (map-emb i) q) b)) → X
  g = map-emb i ∘ pr1
  is-emb-g : is-emb g
  is-emb-g = is-emb-comp' (map-emb i) pr1
    ( is-emb-map-emb i)
    ( is-emb-pr1 (λ x → is-prop-type-trunc-Prop))
  α : hom-slice (map-emb i) g
  α = map-inv-is-equiv
        ( up-i
          ( Σ B ( λ b →
                  type-trunc-Prop (fib (map-hom-slice f (map-emb i) q) b)))
          ( pair g is-emb-g))
        ( pair (map-unit-im (pr1 q)) (pr2 q))
  β : type-trunc-Prop (fib (map-hom-slice f (map-emb i) q) (pr1 (pr1 α b)))
  β = pr2 (pr1 α b)
  γ : fib (map-hom-slice f (map-emb i) q) (pr1 (pr1 α b)) →
      type-Prop (trunc-Prop (fib (pr1 q) b))
  γ (pair a p) =
    unit-trunc-Prop
      ( pair a (p ∙ inv (is-injective-is-emb (is-emb-map-emb i) (pr2 α b))))

is-surjective-map-unit-im :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-surjective (map-unit-im f)
is-surjective-map-unit-im f (pair y z) =
  apply-universal-property-trunc-Prop z
    ( trunc-Prop (fib (map-unit-im f) (pair y z)))
    ( α)
  where
  α : fib f y → type-Prop (trunc-Prop (fib (map-unit-im f) (pair y z)))
  α (pair x p) =
    unit-trunc-Prop (pair x (eq-subtype (λ z → is-prop-type-trunc-Prop) p))

is-prop-hom-slice :
  { l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  { B : UU l3} (i : B ↪ X) → is-prop (hom-slice f (map-emb i))
is-prop-hom-slice {X = X} f i =
  is-prop-is-equiv
    ( (x : X) → fib f x → fib (map-emb i) x)
    ( fiberwise-hom-hom-slice f (map-emb i))
    ( is-equiv-fiberwise-hom-hom-slice f (map-emb i))
    ( is-prop-Π
      ( λ x → is-prop-Π
        ( λ p → is-prop-map-is-emb (is-emb-map-emb i) x)))

is-image' :
  ( l : Level) {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  { B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  UU (lsuc l ⊔ l1 ⊔ l2 ⊔ l3)
is-image' l {X = X} f i q =
  ( C : UU l) (j : C ↪ X) →
    hom-slice f (map-emb j) → hom-slice (map-emb i) (map-emb j)

is-image-is-image' :
  ( l : Level) {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  { B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  is-image' l f i q → is-image l f i q
is-image-is-image' l f i q up' C j =
  is-equiv-is-prop
    ( is-prop-hom-slice (map-emb i) j)
    ( is-prop-hom-slice f j)
    ( up' C j)

dependent-universal-property-surj :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  UU ((lsuc l) ⊔ l1 ⊔ l2)
dependent-universal-property-surj l {B = B} f =
  (P : B → UU-Prop l) →
    is-equiv (λ (h : (b : B) → type-Prop (P b)) x → h (f x))

is-surjective-dependent-universal-property-surj :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  ({l : Level} → dependent-universal-property-surj l f) →
  is-surjective f
is-surjective-dependent-universal-property-surj f dup-surj-f =
  map-inv-is-equiv
    ( dup-surj-f (λ b → trunc-Prop (fib f b)))
    ( λ x → unit-trunc-Prop (pair x refl))

square-dependent-universal-property-surj :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (P : B → UU-Prop l3) →
  ( λ (h : (y : B) → type-Prop (P y)) x → h (f x)) ~
  ( ( λ h x → h (f x) (pair x refl)) ∘
    ( ( λ h y → (h y) ∘ unit-trunc-Prop) ∘
      ( λ h y → const (type-trunc-Prop (fib f y)) (type-Prop (P y)) (h y))))
square-dependent-universal-property-surj f P = refl-htpy

dependent-universal-property-surj-is-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-surjective f →
  ({l : Level} → dependent-universal-property-surj l f)
dependent-universal-property-surj-is-surjective f is-surj-f P =
  is-equiv-comp'
    ( λ h x → h (f x) (pair x refl))
    ( ( λ h y → (h y) ∘ unit-trunc-Prop) ∘
      ( λ h y → const (type-trunc-Prop (fib f y)) (type-Prop (P y)) (h y)))
    ( is-equiv-comp'
      ( λ h y → (h y) ∘ unit-trunc-Prop)
      ( λ h y → const (type-trunc-Prop (fib f y)) (type-Prop (P y)) (h y))
      ( is-equiv-map-Π
        ( λ y p z → p)
        ( λ y →
          is-equiv-diagonal-is-contr
            ( is-proof-irrelevant-is-prop
              ( is-prop-type-trunc-Prop)
              ( is-surj-f y))
            ( type-Prop (P y))))
      ( is-equiv-map-Π
        ( λ b g → g ∘ unit-trunc-Prop)
        ( λ b → is-propositional-truncation-trunc-Prop (fib f b) (P b))))
    ( is-equiv-map-reduce-Π-fib f ( λ y z → type-Prop (P y)))

equiv-dependent-universal-property-surj-is-surjective :
  {l l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-surjective f → (C : B → UU-Prop l) →
  ((b : B) → type-Prop (C b)) ≃ ((a : A) → type-Prop (C (f a)))
equiv-dependent-universal-property-surj-is-surjective f H C =
  pair
    ( λ h x → h (f x))
    ( dependent-universal-property-surj-is-surjective f H C)

is-image-is-surjective' :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  is-surjective (map-hom-slice f (map-emb i) q) →
  ({l : Level} → is-image' l f i q)
is-image-is-surjective' f i q H B' m =
  map-equiv
    ( ( equiv-hom-slice-fiberwise-hom (map-emb i) (map-emb m)) ∘e
      ( ( inv-equiv (reduce-Π-fib (map-emb i) (fib (map-emb m)))) ∘e
        ( inv-equiv
          ( equiv-dependent-universal-property-surj-is-surjective
            ( pr1 q)
            ( H)
            ( λ b →
              pair ( fib (map-emb m) (pr1 i b))
                   ( is-prop-map-emb m (pr1 i b)))) ∘e
          ( ( equiv-map-Π (λ a → equiv-tr (fib (map-emb m)) (pr2 q a))) ∘e
            ( ( reduce-Π-fib f (fib (map-emb m))) ∘e
              ( equiv-fiberwise-hom-hom-slice f (map-emb m)))))))

is-image-is-surjective :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  is-surjective (map-hom-slice f (map-emb i) q) →
  ({l : Level} → is-image l f i q)
is-image-is-surjective f i q H {l} =
  is-image-is-image' l f i q
    ( is-image-is-surjective' f i q H)

comp-hom-slice :
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (h : C → X) →
  hom-slice g h → hom-slice f g → hom-slice f h
comp-hom-slice f g h j i =
  pair ( ( map-hom-slice g h j) ∘
         ( map-hom-slice f g i))
       ( ( triangle-hom-slice f g i) ∙h
         ( (triangle-hom-slice g h j) ·r (map-hom-slice f g i)))

module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  (H : {l : Level} → is-image l f i q)
  {C : UU l4} (j : C ↪ X) (r : hom-slice f (map-emb j))
  where
  
  universal-property-image :
    is-contr
      ( Σ ( hom-slice (map-emb i) (map-emb j))
          ( λ h →
            htpy-hom-slice f
              ( map-emb j)
              ( comp-hom-slice f (map-emb i) (map-emb j) h q)
              ( r)))
  universal-property-image =
    is-contr-equiv'
      ( fib (precomp-emb f i q j) r)
      ( equiv-tot
        ( λ h →
          equiv-htpy-eq-hom-slice f (map-emb j) (precomp-emb f i q j h) r))
      ( is-contr-map-is-equiv (H C j) r)

  hom-slice-universal-property-image : hom-slice (map-emb i) (map-emb j)
  hom-slice-universal-property-image =
    pr1 (center universal-property-image)

  map-hom-slice-universal-property-image : B → C
  map-hom-slice-universal-property-image =
    map-hom-slice (map-emb i) (map-emb j) hom-slice-universal-property-image

  triangle-hom-slice-universal-property-image :
    (map-emb i) ~ (map-emb j ∘ map-hom-slice-universal-property-image)
  triangle-hom-slice-universal-property-image =
    triangle-hom-slice
      ( map-emb i)
      ( map-emb j)
      ( hom-slice-universal-property-image)

  htpy-hom-slice-universal-property-image :
    htpy-hom-slice f
      ( map-emb j)
      ( comp-hom-slice f
        ( map-emb i)
        ( map-emb j)
        ( hom-slice-universal-property-image)
        ( q))
      ( r)
  htpy-hom-slice-universal-property-image =
    pr2 (center universal-property-image)

  htpy-map-hom-slice-universal-property-image :
    map-hom-slice f
      ( map-emb j)
      ( comp-hom-slice f
        ( map-emb i)
        ( map-emb j)
        ( hom-slice-universal-property-image)
        ( q)) ~
    map-hom-slice f (map-emb j) r
  htpy-map-hom-slice-universal-property-image =
    pr1 htpy-hom-slice-universal-property-image

  tetrahedron-hom-slice-universal-property-image :
    ( ( ( triangle-hom-slice f (map-emb i) q) ∙h
        ( ( triangle-hom-slice-universal-property-image) ·r
          ( map-hom-slice f (map-emb i) q))) ∙h
      ( map-emb j ·l htpy-map-hom-slice-universal-property-image)) ~
    ( triangle-hom-slice f (map-emb j) r)
  tetrahedron-hom-slice-universal-property-image =
    pr2 htpy-hom-slice-universal-property-image

is-equiv-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → hom-slice f g → UU (l2 ⊔ l3)
is-equiv-hom-slice f g h = is-equiv (map-hom-slice f g h)

is-equiv-hom-slice-emb :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A ↪ X) (g : B ↪ X) (h : hom-slice (map-emb f) (map-emb g)) →
  hom-slice (map-emb g) (map-emb f) →
  is-equiv-hom-slice (map-emb f) (map-emb g) h
is-equiv-hom-slice-emb f g h i =
  is-equiv-has-inverse
    ( map-hom-slice (map-emb g) (map-emb f) i)
    ( λ y →
      is-injective-emb g
      ( inv
        ( ( triangle-hom-slice
            ( map-emb g)
            ( map-emb f)
            ( i)
            ( y)) ∙
          ( triangle-hom-slice
            ( map-emb f)
            ( map-emb g)
            ( h)
            ( map-hom-slice (map-emb g) (map-emb f) i y)))))
    ( λ x →
      is-injective-emb f
      ( inv
        ( ( triangle-hom-slice (map-emb f) (map-emb g) h x) ∙
          ( triangle-hom-slice (map-emb g) (map-emb f) i
            ( map-hom-slice
              ( map-emb f)
              ( map-emb g)
              ( h)
              ( x))))))

module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  {B' : UU l4} (i' : B' ↪ X) (q' : hom-slice f (map-emb i'))
  (h : hom-slice (map-emb i) (map-emb i'))
  where
  
  is-equiv-is-image-is-image :
    ({l : Level} → is-image l f i q) →
    ({l : Level} → is-image l f i' q') →
    is-equiv (map-hom-slice (map-emb i) (map-emb i') h)
  is-equiv-is-image-is-image up-i up-i' =
    is-equiv-hom-slice-emb i i' h (map-inv-is-equiv (up-i' B i) q)

  is-image-is-image-is-equiv :
    is-equiv (map-hom-slice (map-emb i) (map-emb i') h) →
    ({l : Level} → is-image l f i q) →
    ({l : Level} → is-image l f i' q')
  is-image-is-image-is-equiv is-equiv-h up-i {l} =
    is-image-is-image' l f i' q'
      ( λ C j r →
        comp-hom-slice
          ( map-emb i')
          ( map-emb i)
          ( map-emb j)
          ( map-inv-is-equiv (up-i C j) r)
          ( pair
            ( map-inv-is-equiv is-equiv-h)
            ( triangle-section
              ( map-emb i)
              ( map-emb i')
              ( map-hom-slice (map-emb i) (map-emb i') h)
              ( triangle-hom-slice (map-emb i) (map-emb i') h)
              ( pair ( map-inv-is-equiv is-equiv-h)
                     ( issec-map-inv-is-equiv is-equiv-h)))))

  is-image-is-equiv-is-image :
    ({l : Level} → is-image l f i' q') →
    is-equiv (map-hom-slice (map-emb i) (map-emb i') h) →
    ({l : Level} → is-image l f i q)
  is-image-is-equiv-is-image up-i' is-equiv-h {l} =
    is-image-is-image' l f i q
      ( λ C j r →
        comp-hom-slice
          ( map-emb i)
          ( map-emb i')
          ( map-emb j)
          ( map-inv-is-equiv (up-i' C j) r)
          ( h))
          
module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  (Hi : {l : Level} → is-image l f i q)
  {B' : UU l4} (i' : B' ↪ X) (q' : hom-slice f (map-emb i'))
  (Hi' : {l : Level} → is-image l f i' q')
  where

  uniqueness-image :
    is-contr
      ( Σ ( equiv-slice (map-emb i) (map-emb i'))
          ( λ e →
            htpy-hom-slice f
              ( map-emb i')
              ( comp-hom-slice f
                ( map-emb i)
                ( map-emb i')
                ( hom-equiv-slice (map-emb i) (map-emb i') e)
                ( q))
              ( q')))
  uniqueness-image =
    is-contr-equiv
      ( Σ ( Σ ( hom-slice (map-emb i) (map-emb i'))
              ( λ h →
                htpy-hom-slice f
                  ( map-emb i')
                  ( comp-hom-slice f (map-emb i) (map-emb i') h q)
                  ( q')))
          ( λ h → is-equiv (pr1 (pr1 h))))
      ( ( equiv-right-swap-Σ) ∘e
        ( equiv-Σ
          ( λ h →
            htpy-hom-slice f
              ( map-emb i')
              ( comp-hom-slice f (map-emb i) (map-emb i') (pr1 h) q)
              ( q'))
          ( equiv-right-swap-Σ)
          ( λ { (pair (pair e E) H) → equiv-id})))
      ( is-contr-equiv
        ( is-equiv
          ( map-hom-slice-universal-property-image f i q Hi i' q'))
        ( left-unit-law-Σ-is-contr
          ( universal-property-image f i q Hi i' q')
          ( center (universal-property-image f i q Hi i' q')))
        ( is-proof-irrelevant-is-prop
          ( is-subtype-is-equiv
            ( map-hom-slice-universal-property-image f i q Hi i' q'))
          ( is-equiv-is-image-is-image f i q i' q'
            ( hom-slice-universal-property-image f i q Hi i' q')
            ( Hi)
            ( Hi'))))

  equiv-slice-uniqueness-image : equiv-slice (map-emb i) (map-emb i')
  equiv-slice-uniqueness-image =
    pr1 (center uniqueness-image)

  hom-equiv-slice-uniqueness-image : hom-slice (map-emb i) (map-emb i')
  hom-equiv-slice-uniqueness-image =
    hom-equiv-slice (map-emb i) (map-emb i') (equiv-slice-uniqueness-image)

  map-hom-equiv-slice-uniqueness-image : B → B'
  map-hom-equiv-slice-uniqueness-image =
    map-hom-slice (map-emb i) (map-emb i') (hom-equiv-slice-uniqueness-image)

  is-equiv-map-hom-equiv-slice-uniqueness-image :
    is-equiv map-hom-equiv-slice-uniqueness-image
  is-equiv-map-hom-equiv-slice-uniqueness-image =
    is-equiv-map-equiv (pr1 equiv-slice-uniqueness-image)

  equiv-equiv-slice-uniqueness-image : B ≃ B'
  equiv-equiv-slice-uniqueness-image =
    pair map-hom-equiv-slice-uniqueness-image
         is-equiv-map-hom-equiv-slice-uniqueness-image

  triangle-hom-equiv-slice-uniqueness-image :
    (map-emb i) ~ (map-emb i' ∘ map-hom-equiv-slice-uniqueness-image)
  triangle-hom-equiv-slice-uniqueness-image =
    triangle-hom-slice
      ( map-emb i)
      ( map-emb i')
      ( hom-equiv-slice-uniqueness-image)

  htpy-equiv-slice-uniqueness-image :
    htpy-hom-slice f
      ( map-emb i')
      ( comp-hom-slice f
        ( map-emb i)
        ( map-emb i')
        ( hom-equiv-slice-uniqueness-image)
        ( q))
      ( q')
  htpy-equiv-slice-uniqueness-image =
    pr2 (center uniqueness-image)

  htpy-map-hom-equiv-slice-uniqueness-image :
    ( map-hom-equiv-slice-uniqueness-image ∘ map-hom-slice f (map-emb i) q) ~
    ( map-hom-slice f (map-emb i') q')
  htpy-map-hom-equiv-slice-uniqueness-image =
    pr1 htpy-equiv-slice-uniqueness-image

  tetrahedron-hom-equiv-slice-uniqueness-image :
    ( ( ( triangle-hom-slice f (map-emb i) q) ∙h
        ( ( triangle-hom-equiv-slice-uniqueness-image) ·r
          ( map-hom-slice f (map-emb i) q))) ∙h
      ( map-emb i' ·l htpy-map-hom-equiv-slice-uniqueness-image)) ~
    ( triangle-hom-slice f (map-emb i') q')
  tetrahedron-hom-equiv-slice-uniqueness-image =
    pr2 htpy-equiv-slice-uniqueness-image

fiberwise-map-is-image-im :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} (f : A → X) →
  (m : B ↪ X) (h : hom-slice f (map-emb m)) →
  (x : X) → type-trunc-Prop (fib f x) → fib (map-emb m) x
fiberwise-map-is-image-im f m h x =
  map-universal-property-trunc-Prop
    { A = (fib f x)}
    ( fib-emb-Prop m x)
    ( λ t →
      pair ( map-hom-slice f (map-emb m) h (pr1 t))
           ( ( inv (triangle-hom-slice f (map-emb m) h (pr1 t))) ∙
             ( pr2 t)))

map-is-image-im :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} (f : A → X) →
  (m : B ↪ X) (h : hom-slice f (map-emb m)) → im f → B
map-is-image-im f m h (pair x t) =
  pr1 (fiberwise-map-is-image-im f m h x t)

triangle-is-image-im :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} (f : A → X) →
  (m : B ↪ X) (h : hom-slice f (map-emb m)) →
  inclusion-im f ~ ((map-emb m) ∘ (map-is-image-im f m h))
triangle-is-image-im f m h (pair x t) =
  inv (pr2 (fiberwise-map-is-image-im f m h x t))

is-image-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  {l : Level} → is-image l f (emb-im f) (hom-slice-im f)
is-image-im f {l} =
  is-image-is-image'
    l f (emb-im f) (hom-slice-im f)
    ( λ B m h →
      pair ( map-is-image-im f m h)
           ( triangle-is-image-im f m h))

module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  (H : {l : Level} → is-image l f i q)
  where

  uniqueness-im :
    is-contr
      ( Σ ( equiv-slice (inclusion-im f) (map-emb i))
          ( λ e →
            htpy-hom-slice f
              ( map-emb i)
              ( comp-hom-slice f
                ( inclusion-im f)
                ( map-emb i)
                ( hom-equiv-slice (inclusion-im f) (map-emb i) e)
                ( hom-slice-im f))
              ( q)))
  uniqueness-im =
    uniqueness-image f (emb-im f) (hom-slice-im f) (is-image-im f) i q H

  equiv-slice-uniqueness-im : equiv-slice (inclusion-im f) (map-emb i)
  equiv-slice-uniqueness-im =
    pr1 (center uniqueness-im)

  hom-equiv-slice-uniqueness-im : hom-slice (inclusion-im f) (map-emb i)
  hom-equiv-slice-uniqueness-im =
    hom-equiv-slice (inclusion-im f) (map-emb i) equiv-slice-uniqueness-im

  map-hom-equiv-slice-uniqueness-im : im f → B
  map-hom-equiv-slice-uniqueness-im =
    map-hom-slice (inclusion-im f) (map-emb i) hom-equiv-slice-uniqueness-im

  is-equiv-map-hom-equiv-slice-uniqueness-im :
    is-equiv map-hom-equiv-slice-uniqueness-im
  is-equiv-map-hom-equiv-slice-uniqueness-im =
    is-equiv-map-equiv (pr1 equiv-slice-uniqueness-im)

  equiv-equiv-slice-uniqueness-im : im f ≃ B
  equiv-equiv-slice-uniqueness-im =
    pair map-hom-equiv-slice-uniqueness-im
         is-equiv-map-hom-equiv-slice-uniqueness-im

  triangle-hom-equiv-slice-uniqueness-im :
    (inclusion-im f) ~ (map-emb i ∘ map-hom-equiv-slice-uniqueness-im)
  triangle-hom-equiv-slice-uniqueness-im =
    triangle-hom-slice
      ( inclusion-im f)
      ( map-emb i)
      ( hom-equiv-slice-uniqueness-im)

  htpy-equiv-slice-uniqueness-im :
    htpy-hom-slice f
      ( map-emb i)
      ( comp-hom-slice f
        ( inclusion-im f)
        ( map-emb i)
        ( hom-equiv-slice-uniqueness-im)
        ( hom-slice-im f))
      ( q)
  htpy-equiv-slice-uniqueness-im =
    pr2 (center uniqueness-im)

  htpy-map-hom-equiv-slice-uniqueness-im :
    ( ( map-hom-equiv-slice-uniqueness-im) ∘
      ( map-hom-slice f (inclusion-im f) (hom-slice-im f))) ~
    ( map-hom-slice f (map-emb i) q)
  htpy-map-hom-equiv-slice-uniqueness-im =
    pr1 htpy-equiv-slice-uniqueness-im

  tetrahedron-hom-equiv-slice-uniqueness-im :
    ( ( ( triangle-hom-slice f (inclusion-im f) (hom-slice-im f)) ∙h
        ( ( triangle-hom-equiv-slice-uniqueness-im) ·r
          ( map-hom-slice f (inclusion-im f) (hom-slice-im f)))) ∙h
      ( map-emb i ·l htpy-map-hom-equiv-slice-uniqueness-im)) ~
    ( triangle-hom-slice f (map-emb i) q)
  tetrahedron-hom-equiv-slice-uniqueness-im =
    pr2 htpy-equiv-slice-uniqueness-im

is-equiv-is-emb-is-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-surjective f → is-emb f → is-equiv f
is-equiv-is-emb-is-surjective {f = f} H K =
  is-equiv-is-contr-map
    ( λ y →
      is-proof-irrelevant-is-prop
        ( is-prop-map-is-emb K y)
        ( apply-universal-property-trunc-Prop
          ( H y)
          ( fib-emb-Prop (pair f K) y)
          ( id)))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  where

  is-surjective-comp :
    is-surjective g → is-surjective h → is-surjective f
  is-surjective-comp Sg Sh x =
    apply-universal-property-trunc-Prop
      ( Sg x)
      ( trunc-Prop (fib f x))
      ( λ { (pair b refl) →
            apply-universal-property-trunc-Prop
              ( Sh b)
              ( trunc-Prop (fib f (g b)))
              ( λ { (pair a refl) →
                unit-trunc-Prop (pair a (H a))})})

  is-surjective-left-factor :
    is-surjective f → is-surjective g
  is-surjective-left-factor Sf x =
    apply-universal-property-trunc-Prop
      ( Sf x)
      ( trunc-Prop (fib g x))
      ( λ { (pair a refl) →
            unit-trunc-Prop (pair (h a) (inv (H a)))})

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {g : B → X}
  where

  is-surjective-comp' :
    {h : A → B} → is-surjective g → is-surjective h → is-surjective (g ∘ h)
  is-surjective-comp' {h} =
    is-surjective-comp (g ∘ h) g h refl-htpy

  is-surjective-left-factor' :
    (h : A → B) → is-surjective (g ∘ h) → is-surjective g
  is-surjective-left-factor' h =
    is-surjective-left-factor (g ∘ h) g h refl-htpy

--------------------------------------------------------------------------------

-- Finite types

count : {l : Level} → UU l → UU l
count X = Σ ℕ (λ k → Fin k ≃ X)

module _
  {l : Level} {X : UU l} (e : count X)
  where
  
  number-of-elements-count : ℕ
  number-of-elements-count = pr1 e
  
  equiv-count : Fin number-of-elements-count ≃ X
  equiv-count = pr2 e
  
  map-equiv-count : Fin number-of-elements-count → X
  map-equiv-count = map-equiv equiv-count
  
  map-inv-equiv-count : X → Fin number-of-elements-count
  map-inv-equiv-count = map-inv-equiv equiv-count
  
  inv-equiv-count : X ≃ Fin number-of-elements-count
  inv-equiv-count = inv-equiv equiv-count
  
  is-set-count : is-set X
  is-set-count =
    is-set-equiv'
      ( Fin number-of-elements-count)
      ( equiv-count)
      ( is-set-Fin number-of-elements-count)

is-empty-is-zero-number-of-elements-count :
  {l : Level} {X : UU l} (e : count X) →
  is-zero-ℕ (number-of-elements-count e) → is-empty X
is-empty-is-zero-number-of-elements-count (pair .zero-ℕ e) refl x =
  map-inv-equiv e x

is-zero-number-of-elements-count-is-empty :
  {l : Level} {X : UU l} (e : count X) →
  is-empty X → is-zero-ℕ (number-of-elements-count e)
is-zero-number-of-elements-count-is-empty (pair zero-ℕ e) H = refl
is-zero-number-of-elements-count-is-empty (pair (succ-ℕ k) e) H =
  ex-falso (H (map-equiv e zero-Fin))

count-is-empty :
  {l : Level} {X : UU l} → is-empty X → count X
count-is-empty H =
  pair zero-ℕ (inv-equiv (pair H (is-equiv-is-empty' H)))

count-Fin : (k : ℕ) → count (Fin k)
count-Fin k = pair k equiv-id

count-empty : count empty
count-empty = count-Fin zero-ℕ

count-is-contr :
  {l : Level} {X : UU l} → is-contr X → count X
count-is-contr H = pair one-ℕ (equiv-is-contr is-contr-Fin-one-ℕ H)

is-contr-is-one-number-of-elements-count :
  {l : Level} {X : UU l} (e : count X) →
  is-one-ℕ (number-of-elements-count e) → is-contr X
is-contr-is-one-number-of-elements-count (pair .(succ-ℕ zero-ℕ) e) refl =
  is-contr-equiv' (Fin one-ℕ) e is-contr-Fin-one-ℕ

is-one-number-of-elements-count-is-contr :
  {l : Level} {X : UU l} (e : count X) →
  is-contr X → is-one-ℕ (number-of-elements-count e)
is-one-number-of-elements-count-is-contr (pair zero-ℕ e) H =
  ex-falso (map-inv-equiv e (center H))
is-one-number-of-elements-count-is-contr (pair (succ-ℕ zero-ℕ) e) H =
  refl
is-one-number-of-elements-count-is-contr (pair (succ-ℕ (succ-ℕ k)) e) H =
  ex-falso
    ( Eq-Fin-eq
      ( is-injective-map-equiv e
        ( eq-is-contr' H (map-equiv e zero-Fin) (map-equiv e neg-one-Fin))))

count-unit : count unit
count-unit = count-is-contr is-contr-unit

equiv-count-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) (f : count X) →
  Fin (number-of-elements-count f) ≃ Y
equiv-count-equiv e f = e ∘e (equiv-count f)

count-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) → count X → count Y
count-equiv e f =
  pair (number-of-elements-count f) (equiv-count-equiv e f)

count-equiv' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) → count Y → count X
count-equiv' e = count-equiv (inv-equiv e)

count-is-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y} →
  is-equiv f → count X → count Y
count-is-equiv is-equiv-f = count-equiv (pair _ is-equiv-f)

count-is-equiv' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y} →
  is-equiv f → count Y → count X
count-is-equiv' is-equiv-f = count-equiv' (pair _ is-equiv-f)

has-decidable-equality-count :
  {l : Level} {X : UU l} → count X → has-decidable-equality X
has-decidable-equality-count (pair k e) =
  has-decidable-equality-equiv' e has-decidable-equality-Fin

cases-count-eq :
  {l : Level} {X : UU l} (d : has-decidable-equality X) {x y : X}
  (e : is-decidable (Id x y)) → count (Id x y)
cases-count-eq d {x} {y} (inl p) =
  count-is-contr
    ( is-proof-irrelevant-is-prop (is-set-has-decidable-equality d x y) p)
cases-count-eq d (inr f) =
  count-is-empty f

count-eq :
  {l : Level} {X : UU l} → has-decidable-equality X → (x y : X) → count (Id x y)
count-eq d x y = cases-count-eq d (d x y)

count-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  count X → count Y → count (coprod X Y)
count-coprod (pair k e) (pair l f) =
  pair
    ( add-ℕ k l)
    ( ( equiv-coprod e f) ∘e
      ( inv-equiv (coprod-Fin k l)))

number-of-elements-count-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : count X) (f : count Y) →
  Id ( number-of-elements-count (count-coprod e f))
     ( add-ℕ (number-of-elements-count e) (number-of-elements-count f))
number-of-elements-count-coprod (pair k e) (pair l f) = refl

count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (k : ℕ) (e : Fin k ≃ A) → ((x : A) → count (B x)) → count (Σ A B)
count-Σ' zero-ℕ e f =
  count-is-empty
    ( λ x →
      is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl (pr1 x))
count-Σ' {l1} {l2} {A} {B} (succ-ℕ k) e f =
  count-equiv
    ( ( equiv-Σ-equiv-base B e) ∘e
      ( ( inv-equiv
          ( right-distributive-Σ-coprod (Fin k) unit (B ∘ map-equiv e))) ∘e
        ( equiv-coprod
          ( equiv-id)
          ( inv-equiv
            ( left-unit-law-Σ (B ∘ (map-equiv e ∘ inr)))))))
    ( count-coprod
      ( count-Σ' k equiv-id (λ x → f (map-equiv e (inl x))))
      ( f (map-equiv e (inr star))))

equiv-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (k : ℕ) (e : Fin k ≃ A) (f : (x : A) → count (B x)) →
  Fin (number-of-elements-count (count-Σ' k e f)) ≃ Σ A B
equiv-count-Σ' k e f = pr2 (count-Σ' k e f)

count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → ((x : A) → count (B x)) → count (Σ A B)
count-Σ (pair k e) f =
  pair (number-of-elements-count (count-Σ' k e f)) (equiv-count-Σ' k e f)

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

mere-equiv-Prop :
  {l1 l2 : Level} → UU l1 → UU l2 → UU-Prop (l1 ⊔ l2)
mere-equiv-Prop X Y = trunc-Prop (X ≃ Y)

mere-equiv :
  {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
mere-equiv X Y = type-Prop (mere-equiv-Prop X Y)

is-prop-mere-equiv :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) → is-prop (mere-equiv X Y)
is-prop-mere-equiv X Y = is-prop-type-Prop (mere-equiv-Prop X Y)

refl-mere-equiv :
  {l1 : Level} (X : UU l1) → mere-equiv X X
refl-mere-equiv X = unit-trunc-Prop equiv-id

symmetric-mere-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → mere-equiv X Y → mere-equiv Y X
symmetric-mere-equiv {l1} {l2} {X} {Y} =
  map-universal-property-trunc-Prop
    ( mere-equiv-Prop Y X)
    ( λ e → unit-trunc-Prop (inv-equiv e))

transitive-mere-equiv :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} {Z : UU l3} →
  mere-equiv X Y → mere-equiv Y Z → mere-equiv X Z
transitive-mere-equiv {X = X} {Y} {Z} e f =
  apply-universal-property-trunc-Prop e
    ( mere-equiv-Prop X Z)
    ( λ e' →
      apply-universal-property-trunc-Prop f
        ( mere-equiv-Prop X Z)
        ( λ f' → unit-trunc-Prop (f' ∘e e')))

has-cardinality-Prop :
  {l : Level} → UU l → ℕ → UU-Prop l
has-cardinality-Prop X k = mere-equiv-Prop (Fin k) X

has-cardinality :
  {l : Level} → UU l → ℕ → UU l
has-cardinality X k = mere-equiv (Fin k) X

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

is-finite-Σ :
  {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} →
  is-finite X → ((x : X) → is-finite (Y x)) → is-finite (Σ X Y)
is-finite-Σ {X = X} {Y} is-finite-X is-finite-Y =
  apply-universal-property-trunc-Prop is-finite-X
    ( is-finite-Prop (Σ X Y))
    ( λ (e : count X) →
      apply-universal-property-trunc-Prop
        ( finite-choice is-finite-X is-finite-Y)
        ( is-finite-Prop (Σ X Y))
        ( is-finite-count ∘ (count-Σ e)))

count-prod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count X → count Y → count (X × Y)
count-prod (pair k e) (pair l f) =
  pair
    ( mul-ℕ k l)
    ( ( equiv-prod e f) ∘e
      ( inv-equiv (prod-Fin k l)))

number-of-elements-count-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (count-A : count A)
  (count-B : count B) →
  Id ( number-of-elements-count
       ( count-prod count-A count-B))
     ( mul-ℕ
       ( number-of-elements-count count-A)
       ( number-of-elements-count count-B))
number-of-elements-count-prod (pair k e) (pair l f) = refl

equiv-left-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (y : Y) →
  (Σ (X × Y) (λ t → Id (pr2 t) y)) ≃ X
equiv-left-factor {l1} {l2} {X} {Y} y =
  ( ( right-unit-law-prod) ∘e
    ( equiv-tot
      ( λ x → equiv-is-contr (is-contr-total-path' y) is-contr-unit))) ∘e
  ( assoc-Σ X (λ x → Y) (λ t → Id (pr2 t) y))

count-left-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (X × Y) → Y → count X
count-left-factor e y =
  count-equiv
    ( equiv-left-factor y)
    ( count-Σ e
      ( λ z →
        count-eq
          ( has-decidable-equality-right-factor
            ( has-decidable-equality-count e)
            ( pr1 z))
          ( pr2 z)
          ( y)))

count-right-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (X × Y) → X → count Y
count-right-factor e x =
  count-left-factor (count-equiv commutative-prod e) x

Π-ℕ : (k : ℕ) → (Fin k → ℕ) → ℕ
Π-ℕ zero-ℕ x = one-ℕ
Π-ℕ (succ-ℕ k) x = mul-ℕ (Π-ℕ k (λ i → x (inl i))) (x (inr star))

count-Π-Fin :
  {l1 : Level} {k : ℕ} {B : Fin k → UU l1} →
  ((x : Fin k) → count (B x)) → count ((x : Fin k) → B x)
count-Π-Fin {l1} {zero-ℕ} {B} e =
  count-is-contr (dependent-universal-property-empty' B)
count-Π-Fin {l1} {succ-ℕ k} {B} e =
  count-equiv'
    ( equiv-dependent-universal-property-coprod B)
    ( count-prod
      ( count-Π-Fin (λ x → e (inl x)))
      ( count-equiv'
        ( equiv-ev-star (B ∘ inr))
        ( e (inr star))))

count-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → ((x : A) → count (B x)) → count ((x : A) → B x)
count-Π {l1} {l2} {A} {B} e f =
  count-equiv'
    ( equiv-precomp-Π (equiv-count e) B)
    ( count-Π-Fin (λ x → f (map-equiv-count e x)))

count-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  count A → count B → count (A → B)
count-function-type e f =
  count-Π e (λ x → f)

is-finite-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-finite A → ((x : A) → is-finite (B x)) → is-finite ((x : A) → B x)
is-finite-Π {l1} {l2} {A} {B} f g =
  apply-universal-property-trunc-Prop f
    ( is-finite-Prop ((x : A) → B x))
    ( λ e →
      apply-universal-property-trunc-Prop
        ( finite-choice f g)
        ( is-finite-Prop ((x : A) → B x))
        ( λ h → unit-trunc-Prop (count-Π e h)))

𝔽 : UU (lsuc lzero)
𝔽 = Σ (UU lzero) is-finite

type-𝔽 : 𝔽 → UU lzero
type-𝔽 X = pr1 X

is-finite-type-𝔽 : (X : 𝔽) → is-finite (type-𝔽 X)
is-finite-type-𝔽 X = pr2 X

is-set-is-finite :
  {l : Level} {X : UU l} → is-finite X → is-set X
is-set-is-finite {l} {X} H =
  apply-universal-property-trunc-Prop H
    ( is-set-Prop X)
    ( λ e → is-set-count e)

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

has-decidable-equality-Prop :
  {l1 : Level} (X : UU l1) → UU-Prop l1
has-decidable-equality-Prop X =
  pair (has-decidable-equality X) is-prop-has-decidable-equality

has-decidable-equality-is-finite :
  {l1 : Level} {X : UU l1} → is-finite X → has-decidable-equality X
has-decidable-equality-is-finite {l1} {X} is-finite-X =
  apply-universal-property-trunc-Prop is-finite-X
    ( has-decidable-equality-Prop X)
    ( λ e →
      has-decidable-equality-equiv' (equiv-count e) has-decidable-equality-Fin)

has-decidable-equality-has-cardinality :
  {l1 : Level} {X : UU l1} {k : ℕ} →
  has-cardinality X k → has-decidable-equality X
has-decidable-equality-has-cardinality {l1} {X} {k} H =
  apply-universal-property-trunc-Prop H
    ( has-decidable-equality-Prop X)
    ( λ e → has-decidable-equality-equiv' e has-decidable-equality-Fin)

is-finite-eq :
  {l1 : Level} {X : UU l1} →
  has-decidable-equality X → {x y : X} → is-finite (Id x y)
is-finite-eq d {x} {y} = is-finite-count (count-eq d x y)

Id-𝔽 : (X : 𝔽) (x y : type-𝔽 X) → 𝔽
Id-𝔽 X x y =
  pair ( Id x y)
       ( is-finite-eq (has-decidable-equality-is-finite (is-finite-type-𝔽 X)))

is-finite-prod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  is-finite X → is-finite Y → is-finite (X × Y)
is-finite-prod {X = X} {Y} is-finite-X is-finite-Y =
  apply-universal-property-trunc-Prop is-finite-X
    ( is-finite-Prop (X × Y))
    ( λ (e : count X) →
      apply-universal-property-trunc-Prop is-finite-Y
        ( is-finite-Prop (X × Y))
        ( is-finite-count ∘ (count-prod e)))

prod-𝔽 : 𝔽 → 𝔽 → 𝔽
prod-𝔽 X Y =
  pair ( prod (type-𝔽 X) (type-𝔽 Y))
       ( is-finite-prod (is-finite-type-𝔽 X) (is-finite-type-𝔽 Y))

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

Π-𝔽 : (A : 𝔽) (B : type-𝔽 A → 𝔽) → 𝔽
Π-𝔽 A B =
  pair ( (x : type-𝔽 A) → type-𝔽 (B x))
       ( is-finite-Π (is-finite-type-𝔽 A) (λ x → is-finite-type-𝔽 (B x)))

is-finite-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-finite A → is-finite B → is-finite (A → B)
is-finite-function-type f g = is-finite-Π f (λ x → g)

_→-𝔽_ : 𝔽 → 𝔽 → 𝔽
A →-𝔽 B =
  pair ( type-𝔽 A → type-𝔽 B)
       ( is-finite-function-type (is-finite-type-𝔽 A) (is-finite-type-𝔽 B))

is-finite-≃ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-finite A → is-finite B → is-finite (A ≃ B)
is-finite-≃ f g =
  is-finite-Σ
    ( is-finite-function-type f g)
    ( λ h →
      is-finite-prod
        ( is-finite-Σ
          ( is-finite-function-type g f)
          ( λ k →
            is-finite-Π g
              ( λ y → is-finite-eq (has-decidable-equality-is-finite g))))
        ( is-finite-Σ
          ( is-finite-function-type g f)
          ( λ k →
            is-finite-Π f
              ( λ x → is-finite-eq (has-decidable-equality-is-finite f)))))

_≃-𝔽_ : 𝔽 → 𝔽 → 𝔽
A ≃-𝔽 B =
  pair ( type-𝔽 A ≃ type-𝔽 B)
       ( is-finite-≃ (is-finite-type-𝔽 A) (is-finite-type-𝔽 B))

Aut-𝔽 : 𝔽 → 𝔽
Aut-𝔽 A = A ≃-𝔽 A

UU-Fin-Level : (l : Level) → ℕ → UU (lsuc l)
UU-Fin-Level l k = Σ (UU l) (mere-equiv (Fin k))

type-UU-Fin-Level : {l : Level} {k : ℕ} → UU-Fin-Level l k → UU l
type-UU-Fin-Level X = pr1 X

mere-equiv-UU-Fin-Level :
  {l : Level} {k : ℕ} (X : UU-Fin-Level l k) → mere-equiv (Fin k) (type-UU-Fin-Level X)
mere-equiv-UU-Fin-Level X = pr2 X

UU-Fin : ℕ → UU (lsuc lzero)
UU-Fin k = UU-Fin-Level lzero k

type-UU-Fin : {k : ℕ} → UU-Fin k → UU lzero
type-UU-Fin X = pr1 X

Maybe : {l : Level} → UU l → UU l
Maybe X = coprod X unit

unit-Maybe : {l : Level} {X : UU l} → X → Maybe X
unit-Maybe = inl

is-emb-unit-Maybe : {l : Level} {X : UU l} → is-emb (unit-Maybe {X = X})
is-emb-unit-Maybe {l} {X} = is-emb-inl X unit

is-injective-unit-Maybe :
  {l : Level} {X : UU l} → is-injective (unit-Maybe {X = X})
is-injective-unit-Maybe = is-injective-inl

exception-Maybe : {l : Level} {X : UU l} → Maybe X
exception-Maybe {l} {X} = inr star

is-exception-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-exception-Maybe {l} {X} x = Id x exception-Maybe

is-not-exception-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-not-exception-Maybe x = ¬ (is-exception-Maybe x)

is-not-exception-unit-Maybe :
  {l : Level} {X : UU l} (x : X) → is-not-exception-Maybe (unit-Maybe x)
is-not-exception-unit-Maybe {l} {X} x = neq-inl-inr x star

is-decidable-is-exception-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-decidable (is-exception-Maybe x)
is-decidable-is-exception-Maybe {l} {X} (inl x) =
  inr
    (λ p → ex-falso (map-inv-raise (Eq-eq-coprod X unit (inl x) (inr star) p)))
is-decidable-is-exception-Maybe (inr star) = inl refl

is-decidable-is-not-exception-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-decidable (is-not-exception-Maybe x)
is-decidable-is-not-exception-Maybe x =
  is-decidable-neg (is-decidable-is-exception-Maybe x)

is-value-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-value-Maybe {l} {X} x = Σ X (λ y → Id (inl y) x)

value-is-value-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-value-Maybe x → X
value-is-value-Maybe x = pr1

eq-is-value-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) (H : is-value-Maybe x) →
  Id (inl (value-is-value-Maybe x H)) x
eq-is-value-Maybe x H = pr2 H

decide-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) →
  coprod (is-value-Maybe x) (is-exception-Maybe x)
decide-Maybe (inl x) = inl (pair x refl)
decide-Maybe (inr star) = inr refl

is-value-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) →
  is-not-exception-Maybe x → is-value-Maybe x
is-value-is-not-exception-Maybe x H =
  map-right-unit-law-coprod-is-empty (is-value-Maybe x) (is-exception-Maybe x) H (decide-Maybe x)

value-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) → is-not-exception-Maybe x → X
value-is-not-exception-Maybe x H =
  value-is-value-Maybe x (is-value-is-not-exception-Maybe x H)

eq-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) (H : is-not-exception-Maybe x) →
  Id (inl (value-is-not-exception-Maybe x H)) x
eq-is-not-exception-Maybe x H =
  eq-is-value-Maybe x (is-value-is-not-exception-Maybe x H)

is-not-exception-is-value-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) →
  is-value-Maybe x → is-not-exception-Maybe x
is-not-exception-is-value-Maybe {l1} {X} .(inl x) (pair x refl) =
  is-not-exception-unit-Maybe x

is-not-exception-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) → is-exception-Maybe (f (inl x)) →
  is-not-exception-Maybe (f exception-Maybe)
is-not-exception-injective-map-exception-Maybe is-inj-f x p q =
  is-not-exception-unit-Maybe x (is-inj-f (p ∙ inv q))

is-not-exception-map-equiv-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-exception-Maybe (map-equiv e (inl x)) →
  is-not-exception-Maybe (map-equiv e exception-Maybe)
is-not-exception-map-equiv-exception-Maybe e =
  is-not-exception-injective-map-exception-Maybe (is-injective-map-equiv e)

is-value-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) → is-exception-Maybe (f (inl x)) →
  is-value-Maybe (f exception-Maybe)
is-value-injective-map-exception-Maybe {f = f} is-inj-f x H =
  is-value-is-not-exception-Maybe
    ( f exception-Maybe)
    ( is-not-exception-injective-map-exception-Maybe is-inj-f x H)

value-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) → is-exception-Maybe (f (inl x)) → Y
value-injective-map-exception-Maybe {f = f} is-inj-f x H =
  value-is-value-Maybe
    ( f exception-Maybe)
    ( is-value-injective-map-exception-Maybe is-inj-f x H)

comp-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) (H : is-exception-Maybe (f (inl x))) →
  Id ( inl (value-injective-map-exception-Maybe is-inj-f x H))
     ( f exception-Maybe)
comp-injective-map-exception-Maybe {f = f} is-inj-f x H =
  eq-is-value-Maybe
    ( f exception-Maybe)
    ( is-value-injective-map-exception-Maybe is-inj-f x H)

is-not-exception-emb-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ↪ Maybe Y)
  (x : X) → is-exception-Maybe (map-emb e (inl x)) →
  is-not-exception-Maybe (map-emb e exception-Maybe)
is-not-exception-emb-exception-Maybe e =
  is-not-exception-injective-map-exception-Maybe (is-injective-emb e)

is-value-map-equiv-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-exception-Maybe (map-equiv e (inl x)) →
  is-value-Maybe (map-equiv e exception-Maybe)
is-value-map-equiv-exception-Maybe e x H =
  is-value-is-not-exception-Maybe
    ( map-equiv e exception-Maybe)
    ( is-not-exception-map-equiv-exception-Maybe e x H)

value-map-equiv-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-exception-Maybe (map-equiv e (inl x)) → Y
value-map-equiv-exception-Maybe e x H =
  value-is-value-Maybe
    ( map-equiv e exception-Maybe)
    ( is-value-map-equiv-exception-Maybe e x H)

comp-map-equiv-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  (H : is-exception-Maybe (map-equiv e (inl x))) →
  Id ( inl (value-map-equiv-exception-Maybe e x H))
     ( map-equiv e exception-Maybe)
comp-map-equiv-exception-Maybe e x H =
  eq-is-value-Maybe
    ( map-equiv e exception-Maybe)
    ( is-value-map-equiv-exception-Maybe e x H)

restrict-injective-map-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) (u : Maybe Y) (p : Id (f (inl x)) u) → Y
restrict-injective-map-Maybe' {f = f} is-inj-f x (inl y) p = y
restrict-injective-map-Maybe' {f = f} is-inj-f x (inr star) p =
  value-injective-map-exception-Maybe is-inj-f x p

restrict-injective-map-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → X → Y
restrict-injective-map-Maybe {f = f} is-inj-f x =
  restrict-injective-map-Maybe' is-inj-f x (f (inl x)) refl

comp-restrict-injective-map-is-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) (u : Maybe Y) (p : Id (f (inl x)) u) →
  is-exception-Maybe (f (inl x)) →
  Id (inl (restrict-injective-map-Maybe' is-inj-f x u p)) (f exception-Maybe)
comp-restrict-injective-map-is-exception-Maybe' {f = f} is-inj-f x (inl y) p q =
  ex-falso (is-not-exception-unit-Maybe y (inv p ∙ q))
comp-restrict-injective-map-is-exception-Maybe' {f = f} is-inj-f x (inr star) p q =
  comp-injective-map-exception-Maybe is-inj-f x p

comp-restrict-injective-map-is-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) → is-exception-Maybe (f (inl x)) →
  Id (inl (restrict-injective-map-Maybe is-inj-f x)) (f exception-Maybe)
comp-restrict-injective-map-is-exception-Maybe {f = f} is-inj-f x =
  comp-restrict-injective-map-is-exception-Maybe' is-inj-f x (f (inl x)) refl

comp-restrict-injective-map-is-not-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) (u : Maybe Y) (p : Id (f (inl x)) u) →
  is-not-exception-Maybe (f (inl x)) →
  Id (inl (restrict-injective-map-Maybe' is-inj-f x u p)) (f (inl x))
comp-restrict-injective-map-is-not-exception-Maybe' is-inj-f x (inl y) p H =
  inv p
comp-restrict-injective-map-is-not-exception-Maybe' is-inj-f x (inr star) p H =
  ex-falso (H p)

comp-restrict-injective-map-is-not-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) → is-not-exception-Maybe (f (inl x)) →
  Id (inl (restrict-injective-map-Maybe is-inj-f x)) (f (inl x))
comp-restrict-injective-map-is-not-exception-Maybe {f = f} is-inj-f x =
  comp-restrict-injective-map-is-not-exception-Maybe' is-inj-f x (f (inl x))
    refl

map-equiv-equiv-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y)
  (x : X) (u : Maybe Y) (p : Id (map-equiv e (inl x)) u) → Y
map-equiv-equiv-Maybe' e =
  restrict-injective-map-Maybe' (is-injective-map-equiv e)

map-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) → X → Y
map-equiv-equiv-Maybe e =
  restrict-injective-map-Maybe (is-injective-map-equiv e)

comp-map-equiv-equiv-is-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  (u : Maybe Y) (p : Id (map-equiv e (inl x)) u) →
  is-exception-Maybe (map-equiv e (inl x)) →
  Id (inl (map-equiv-equiv-Maybe' e x u p)) (map-equiv e exception-Maybe)
comp-map-equiv-equiv-is-exception-Maybe' e =
  comp-restrict-injective-map-is-exception-Maybe' (is-injective-map-equiv e)

comp-map-equiv-equiv-is-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-exception-Maybe (map-equiv e (inl x)) →
  Id (inl (map-equiv-equiv-Maybe e x)) (map-equiv e exception-Maybe)
comp-map-equiv-equiv-is-exception-Maybe e x =
  comp-map-equiv-equiv-is-exception-Maybe' e x (map-equiv e (inl x)) refl

comp-map-equiv-equiv-is-not-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  (u : Maybe Y) (p : Id (map-equiv e (inl x)) u) →
  is-not-exception-Maybe (map-equiv e (inl x)) →
  Id (inl (map-equiv-equiv-Maybe' e x u p)) (map-equiv e (inl x))
comp-map-equiv-equiv-is-not-exception-Maybe' e x (inl y) p H =
  inv p
comp-map-equiv-equiv-is-not-exception-Maybe' e x (inr star) p H =
  ex-falso (H p)

comp-map-equiv-equiv-is-not-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-not-exception-Maybe (map-equiv e (inl x)) →
  Id (inl (map-equiv-equiv-Maybe e x)) (map-equiv e (inl x))
comp-map-equiv-equiv-is-not-exception-Maybe e x =
  comp-map-equiv-equiv-is-not-exception-Maybe' e x (map-equiv e (inl x)) refl

map-inv-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) → Y → X
map-inv-equiv-equiv-Maybe e =
  map-equiv-equiv-Maybe (inv-equiv e)

comp-map-inv-equiv-equiv-is-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (y : Y) →
  is-exception-Maybe (map-inv-equiv e (inl y)) →
  Id (inl (map-inv-equiv-equiv-Maybe e y)) (map-inv-equiv e exception-Maybe)
comp-map-inv-equiv-equiv-is-exception-Maybe e =
  comp-map-equiv-equiv-is-exception-Maybe (inv-equiv e)

comp-map-inv-equiv-equiv-is-not-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (y : Y) →
  ( f : is-not-exception-Maybe (map-inv-equiv e (inl y))) →
  Id (inl (map-inv-equiv-equiv-Maybe e y)) (map-inv-equiv e (inl y))
comp-map-inv-equiv-equiv-is-not-exception-Maybe e =
  comp-map-equiv-equiv-is-not-exception-Maybe (inv-equiv e)

issec-map-inv-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) →
  (map-equiv-equiv-Maybe e ∘ map-inv-equiv-equiv-Maybe e) ~ id
issec-map-inv-equiv-equiv-Maybe e y with
  is-decidable-is-exception-Maybe (map-inv-equiv e (inl y))
... | inl p =
  is-injective-unit-Maybe
    ( ( comp-map-equiv-equiv-is-exception-Maybe e
        ( map-inv-equiv-equiv-Maybe e y)
        ( ( ap
            ( map-equiv e)
            ( comp-map-inv-equiv-equiv-is-exception-Maybe e y p)) ∙
          ( issec-map-inv-equiv e exception-Maybe))) ∙
      ( ( ap (map-equiv e) (inv p)) ∙
        ( issec-map-inv-equiv e (inl y))))
... | inr f =
  is-injective-unit-Maybe
    ( ( comp-map-equiv-equiv-is-not-exception-Maybe e
        ( map-inv-equiv-equiv-Maybe e y)
        ( is-not-exception-is-value-Maybe
          ( map-equiv e (inl (map-inv-equiv-equiv-Maybe e y)))
          ( pair y
            ( inv
              ( ( ap
                  ( map-equiv e)
                  ( comp-map-inv-equiv-equiv-is-not-exception-Maybe e y f)) ∙
                ( issec-map-inv-equiv e (inl y))))))) ∙
      ( ( ap
          ( map-equiv e)
          ( comp-map-inv-equiv-equiv-is-not-exception-Maybe e y f)) ∙
        ( issec-map-inv-equiv e (inl y))))

isretr-map-inv-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) →
  (map-inv-equiv-equiv-Maybe e ∘ map-equiv-equiv-Maybe e) ~ id
isretr-map-inv-equiv-equiv-Maybe e x with
  is-decidable-is-exception-Maybe (map-equiv e (inl x))
... | inl p =
  is-injective-unit-Maybe
    ( ( comp-map-inv-equiv-equiv-is-exception-Maybe e
        ( map-equiv-equiv-Maybe e x)
        ( ( ap ( map-inv-equiv e)
               ( comp-map-equiv-equiv-is-exception-Maybe e x p)) ∙
          ( isretr-map-inv-equiv e exception-Maybe))) ∙
      ( ( ap (map-inv-equiv e) (inv p)) ∙
        ( isretr-map-inv-equiv e (inl x))))
... | inr f =
  is-injective-unit-Maybe
    ( ( comp-map-inv-equiv-equiv-is-not-exception-Maybe e
        ( map-equiv-equiv-Maybe e x)
        ( is-not-exception-is-value-Maybe
          ( map-inv-equiv e (inl (map-equiv-equiv-Maybe e x)))
          ( pair x
            ( inv
              ( ( ap (map-inv-equiv e)
                     ( comp-map-equiv-equiv-is-not-exception-Maybe e x f)) ∙
                ( isretr-map-inv-equiv e (inl x))))))) ∙
      ( ( ap ( map-inv-equiv e)
             ( comp-map-equiv-equiv-is-not-exception-Maybe e x f)) ∙
        ( isretr-map-inv-equiv e (inl x))))

is-equiv-map-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) →
  is-equiv (map-equiv-equiv-Maybe e)
is-equiv-map-equiv-equiv-Maybe e =
  is-equiv-has-inverse
    ( map-inv-equiv-equiv-Maybe e)
    ( issec-map-inv-equiv-equiv-Maybe e)
    ( isretr-map-inv-equiv-equiv-Maybe e)

equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (Maybe X ≃ Maybe Y) → (X ≃ Y)
equiv-equiv-Maybe e =
  pair (map-equiv-equiv-Maybe e) (is-equiv-map-equiv-equiv-Maybe e)

is-injective-Fin : {k l : ℕ} → (Fin k ≃ Fin l) → Id k l
is-injective-Fin {zero-ℕ} {zero-ℕ} e = refl
is-injective-Fin {zero-ℕ} {succ-ℕ l} e = ex-falso (map-inv-equiv e zero-Fin)
is-injective-Fin {succ-ℕ k} {zero-ℕ} e = ex-falso (map-equiv e zero-Fin)
is-injective-Fin {succ-ℕ k} {succ-ℕ l} e =
  ap succ-ℕ (is-injective-Fin (equiv-equiv-Maybe e))

double-counting-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (count-A : count A)
  (count-B : count B) (e : A ≃ B) →
  Id (number-of-elements-count count-A) (number-of-elements-count count-B)
double-counting-equiv (pair k f) (pair l g) e =
  is-injective-Fin ((inv-equiv g ∘e e) ∘e f)

double-counting :
  {l : Level} {A : UU l} (count-A count-A' : count A) →
  Id (number-of-elements-count count-A) (number-of-elements-count count-A')
double-counting count-A count-A' =
  double-counting-equiv count-A count-A' equiv-id

count-Maybe : {l : Level} {X : UU l} → count X → count (Maybe X)
count-Maybe {l} {X} e = count-coprod e count-unit

is-nonzero-number-of-elements-count-Maybe :
  {l : Level} {X : UU l} (e : count (Maybe X)) →
  is-nonzero-ℕ (number-of-elements-count e)
is-nonzero-number-of-elements-count-Maybe e p =
  is-empty-is-zero-number-of-elements-count e p exception-Maybe

is-successor-number-of-elements-count-Maybe :
  {l : Level} {X : UU l} (e : count (Maybe X)) →
  is-successor-ℕ (number-of-elements-count e)
is-successor-number-of-elements-count-Maybe e =
  is-successor-is-nonzero-ℕ (is-nonzero-number-of-elements-count-Maybe e)

count-count-Maybe :
  {l : Level} {X : UU l} → count (Maybe X) → count X
count-count-Maybe (pair k e) with
  is-successor-number-of-elements-count-Maybe (pair k e)
... | pair l refl = pair l (equiv-equiv-Maybe e)

sum-Fin-ℕ : {k : ℕ} → (Fin k → ℕ) → ℕ
sum-Fin-ℕ {zero-ℕ} f = zero-ℕ
sum-Fin-ℕ {succ-ℕ k} f = add-ℕ (sum-Fin-ℕ (λ x → f (inl x))) (f (inr star))

htpy-sum-Fin-ℕ :
  {k : ℕ} {f g : Fin k → ℕ} (H : f ~ g) → Id (sum-Fin-ℕ f) (sum-Fin-ℕ g)
htpy-sum-Fin-ℕ {zero-ℕ} H = refl
htpy-sum-Fin-ℕ {succ-ℕ k} H =
  ap-add-ℕ
    ( htpy-sum-Fin-ℕ (λ x → H (inl x)))
    ( H (inr star))

constant-sum-Fin-ℕ :
  (m n : ℕ) → Id (sum-Fin-ℕ (const (Fin m) ℕ n)) (mul-ℕ m n)
constant-sum-Fin-ℕ zero-ℕ n = refl
constant-sum-Fin-ℕ (succ-ℕ m) n = ap (add-ℕ' n) (constant-sum-Fin-ℕ m n)

sum-count-ℕ : {l : Level} {A : UU l} (e : count A) → (f : A → ℕ) → ℕ
sum-count-ℕ (pair k e) f = sum-Fin-ℕ (f ∘ (map-equiv e))

ap-sum-count-ℕ :
  {l : Level} {A : UU l} (e : count A) {f g : A → ℕ} (H : f ~ g) →
  Id (sum-count-ℕ e f) (sum-count-ℕ e g)
ap-sum-count-ℕ (pair k e) H = htpy-sum-Fin-ℕ (H ·r (map-equiv e))

constant-sum-count-ℕ :
  {l : Level} {A : UU l} (e : count A) (n : ℕ) →
  Id (sum-count-ℕ e (const A ℕ n)) (mul-ℕ (number-of-elements-count e) n)
constant-sum-count-ℕ (pair m e) n = constant-sum-Fin-ℕ m n

number-of-elements-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (k : ℕ) (e : Fin k ≃ A) →
  (f : (x : A) → count (B x)) →
  Id ( number-of-elements-count (count-Σ' k e f))
     ( sum-Fin-ℕ (λ x → number-of-elements-count (f (map-equiv e x)))) 
number-of-elements-count-Σ' zero-ℕ e f = refl
number-of-elements-count-Σ' (succ-ℕ k) e f =
  ( number-of-elements-count-coprod
    ( count-Σ' k equiv-id (λ x → f (map-equiv e (inl x))))
    ( f (map-equiv e (inr star)))) ∙
  ( ap
    ( add-ℕ' (number-of-elements-count (f (map-equiv e (inr star)))))
    ( number-of-elements-count-Σ' k equiv-id (λ x → f (map-equiv e (inl x)))))

number-of-elements-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (e : count A)
  (f : (x : A) → count (B x)) →
  Id ( number-of-elements-count (count-Σ e f))
     ( sum-count-ℕ e (λ x → number-of-elements-count (f x)))
number-of-elements-count-Σ (pair k e) f = number-of-elements-count-Σ' k e f

double-counting-coprod :
  { l1 l2 : Level} {A : UU l1} {B : UU l2}
  ( count-A : count A) (count-B : count B) (count-C : count (coprod A B)) →
  Id ( number-of-elements-count count-C)
     ( add-ℕ
       ( number-of-elements-count count-A)
       ( number-of-elements-count count-B))
double-counting-coprod count-A count-B count-C =
  ( double-counting count-C (count-coprod count-A count-B)) ∙
  ( number-of-elements-count-coprod count-A count-B)

double-counting-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
  (count-B : (x : A) → count (B x)) (count-C : count (Σ A B)) →
  Id ( number-of-elements-count count-C)
     ( sum-count-ℕ count-A (λ x → number-of-elements-count (count-B x)))
double-counting-Σ count-A count-B count-C =
  ( double-counting count-C (count-Σ count-A count-B)) ∙
  ( number-of-elements-count-Σ count-A count-B)

count-fiber-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → count (Σ A B) → (x : A) → count (B x)
count-fiber-count-Σ {B = B} e f x =
  count-equiv
    ( equiv-fib-pr1 x)
    ( count-Σ f
      ( λ z → count-eq (has-decidable-equality-count e) (pr1 z) x))

count-fib :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  count A → count B → (y : B) → count (fib f y)
count-fib f count-A count-B =
  count-fiber-count-Σ count-B (count-equiv' (equiv-total-fib f) count-A)

sum-number-of-elements-count-fiber-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (e : count A)
  (f : count (Σ A B)) →
  Id ( sum-count-ℕ e
       ( λ x → number-of-elements-count (count-fiber-count-Σ e f x)))
     ( number-of-elements-count f)
sum-number-of-elements-count-fiber-count-Σ e f =
  ( inv (number-of-elements-count-Σ e (λ x → count-fiber-count-Σ e f x))) ∙
  ( double-counting (count-Σ e (λ x → count-fiber-count-Σ e f x)) f)

double-counting-fiber-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
  (count-B : (x : A) → count (B x)) (count-C : count (Σ A B)) (x : A) →
  Id ( number-of-elements-count (count-B x))
     ( number-of-elements-count (count-fiber-count-Σ count-A count-C x))
double-counting-fiber-count-Σ count-A count-B count-C x =
  double-counting (count-B x) (count-fiber-count-Σ count-A count-C x)

sum-number-of-elements-count-fib :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (count-A : count A) (count-B : count B) →
  Id ( sum-count-ℕ count-B
       ( λ x → number-of-elements-count (count-fib f count-A count-B x)))
     ( number-of-elements-count count-A)
sum-number-of-elements-count-fib f count-A count-B =
  sum-number-of-elements-count-fiber-count-Σ count-B
    ( count-equiv' (equiv-total-fib f) count-A)

double-counting-fib :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (count-A : count A) →
  (count-B : count B) (count-fib-f : (y : B) → count (fib f y)) (y : B) →
  Id ( number-of-elements-count (count-fib-f y))
     ( number-of-elements-count (count-fib f count-A count-B y))
double-counting-fib f count-A count-B count-fib-f y =
  double-counting (count-fib-f y) (count-fib f count-A count-B y)

equiv-total-fib-map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  Σ (Σ A B) (fib (map-section b)) ≃ A
equiv-total-fib-map-section b = equiv-total-fib (map-section b)

count-fib-map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  count (Σ A B) → ((x : A) → count (B x)) →
  (t : Σ A B) → count (fib (map-section b) t)
count-fib-map-section {l1} {l2} {A} {B} b e f (pair y z) =
  count-equiv'
    ( ( ( left-unit-law-Σ-is-contr
            ( is-contr-total-path' y)
            ( pair y refl)) ∘e
        ( inv-assoc-Σ A
          ( λ x → Id x y)
          ( λ t → Id (tr B (pr2 t) (b (pr1 t))) z))) ∘e
      ( equiv-tot (λ x → equiv-pair-eq-Σ (pair x (b x)) (pair y z))))
    ( count-eq (has-decidable-equality-count (f y)) (b y) z)

count-base-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  count (Σ A B) → ((x : A) → count (B x)) → count A
count-base-count-Σ b e f =
  count-equiv
    ( equiv-total-fib-map-section b)
    ( count-Σ e (count-fib-map-section b e f))

sum-number-of-elements-count-base-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  (count-ΣAB : count (Σ A B)) (count-B : (x : A) → count (B x)) →
  Id ( sum-count-ℕ
       ( count-base-count-Σ b count-ΣAB count-B)
       ( λ x → number-of-elements-count (count-B x)))
     ( number-of-elements-count count-ΣAB)
sum-number-of-elements-count-base-count-Σ b count-ΣAB count-B =
  ( inv
    ( number-of-elements-count-Σ
      ( count-base-count-Σ b count-ΣAB count-B)
      ( count-B))) ∙
  ( double-counting
    ( count-Σ (count-base-count-Σ b count-ΣAB count-B) count-B)
    ( count-ΣAB))

double-counting-base-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  (count-A : count A) (count-B : (x : A) → count (B x))
  (count-ΣAB : count (Σ A B)) →
  Id ( number-of-elements-count (count-base-count-Σ b count-ΣAB count-B))
     ( number-of-elements-count count-A)
double-counting-base-count-Σ b count-A count-B count-ΣAB =
  double-counting (count-base-count-Σ b count-ΣAB count-B) count-A

section-count-base-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count (Σ A B) →
  (f : (x : A) → count (B x)) →
  count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (f x)))) →
  (x : A) → coprod (B x) (is-zero-ℕ (number-of-elements-count (f x)))
section-count-base-count-Σ' e f g x with
  is-decidable-is-zero-ℕ (number-of-elements-count (f x))
... | inl p = inr p
... | inr H with is-successor-is-nonzero-ℕ H
... | (pair k p) = inl (map-equiv-count (f x) (tr Fin (inv p) zero-Fin))

count-base-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count (Σ A B) →
  (f : (x : A) → count (B x)) →
  count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (f x)))) → count A
count-base-count-Σ' {l1} {l2} {A} {B} e f g =
  count-base-count-Σ
    ( section-count-base-count-Σ' e f g)
    ( count-equiv'
      ( left-distributive-Σ-coprod A B
        ( λ x → is-zero-ℕ (number-of-elements-count (f x))))
      ( count-coprod e g))
    ( λ x →
      count-coprod
        ( f x)
        ( count-eq has-decidable-equality-ℕ
          ( number-of-elements-count (f x))
          ( zero-ℕ)))

sum-number-of-elements-count-base-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-ΣAB : count (Σ A B)) →
  ( count-B : (x : A) → count (B x)) →
  ( count-nB :
    count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (count-B x))))) →
  Id ( sum-count-ℕ
       ( count-base-count-Σ' count-ΣAB count-B count-nB)
       ( λ x → number-of-elements-count (count-B x)))
     ( number-of-elements-count count-ΣAB)
sum-number-of-elements-count-base-count-Σ' count-ΣAB count-B count-nB =
  ( inv
    ( number-of-elements-count-Σ
      ( count-base-count-Σ' count-ΣAB count-B count-nB)
      ( count-B))) ∙
  ( double-counting
    ( count-Σ
      ( count-base-count-Σ' count-ΣAB count-B count-nB)
      ( count-B))
    ( count-ΣAB))

double-counting-base-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
  ( count-B : (x : A) → count (B x)) (count-ΣAB : count (Σ A B)) →
  ( count-nB :
    count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (count-B x))))) →
  Id ( number-of-elements-count
       ( count-base-count-Σ' count-ΣAB count-B count-nB))
     ( number-of-elements-count count-A)
double-counting-base-count-Σ' count-A count-B count-ΣAB count-nB =
  double-counting (count-base-count-Σ' count-ΣAB count-B count-nB) count-A

is-left : {l1 l2 : Level} {X : UU l1} {Y : UU l2} → coprod X Y → UU lzero
is-left (inl x) = unit
is-left (inr x) = empty

equiv-left-summand :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (Σ (coprod X Y) is-left) ≃ X
equiv-left-summand {l1} {l2} {X} {Y} =
  ( ( right-unit-law-coprod X) ∘e
    ( equiv-coprod right-unit-law-prod (right-absorption-prod Y))) ∘e
  ( right-distributive-Σ-coprod X Y is-left)

count-is-left :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (t : coprod X Y) → count (is-left t)
count-is-left (inl x) = count-unit
count-is-left (inr x) = count-empty

count-left-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (coprod X Y) → count X
count-left-coprod e = count-equiv equiv-left-summand (count-Σ e count-is-left)

is-right : {l1 l2 : Level} {X : UU l1} {Y : UU l2} → coprod X Y → UU lzero
is-right (inl x) = empty
is-right (inr x) = unit

equiv-right-summand :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (Σ (coprod X Y) is-right) ≃ Y
equiv-right-summand {l1} {l2} {X} {Y} =
  ( ( left-unit-law-coprod Y) ∘e
    ( equiv-coprod (right-absorption-prod X) right-unit-law-prod)) ∘e
    ( right-distributive-Σ-coprod X Y is-right)

count-is-right :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (t : coprod X Y) → count (is-right t)
count-is-right (inl x) = count-empty
count-is-right (inr x) = count-unit

count-right-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (coprod X Y) → count Y
count-right-coprod e =
  count-equiv equiv-right-summand (count-Σ e count-is-right)

sum-number-of-elements-coprod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : count (coprod A B)) →
  Id ( add-ℕ ( number-of-elements-count (count-left-coprod e))
             ( number-of-elements-count (count-right-coprod e)))
     ( number-of-elements-count e)
sum-number-of-elements-coprod e =
  ( inv
    ( number-of-elements-count-coprod
      ( count-left-coprod e)
      ( count-right-coprod e))) ∙
  ( inv
    ( double-counting-coprod (count-left-coprod e) (count-right-coprod e) e))

product-number-of-elements-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (count-AB : count (A × B)) →
  (a : A) (b : B) →
  Id ( mul-ℕ ( number-of-elements-count (count-left-factor count-AB b))
             ( number-of-elements-count (count-right-factor count-AB a)))
     ( number-of-elements-count count-AB)
product-number-of-elements-prod count-AB a b =
  ( inv
    ( number-of-elements-count-prod
      ( count-left-factor count-AB b)
      ( count-right-factor count-AB a))) ∙
  ( double-counting
    ( count-prod (count-left-factor count-AB b) (count-right-factor count-AB a))
    ( count-AB))

ev-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2} →
  ((x : Maybe A) → B x) → ((x : A) → B (unit-Maybe x)) × B exception-Maybe
ev-Maybe h = pair (λ x → h (unit-Maybe x)) (h exception-Maybe)

ind-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2} →
  ((x : A) → B (unit-Maybe x)) × (B exception-Maybe) → (x : Maybe A) → B x
ind-Maybe (pair h b) (inl x) = h x
ind-Maybe (pair h b) (inr star) = b

issec-ind-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2} →
  (ev-Maybe {B = B} ∘ ind-Maybe {B = B}) ~ id
issec-ind-Maybe (pair h b) = refl

isretr-ind-Maybe' :
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2} (h : (x : Maybe A) → B x) →
  (ind-Maybe (ev-Maybe h)) ~ h
isretr-ind-Maybe' h (inl x) = refl
isretr-ind-Maybe' h (inr star) = refl

isretr-ind-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2} →
  (ind-Maybe {B = B} ∘ ev-Maybe {B = B}) ~ id
isretr-ind-Maybe h = eq-htpy (isretr-ind-Maybe' h)

dependent-universal-property-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2} →
  is-equiv (ev-Maybe {B = B})
dependent-universal-property-Maybe =
  is-equiv-has-inverse
    ind-Maybe
    issec-ind-Maybe
    isretr-ind-Maybe

equiv-dependent-universal-property-Maybe :
  {l1 l2 : Level} {A : UU l1} (B : Maybe A → UU l2) →
  ((x : Maybe A) → B x) ≃ (((x : A) → B (unit-Maybe x)) × B exception-Maybe)
equiv-dependent-universal-property-Maybe B =
  pair ev-Maybe dependent-universal-property-Maybe

equiv-universal-property-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (Maybe A → B) ≃ ((A → B) × B)
equiv-universal-property-Maybe {l1} {l2} {A} {B} =
  equiv-dependent-universal-property-Maybe (λ x → B)

mere-equiv-UU-Fin : {k : ℕ} (X : UU-Fin k) → mere-equiv (Fin k) (type-UU-Fin X)
mere-equiv-UU-Fin X = pr2 X

has-finite-cardinality :
  {l : Level} → UU l → UU l
has-finite-cardinality X = Σ ℕ (has-cardinality X)

number-of-elements-has-finite-cardinality :
  {l : Level} {X : UU l} → has-finite-cardinality X → ℕ
number-of-elements-has-finite-cardinality = pr1

mere-equiv-has-finite-cardinality :
  {l : Level} {X : UU l} (c : has-finite-cardinality X) →
  type-trunc-Prop (Fin (number-of-elements-has-finite-cardinality c) ≃ X)
mere-equiv-has-finite-cardinality = pr2

all-elements-equal-has-finite-cardinality :
  {l1 : Level} {X : UU l1} → all-elements-equal (has-finite-cardinality X)
all-elements-equal-has-finite-cardinality {l1} {X} (pair k K) (pair l L) =
  eq-subtype
    ( λ k → is-prop-type-trunc-Prop)
    ( apply-universal-property-trunc-Prop K
      ( pair (Id k l) (is-set-ℕ k l))
      ( λ (e : Fin k ≃ X) →
        apply-universal-property-trunc-Prop L
          ( pair (Id k l) (is-set-ℕ k l))
          ( λ (f : Fin l ≃ X) → is-injective-Fin ((inv-equiv f) ∘e e))))

is-prop-has-finite-cardinality :
  {l1 : Level} {X : UU l1} → is-prop (has-finite-cardinality X)
is-prop-has-finite-cardinality =
  is-prop-all-elements-equal all-elements-equal-has-finite-cardinality

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

is-finite-has-cardinality :
  {l : Level} {X : UU l} {k : ℕ} → has-cardinality X k → is-finite X
is-finite-has-cardinality {k = k} H =
  is-finite-has-finite-cardinality (pair k H)

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
    ( λ g → Id-Prop ℕ-Set ( number-of-elements-count e)
                          ( number-of-elements-is-finite g))
    ( λ g →
      ( is-injective-Fin ((inv-equiv (equiv-count g)) ∘e (equiv-count e))) ∙
      ( ap pr1
        ( eq-is-prop' is-prop-has-finite-cardinality
          ( has-finite-cardinality-count g)
          ( has-finite-cardinality-is-finite (unit-trunc-Prop g)))))
    ( f)

is-finite-empty : is-finite empty
is-finite-empty = is-finite-count count-empty

is-finite-is-empty :
  {l1 : Level} {X : UU l1} → is-empty X → is-finite X
is-finite-is-empty H = is-finite-count (count-is-empty H)

empty-𝔽 : 𝔽
empty-𝔽 = pair empty (is-finite-is-empty id)

empty-UU-Fin : UU-Fin zero-ℕ
empty-UU-Fin = pair empty (unit-trunc-Prop equiv-id)

is-finite-unit : is-finite unit
is-finite-unit = is-finite-count count-unit

unit-𝔽 : 𝔽
unit-𝔽 = pair unit is-finite-unit

unit-UU-Fin : UU-Fin one-ℕ
unit-UU-Fin = pair unit (unit-trunc-Prop (left-unit-law-coprod unit))

is-finite-is-contr :
  {l1 : Level} {X : UU l1} → is-contr X → is-finite X
is-finite-is-contr H = is-finite-count (count-is-contr H)

is-finite-is-decidable-Prop :
  {l : Level} (P : UU-Prop l) →
  is-decidable (type-Prop P) → is-finite (type-Prop P)
is-finite-is-decidable-Prop P (inl x) =
  is-finite-is-contr (is-proof-irrelevant-is-prop (is-prop-type-Prop P) x)
is-finite-is-decidable-Prop P (inr x) =
  is-finite-is-empty x

is-finite-Fin : {k : ℕ} → is-finite (Fin k)
is-finite-Fin {k} = is-finite-count (count-Fin k)

Fin-𝔽 : ℕ → 𝔽
Fin-𝔽 k = pair (Fin k) (is-finite-Fin)

Fin-UU-Fin : (k : ℕ) → UU-Fin k
Fin-UU-Fin k = pair (Fin k) (unit-trunc-Prop equiv-id)

raise-Fin : (l : Level) (k : ℕ) → UU l
raise-Fin l k = raise l (Fin k)

equiv-raise-Fin : (l : Level) (k : ℕ) → Fin k ≃ raise-Fin l k
equiv-raise-Fin l k = equiv-raise l (Fin k)

map-raise-Fin : (l : Level) (k : ℕ) → Fin k → raise-Fin l k
map-raise-Fin l k = map-raise

Fin-UU-Fin-Level : (l : Level) (k : ℕ) → UU-Fin-Level l k
Fin-UU-Fin-Level l k =
  pair (raise-Fin l k) (unit-trunc-Prop (equiv-raise-Fin l k))

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

is-decidable-type-trunc-Prop-is-finite :
  {l1 : Level} {A : UU l1} → is-finite A → is-decidable (type-trunc-Prop A)
is-decidable-type-trunc-Prop-is-finite H =
  map-coprod
    ( id)
    ( map-universal-property-trunc-Prop empty-Prop)
    ( is-inhabited-or-empty-is-finite H)

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
            ( λ t →
              count-eq
                ( has-decidable-equality-is-finite (g (pr1 t)))
                ( b (pr1 t))
                ( pr2 t)))))

is-finite-base-is-finite-Σ-mere-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  type-trunc-Prop ((x : A) → B x) →
  is-finite (Σ A B) → ((x : A) → is-finite (B x)) → is-finite A
is-finite-base-is-finite-Σ-mere-section {l1} {l2} {A} {B} H f g =
  apply-universal-property-trunc-Prop H
    ( is-finite-Prop A)
    ( λ b → is-finite-base-is-finite-Σ-section b f g)

global-choice-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) →
  global-choice X → global-choice Y
global-choice-equiv e f =
  (map-equiv e ∘ f) ∘ (functor-trunc-Prop (map-inv-equiv e))

global-choice-equiv' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) →
  global-choice Y → global-choice X
global-choice-equiv' e f =
  (map-inv-equiv e ∘ f) ∘ (functor-trunc-Prop (map-equiv e))

global-choice-count :
  {l : Level} {A : UU l} → count A → global-choice A
global-choice-count (pair zero-ℕ e) t =
  ex-falso
    ( is-empty-type-trunc-Prop
      ( is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl)
      ( t))
global-choice-count (pair (succ-ℕ k) e) t = map-equiv e zero-Fin

global-choice-decidable-subtype-Fin :
  {l : Level} {k : ℕ} (P : Fin k → UU l) → ((x : Fin k) → is-prop (P x)) →
  ((x : Fin k) → is-decidable (P x)) → global-choice (Σ (Fin k) P)
global-choice-decidable-subtype-Fin {l} {zero-ℕ} P H d t =
  ex-falso (apply-universal-property-trunc-Prop t empty-Prop pr1)
global-choice-decidable-subtype-Fin {l} {succ-ℕ k} P H d t =
  map-Σ P
    ( mod-succ-ℕ k)
    ( λ x → id)
    ( global-choice-total-Q
      ( functor-trunc-Prop
        ( map-Σ Q
          ( nat-Fin)
          ( λ x → tr P (inv (issec-nat-Fin x))))
        ( t)))
  where
  Q : ℕ → UU l
  Q n = P (mod-succ-ℕ k n)
  is-prop-Q : (n : ℕ) → is-prop (Q n)
  is-prop-Q n = H (mod-succ-ℕ k n)
  is-decidable-Q : (n : ℕ) → is-decidable (Q n)
  is-decidable-Q n = d (mod-succ-ℕ k n)
  global-choice-total-Q : global-choice (Σ ℕ Q)
  global-choice-total-Q =
    global-choice-decidable-subtype-ℕ is-prop-Q is-decidable-Q

global-choice-decidable-subtype-count :
  {l1 l2 : Level} {A : UU l1} (e : count A) {P : A → UU l2} →
  ((x : A) → is-decidable (P x)) → ((x : A) → is-prop (P x)) →
  global-choice (Σ A P)
global-choice-decidable-subtype-count e {P} d H =
  global-choice-equiv
    ( equiv-Σ-equiv-base P (equiv-count e))
    ( global-choice-decidable-subtype-Fin
      ( λ x → P (map-equiv-count e x))
      ( λ x → H (map-equiv-count e x))
      ( λ x → d (map-equiv-count e x)))

global-choice-emb-count :
  {l1 l2 : Level} {A : UU l1} (e : count A) {B : UU l2} (f : B ↪ A) →
  ((x : A) → is-decidable (fib (map-emb f) x)) → global-choice B
global-choice-emb-count e f d t =
  map-equiv-total-fib
    ( map-emb f)
    ( global-choice-decidable-subtype-count e d
      ( is-prop-map-emb f)
      ( functor-trunc-Prop
        ( map-inv-equiv-total-fib (map-emb f))
        ( t)))

is-decidable-count :
  {l : Level} {X : UU l} → count X → is-decidable X
is-decidable-count (pair zero-ℕ e) =
  inr (is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl)
is-decidable-count (pair (succ-ℕ k) e) =
  inl (map-equiv e zero-Fin)

count-is-decidable-is-prop :
  {l : Level} {A : UU l} → is-prop A → is-decidable A → count A
count-is-decidable-is-prop H (inl x) =
  count-is-contr (is-proof-irrelevant-is-prop H x)
count-is-decidable-is-prop H (inr f) = count-is-empty f

count-decidable-Prop :
  {l1 : Level} (P : UU-Prop l1) →
  is-decidable (type-Prop P) → count (type-Prop P)
count-decidable-Prop P (inl p) =
  count-is-contr (is-proof-irrelevant-is-prop (is-prop-type-Prop P) p)
count-decidable-Prop P (inr f) = count-is-empty f

is-decidable-count-Σ :
  {l1 l2 : Level} {X : UU l1} {P : X → UU l2} →
  count X → count (Σ X P) → (x : X) → is-decidable (P x)
is-decidable-count-Σ e f x =
  is-decidable-count (count-fiber-count-Σ e f x)

count-decidable-subtype :
  {l1 l2 : Level} {X : UU l1} (P : X → UU-Prop l2) →
  ((x : X) → is-decidable (type-Prop (P x))) →
  count X → count (Σ X (λ x → type-Prop (P x)))
count-decidable-subtype P d e =
  count-Σ e (λ x → count-decidable-Prop (P x) (d x))

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

count-domain-emb-is-finite-domain-emb :
  {l1 l2 : Level} {A : UU l1} (e : count A) {B : UU l2} (f : B ↪ A) →
  is-finite B → count B
count-domain-emb-is-finite-domain-emb e f H =
  count-equiv
    ( equiv-total-fib (map-emb f))
    ( count-total-subtype-is-finite-total-subtype e
      ( λ x → pair (fib (map-emb f) x) (is-prop-map-emb f x))
      ( is-finite-equiv'
        ( equiv-total-fib (map-emb f))
        ( H)))

choice-count-Σ-is-finite-fiber :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-set A → count (Σ A B) → ((x : A) → is-finite (B x)) →
  ((x : A) → type-trunc-Prop (B x)) → (x : A) → B x
choice-count-Σ-is-finite-fiber {l1} {l2} {A} {B} K e g H x =
  global-choice-count
    ( count-domain-emb-is-finite-domain-emb e
      ( emb-fiber-inclusion B K x)
      ( g x))
    ( H x)

choice-is-finite-Σ-is-finite-fiber :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-set A → is-finite (Σ A B) → ((x : A) → is-finite (B x)) →
  ((x : A) → type-trunc-Prop (B x)) → type-trunc-Prop ((x : A) → B x)
choice-is-finite-Σ-is-finite-fiber {l1} {l2} {A} {B} K f g H =
  apply-universal-property-trunc-Prop f
    ( trunc-Prop ((x : A) → B x))
    ( λ e → unit-trunc-Prop (choice-count-Σ-is-finite-fiber K e g H))

is-finite-base-is-finite-Σ-merely-inhabited :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-set A → (b : (x : A) → type-trunc-Prop (B x)) →
  is-finite (Σ A B) → ((x : A) → is-finite (B x)) → is-finite A
is-finite-base-is-finite-Σ-merely-inhabited {l1} {l2} {A} {B} K b f g =
  is-finite-base-is-finite-Σ-mere-section
    ( choice-is-finite-Σ-is-finite-fiber K f g b)
    ( f)
    ( g)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  (K : is-finite A)
  where

  is-finite-codomain-has-decidable-equality :
    is-surjective f → has-decidable-equality B → is-finite B
  is-finite-codomain-has-decidable-equality H d =
    is-finite-base-is-finite-Σ-merely-inhabited
      ( is-set-has-decidable-equality d)
      ( H)
      ( is-finite-equiv' (equiv-total-fib f) K)
      ( λ b → is-finite-Σ K (λ a → is-finite-eq d))

is-finite-im-has-decidable-equality :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (K : is-finite A) →
  has-decidable-equality B → is-finite (im f)
is-finite-im-has-decidable-equality {f = f} K d =
  is-finite-codomain-has-decidable-equality K
    ( is-surjective-map-unit-im f)
    ( λ x y →
      is-decidable-equiv
        ( equiv-Eq-total-subtype-eq (λ u → is-prop-type-trunc-Prop) x y)
        ( d (pr1 x) (pr1 y)))

is-finite-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  is-finite X → is-finite Y → is-finite (coprod X Y)
is-finite-coprod {X = X} {Y} is-finite-X is-finite-Y =
  apply-universal-property-trunc-Prop is-finite-X
    ( is-finite-Prop (coprod X Y))
    ( λ (e : count X) →
      apply-universal-property-trunc-Prop is-finite-Y
        ( is-finite-Prop (coprod X Y))
        ( is-finite-count ∘ (count-coprod e)))

is-finite-mere-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → mere-equiv A B →
  is-finite A → is-finite B
is-finite-mere-equiv e H =
  apply-universal-property-trunc-Prop e
    ( is-finite-Prop _)
    ( λ e' → is-finite-equiv e' H)

is-finite-type-UU-Fin-Level :
  {l : Level} {k : ℕ} (X : UU-Fin-Level l k) → is-finite (type-UU-Fin-Level X)
is-finite-type-UU-Fin-Level X =
  is-finite-mere-equiv
    ( mere-equiv-UU-Fin-Level X)
    ( is-finite-Fin)

is-finite-type-UU-Fin :
  {k : ℕ} (X : UU-Fin k) → is-finite (type-UU-Fin X)
is-finite-type-UU-Fin X = is-finite-type-UU-Fin-Level X

is-decidable-Σ-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : coprod A B → UU l3) →
  is-decidable (Σ A (C ∘ inl)) → is-decidable (Σ B (C ∘ inr)) →
  is-decidable (Σ (coprod A B) C)
is-decidable-Σ-coprod {l1} {l2} {l3} {A} {B} C dA dB =
  is-decidable-equiv
    ( right-distributive-Σ-coprod A B C)
    ( is-decidable-coprod dA dB)

is-decidable-Σ-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2} →
  is-decidable (Σ A (B ∘ unit-Maybe)) → is-decidable (B exception-Maybe) →
  is-decidable (Σ (Maybe A) B)
is-decidable-Σ-Maybe {l1} {l2} {A} {B} dA de =
  is-decidable-Σ-coprod B dA
    ( is-decidable-equiv
      ( left-unit-law-Σ (B ∘ inr))
      ( de))

is-decidable-Σ-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} {D : B → UU l4}
  (e : A ≃ B) (f : (x : A) → C x ≃ D (map-equiv e x)) →
  is-decidable (Σ A C) → is-decidable (Σ B D)
is-decidable-Σ-equiv {D = D} e f =
  is-decidable-equiv' (equiv-Σ D e f)

is-decidable-Σ-equiv' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} {D : B → UU l4}
  (e : A ≃ B) (f : (x : A) → C x ≃ D (map-equiv e x)) →
  is-decidable (Σ B D) → is-decidable (Σ A C)
is-decidable-Σ-equiv' {D = D} e f =
  is-decidable-equiv (equiv-Σ D e f) 

is-decidable-Σ-count :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count A →
  ((x : A) → is-decidable (B x)) → is-decidable (Σ A B)
is-decidable-Σ-count e d =
  is-decidable-Σ-equiv
    ( equiv-count e)
    ( λ x → equiv-id)
    ( is-decidable-Σ-Fin (λ x → d (map-equiv-count e x)))

is-decidable-Π-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : coprod A B → UU l3} →
  is-decidable ((a : A) → C (inl a)) → is-decidable ((b : B) → C (inr b)) →
  is-decidable ((x : coprod A B) → C x)
is-decidable-Π-coprod {C = C} dA dB =
  is-decidable-equiv
    ( equiv-dependent-universal-property-coprod C)
    ( is-decidable-prod dA dB)

is-decidable-Π-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2} →
  is-decidable ((x : A) → B (unit-Maybe x)) → is-decidable (B exception-Maybe) →
  is-decidable ((x : Maybe A) → B x)
is-decidable-Π-Maybe {B = B} du de =
  is-decidable-equiv
    ( equiv-dependent-universal-property-Maybe B)
    ( is-decidable-prod du de)

is-decidable-Π-Fin :
  {l1 : Level} {k : ℕ} {B : Fin k → UU l1} →
  ((x : Fin k) → is-decidable (B x)) → is-decidable ((x : Fin k) → B x)
is-decidable-Π-Fin {l1} {zero-ℕ} {B} d = inl ind-empty
is-decidable-Π-Fin {l1} {succ-ℕ k} {B} d =
  is-decidable-Π-Maybe
    ( is-decidable-Π-Fin (λ x → d (inl x)))
    ( d (inr star))

is-decidable-Π-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} {D : B → UU l4}
  (e : A ≃ B) (f : (x : A) → C x ≃ D (map-equiv e x)) →
  is-decidable ((x : A) → C x) → is-decidable ((y : B) → D y)
is-decidable-Π-equiv {D = D} e f = is-decidable-equiv' (equiv-Π D e f)

is-decidable-Π-equiv' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} {D : B → UU l4}
  (e : A ≃ B) (f : (x : A) → C x ≃ D (map-equiv e x)) →
  is-decidable ((y : B) → D y) → is-decidable ((x : A) → C x)
is-decidable-Π-equiv' {D = D} e f = is-decidable-equiv (equiv-Π D e f)

is-decidable-Π-count :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → ((x : A) → is-decidable (B x)) → is-decidable ((x : A) → B x)
is-decidable-Π-count e d =
  is-decidable-Π-equiv
    ( equiv-count e)
    ( λ x → equiv-id)
    ( is-decidable-Π-Fin (λ x → d (map-equiv-count e x)))

--------------------------------------------------------------------------------

-- Univalence

equiv-eq : {i : Level} {A : UU i} {B : UU i} → Id A B → A ≃ B
equiv-eq refl = equiv-id

UNIVALENCE : {i : Level} (A B : UU i) → UU (lsuc i)
UNIVALENCE A B = is-equiv (equiv-eq {A = A} {B = B})

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

postulate univalence : {i : Level} (A B : UU i) → UNIVALENCE A B

eq-equiv : {i : Level} (A B : UU i) → (A ≃ B) → Id A B
eq-equiv A B = map-inv-is-equiv (univalence A B)

equiv-univalence :
  {i : Level} {A B : UU i} → Id A B ≃ (A ≃ B)
equiv-univalence = pair equiv-eq (univalence _ _)

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

subuniverse :
  (l1 l2 : Level) → UU ((lsuc l1) ⊔ (lsuc l2))
subuniverse l1 l2 = UU l1 → UU-Prop l2

total-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) → UU ((lsuc l1) ⊔ l2)
total-subuniverse {l1} P = Σ (UU l1) (λ X → type-Prop (P X))

equiv-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  (X Y : total-subuniverse P) → UU l1
equiv-subuniverse P X Y = (pr1 X) ≃ (pr1 Y)

equiv-eq-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  (s t : total-subuniverse P) → Id s t → equiv-subuniverse P s t
equiv-eq-subuniverse P (pair X p) .(pair X p) refl = equiv-id

is-subtype-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  is-prop (type-Prop (P X))
is-subtype-subuniverse P X = is-prop-type-Prop (P X)

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

is-equiv-equiv-eq-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2)
  (s t : total-subuniverse P) → is-equiv (equiv-eq-subuniverse P s t)
is-equiv-equiv-eq-subuniverse P (pair X p) =
  fundamental-theorem-id
    ( pair X p)
    ( equiv-id)
    ( is-contr-total-equiv-subuniverse P (pair X p))
    ( equiv-eq-subuniverse P (pair X p))

eq-equiv-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  {s t : total-subuniverse P} → equiv-subuniverse P s t → Id s t
eq-equiv-subuniverse P {s} {t} =
  map-inv-is-equiv (is-equiv-equiv-eq-subuniverse P s t)

UU-Contr : (l : Level) → UU (lsuc l)
UU-Contr l = total-subuniverse is-contr-Prop

type-UU-Contr : {l : Level} → UU-Contr l → UU l
type-UU-Contr A = pr1 A

is-contr-type-UU-Contr :
  {l : Level} (A : UU-Contr l) → is-contr (type-UU-Contr A)
is-contr-type-UU-Contr A = pr2 A

equiv-UU-Contr :
  {l1 l2 : Level} (X : UU-Contr l1) (Y : UU-Contr l2) → UU (l1 ⊔ l2)
equiv-UU-Contr X Y = type-UU-Contr X ≃ type-UU-Contr Y

equiv-eq-UU-Contr :
  {l1 : Level} (X Y : UU-Contr l1) → Id X Y → equiv-UU-Contr X Y
equiv-eq-UU-Contr X Y = equiv-eq-subuniverse is-contr-Prop X Y

is-equiv-equiv-eq-UU-Contr :
  {l1 : Level} (X Y : UU-Contr l1) → is-equiv (equiv-eq-UU-Contr X Y)
is-equiv-equiv-eq-UU-Contr X Y =
  is-equiv-equiv-eq-subuniverse is-contr-Prop X Y

eq-equiv-UU-Contr :
  {l1 : Level} {X Y : UU-Contr l1} → equiv-UU-Contr X Y → Id X Y
eq-equiv-UU-Contr = eq-equiv-subuniverse is-contr-Prop

center-UU-contr : (l : Level) → UU-Contr l
center-UU-contr l = pair (raise-unit l) is-contr-raise-unit

contraction-UU-contr :
  {l : Level} (A : UU-Contr l) → Id (center-UU-contr l) A
contraction-UU-contr A =
  eq-equiv-UU-Contr
    ( equiv-is-contr is-contr-raise-unit (is-contr-type-UU-Contr A))

is-contr-UU-Contr : (l : Level) → is-contr (UU-Contr l)
is-contr-UU-Contr l = pair (center-UU-contr l) contraction-UU-contr

UU-Trunc : (k : 𝕋) (l : Level) → UU (lsuc l)
UU-Trunc k l = Σ (UU l) (is-trunc k)

type-UU-Trunc : {k : 𝕋} {l : Level} → UU-Trunc k l → UU l
type-UU-Trunc A = pr1 A

is-trunc-type-UU-Trunc :
  {k : 𝕋} {l : Level} (A : UU-Trunc k l) → is-trunc k (type-UU-Trunc A)
is-trunc-type-UU-Trunc A = pr2 A

is-trunc-UU-Trunc :
  (k : 𝕋) (l : Level) → is-trunc (succ-𝕋 k) (UU-Trunc k l)
is-trunc-UU-Trunc k l X Y =
  is-trunc-is-equiv k
    ( Id (pr1 X) (pr1 Y))
    ( ap pr1)
    ( is-emb-pr1
      ( is-prop-is-trunc k) X Y)
    ( is-trunc-is-equiv k
      ( (pr1 X) ≃ (pr1 Y))
      ( equiv-eq)
      ( univalence (pr1 X) (pr1 Y))
      ( is-trunc-equiv-is-trunc k (pr2 X) (pr2 Y)))

is-set-UU-Prop : (l : Level) → is-set (UU-Prop l)
is-set-UU-Prop l = is-trunc-UU-Trunc (neg-one-𝕋) l

UU-Prop-Set : (l : Level) → UU-Set (lsuc l)
UU-Prop-Set l = pair (UU-Prop l) (is-set-UU-Prop l)

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

iff-eq :
  {l1 : Level} {P Q : UU-Prop l1} → Id P Q → P ⇔ Q
iff-eq refl = pair id id

is-equiv-iff-eq :
  {l1 : Level} (P Q : UU-Prop l1) → is-equiv (iff-eq {l1} {P} {Q})
is-equiv-iff-eq P =
  fundamental-theorem-id P
    ( pair id id)
    ( is-contr-total-iff P)
    ( λ Q → iff-eq {P = P} {Q})

eq-iff' :
  {l1 : Level} (P Q : UU-Prop l1) → P ⇔ Q → Id P Q
eq-iff' P Q = map-inv-is-equiv (is-equiv-iff-eq P Q)

eq-iff :
  {l1 : Level} {P Q : UU-Prop l1} →
  (type-Prop P → type-Prop Q) → (type-Prop Q → type-Prop P) → Id P Q
eq-iff {l1} {P} {Q} f g = eq-iff' P Q (pair f g)

eq-equiv-Prop :
  {l1 : Level} {P Q : UU-Prop l1} → (type-Prop P ≃ type-Prop Q) → Id P Q
eq-equiv-Prop e =
  eq-iff (map-equiv e) (map-inv-equiv e)

precomp-Set :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : UU-Set l3) →
  (B → type-Set C) → (A → type-Set C)
precomp-Set f C = precomp f (type-Set C)

square-htpy-eq :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B) →
  ( g h : B → C) →
  ( (λ (p : (y : B) → Id (g y) (h y)) (x : A) → p (f x)) ∘ htpy-eq) ~
  ( htpy-eq ∘ (ap (precomp f C)))
square-htpy-eq f g .g refl = refl

is-emb-precomp-Set-is-surjective :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-surjective f → (C : UU-Set l3) → is-emb (precomp-Set f C)
is-emb-precomp-Set-is-surjective H C =
  is-emb-is-injective
    ( is-set-function-type (is-set-type-Set C))
    ( λ {g} {h} p →
      eq-htpy (λ b →
         apply-universal-property-trunc-Prop
           ( H b)
           ( Id-Prop C (g b) (h b))
           ( λ u →
             ( inv (ap g (pr2 u))) ∙
             ( ( htpy-eq p (pr1 u))  ∙
               ( ap h (pr2 u))))))

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

equiv-equiv-eq-UU-Fin-Level :
  {l : Level} {k : ℕ} (X Y : UU-Fin-Level l k) →
  Id X Y ≃ equiv-UU-Fin-Level X Y
equiv-equiv-eq-UU-Fin-Level X Y =
  pair equiv-eq-UU-Fin-Level (is-equiv-equiv-eq-UU-Fin-Level X Y)

equiv-equiv-eq-UU-Fin :
  {k : ℕ} (X Y : UU-Fin k) → Id X Y ≃ equiv-UU-Fin X Y
equiv-equiv-eq-UU-Fin X Y =
  pair equiv-eq-UU-Fin (is-equiv-equiv-eq-UU-Fin X Y)

--------------------------------------------------------------------------------

-- Set quotients

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

is-locally-small :
  (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
is-locally-small l A = (x y : A) → is-small l (Id x y)

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
map-set-quotient R = map-unit-im (prop-Eq-Rel R)

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

is-set-set-quotient :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) → is-set (set-quotient R)
is-set-set-quotient {l1} {l2} R =
  is-set-im (prop-Eq-Rel R) (is-set-function-type (is-set-UU-Prop l2))

quotient-Set :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) → UU-Set (l1 ⊔ lsuc l2)
quotient-Set R = pair (set-quotient R) (is-set-set-quotient R)

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

apply-effectiveness-map-set-quotient :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) {x y : A} →
  Id (map-set-quotient R x) (map-set-quotient R y) → type-Eq-Rel R x y
apply-effectiveness-map-set-quotient R {x} {y} =
  map-equiv (is-effective-map-set-quotient R x y)

apply-effectiveness-map-set-quotient' :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) {x y : A} →
  type-Eq-Rel R x y → Id (map-set-quotient R x) (map-set-quotient R y)
apply-effectiveness-map-set-quotient' R {x} {y} =
  map-inv-equiv (is-effective-map-set-quotient R x y)

reflects-Eq-Rel :
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  {B : UU l3} → (A → B) → UU (l1 ⊔ (l2 ⊔ l3))
reflects-Eq-Rel {A = A} R f =
  {x y : A} → type-Eq-Rel R x y → Id (f x) (f y)

reflecting-map-Eq-Rel :
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU l3) →
  UU (l1 ⊔ l2 ⊔ l3)
reflecting-map-Eq-Rel {A = A} R B =
  Σ (A → B) (reflects-Eq-Rel R)

is-prop-reflects-Eq-Rel :
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU-Set l3)
  (f : A → type-Set B) → is-prop (reflects-Eq-Rel R f)
is-prop-reflects-Eq-Rel R B f =
  is-prop-Π'
    ( λ x →
      is-prop-Π'
        ( λ y →
          is-prop-function-type (is-set-type-Set B (f x) (f y))))

module _
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU-Set l3)
  (f : reflecting-map-Eq-Rel R (type-Set B))
  where

  htpy-reflecting-map-Eq-Rel :
    (g : reflecting-map-Eq-Rel R (type-Set B)) → UU _
  htpy-reflecting-map-Eq-Rel g =
    pr1 f ~ pr1 g
  
  refl-htpy-reflecting-map-Eq-Rel :
    htpy-reflecting-map-Eq-Rel f
  refl-htpy-reflecting-map-Eq-Rel = refl-htpy
  
  htpy-eq-reflecting-map-Eq-Rel :
    (g : reflecting-map-Eq-Rel R (type-Set B)) →
    Id f g → htpy-reflecting-map-Eq-Rel g
  htpy-eq-reflecting-map-Eq-Rel .f refl =
    refl-htpy-reflecting-map-Eq-Rel
  
  is-contr-total-htpy-reflecting-map-Eq-Rel :
    is-contr
      ( Σ (reflecting-map-Eq-Rel R (type-Set B)) htpy-reflecting-map-Eq-Rel)
  is-contr-total-htpy-reflecting-map-Eq-Rel =
    is-contr-total-Eq-substructure
      ( is-contr-total-htpy (pr1 f))
      ( is-prop-reflects-Eq-Rel R B)
      ( pr1 f)
      ( refl-htpy)
      ( pr2 f)

  is-equiv-htpy-eq-reflecting-map-Eq-Rel :
    (g : reflecting-map-Eq-Rel R (type-Set B)) →
    is-equiv (htpy-eq-reflecting-map-Eq-Rel g)
  is-equiv-htpy-eq-reflecting-map-Eq-Rel =
    fundamental-theorem-id f
      refl-htpy-reflecting-map-Eq-Rel
      is-contr-total-htpy-reflecting-map-Eq-Rel
      htpy-eq-reflecting-map-Eq-Rel

  eq-htpy-reflecting-map-Eq-Rel :
    (g : reflecting-map-Eq-Rel R (type-Set B)) →
    htpy-reflecting-map-Eq-Rel g → Id f g
  eq-htpy-reflecting-map-Eq-Rel g =
    map-inv-is-equiv (is-equiv-htpy-eq-reflecting-map-Eq-Rel g)

  equiv-htpy-eq-reflecting-map-Eq-Rel :
    (g : reflecting-map-Eq-Rel R (type-Set B)) →
    Id f g ≃ htpy-reflecting-map-Eq-Rel g
  equiv-htpy-eq-reflecting-map-Eq-Rel g =
    pair
      ( htpy-eq-reflecting-map-Eq-Rel g)
      ( is-equiv-htpy-eq-reflecting-map-Eq-Rel g)

precomp-Set-Quotient :
  {l l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  (B : UU-Set l3) (f : reflecting-map-Eq-Rel R (type-Set B)) →
  (X : UU-Set l) → (type-hom-Set B X) → reflecting-map-Eq-Rel R (type-Set X)
precomp-Set-Quotient R B f X g =
  pair (g ∘ (pr1 f)) (λ r → ap g (pr2 f r))

precomp-id-Set-Quotient :
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU-Set l3)
  (f : reflecting-map-Eq-Rel R (type-Set B)) →
  Id (precomp-Set-Quotient R B f B id) f
precomp-id-Set-Quotient R B f =
  eq-htpy-reflecting-map-Eq-Rel R B
    ( precomp-Set-Quotient R B f B id)
    ( f)
    ( refl-htpy)

precomp-comp-Set-Quotient :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  (B : UU-Set l3) (f : reflecting-map-Eq-Rel R (type-Set B))
  (C : UU-Set l4) (g : type-hom-Set B C)
  (D : UU-Set l5) (h : type-hom-Set C D) →
  Id ( precomp-Set-Quotient R B f D (h ∘ g))
     ( precomp-Set-Quotient R C (precomp-Set-Quotient R B f C g) D h)
precomp-comp-Set-Quotient R B f C g D h =
  eq-htpy-reflecting-map-Eq-Rel R D
    ( precomp-Set-Quotient R B f D (h ∘ g))
    ( precomp-Set-Quotient R C (precomp-Set-Quotient R B f C g) D h)
    ( refl-htpy)

is-set-quotient :
  (l : Level) {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  (B : UU-Set l3) (f : reflecting-map-Eq-Rel R (type-Set B)) → UU _
is-set-quotient l R B f =
  (X : UU-Set l) →
  is-equiv (precomp-Set-Quotient R B f X)

universal-property-set-quotient :
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU-Set l3)
  (f : reflecting-map-Eq-Rel R (type-Set B)) →
  ({l : Level} → is-set-quotient l R B f) → {l : Level}
  (X : UU-Set l) (g : reflecting-map-Eq-Rel R (type-Set X)) →
  is-contr (Σ (type-hom-Set B X) (λ h → (h ∘ pr1 f) ~ pr1 g))
universal-property-set-quotient R B f Q X g =
   is-contr-equiv'
     ( fib (precomp-Set-Quotient R B f X) g)
     ( equiv-tot
       ( λ h →
         equiv-htpy-eq-reflecting-map-Eq-Rel R X
           ( precomp-Set-Quotient R B f X h)
           ( g)))
     ( is-contr-map-is-equiv (Q X) g)

map-universal-property-set-quotient :
  {l1 l2 l3 l4 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU-Set l3)
  (f : reflecting-map-Eq-Rel R (type-Set B)) →
  (Uf : {l : Level} → is-set-quotient l R B f) (C : UU-Set l4)
  (g : reflecting-map-Eq-Rel R (type-Set C)) →
  type-Set B → type-Set C
map-universal-property-set-quotient R B f Uf C g =
  pr1 (center (universal-property-set-quotient R B f Uf C g))

triangle-universal-property-set-quotient :
  {l1 l2 l3 l4 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU-Set l3)
  (f : reflecting-map-Eq-Rel R (type-Set B)) →
  (Uf : {l : Level} → is-set-quotient l R B f) (C : UU-Set l4)
  (g : reflecting-map-Eq-Rel R (type-Set C)) →
  (map-universal-property-set-quotient R B f Uf C g ∘ pr1 f) ~ pr1 g
triangle-universal-property-set-quotient R B f Uf C g =
  ( pr2 (center (universal-property-set-quotient R B f Uf C g)))

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  (B : UU-Set l3) (f : reflecting-map-Eq-Rel R (type-Set B))
  (C : UU-Set l4) (g : reflecting-map-Eq-Rel R (type-Set C))
  {h : type-Set B → type-Set C} (H : (h ∘ pr1 f) ~ pr1 g)
  where

  is-equiv-is-set-quotient-is-set-quotient :
    ({l : Level} → is-set-quotient l R B f) →
    ({l : Level} → is-set-quotient l R C g) →
    is-equiv h
  is-equiv-is-set-quotient-is-set-quotient Uf Ug =
    is-equiv-has-inverse
      ( pr1 (center K))
      ( htpy-eq
        ( is-injective-is-equiv
          ( Ug C)
          { h ∘ k}
          { id}
          ( ( precomp-comp-Set-Quotient R C g B k C h) ∙
            ( ( ap (λ t → precomp-Set-Quotient R B t C h) α) ∙
              ( ( eq-htpy-reflecting-map-Eq-Rel R C
                  ( precomp-Set-Quotient R B f C h) g H) ∙
                ( inv (precomp-id-Set-Quotient R C g)))))))
      ( htpy-eq
        ( is-injective-is-equiv
          ( Uf B)
          { k ∘ h}
          { id}
          ( ( precomp-comp-Set-Quotient R B f C h B k) ∙
            ( ( ap
                ( λ t → precomp-Set-Quotient R C t B k)
                ( eq-htpy-reflecting-map-Eq-Rel R C
                  ( precomp-Set-Quotient R B f C h) g H)) ∙
              ( ( α) ∙
                ( inv (precomp-id-Set-Quotient R B f)))))))
    where
    K = universal-property-set-quotient R C g Ug B f
    k : type-Set C → type-Set B
    k = pr1 (center K)
    α : Id (precomp-Set-Quotient R C g B k) f
    α = eq-htpy-reflecting-map-Eq-Rel R B
          ( precomp-Set-Quotient R C g B k)
          ( f)
          ( pr2 (center K))

  is-set-quotient-is-set-quotient-is-equiv :
    is-equiv h → ({l : Level} → is-set-quotient l R B f) →
    {l : Level} → is-set-quotient l R C g
  is-set-quotient-is-set-quotient-is-equiv E Uf {l} X =
    is-equiv-comp
      ( precomp-Set-Quotient R C g X)
      ( precomp-Set-Quotient R B f X)
      ( precomp h (type-Set X))
      ( λ k →
        eq-htpy-reflecting-map-Eq-Rel R X
          ( precomp-Set-Quotient R C g X k)
          ( precomp-Set-Quotient R B f X (k ∘ h))
          ( inv-htpy (k ·l H)))
      ( is-equiv-precomp-is-equiv h E (type-Set X))
      ( Uf X)

  is-set-quotient-is-equiv-is-set-quotient :
    ({l : Level} → is-set-quotient l R C g) → is-equiv h →
    {l : Level} → is-set-quotient l R B f
  is-set-quotient-is-equiv-is-set-quotient Ug E {l} X =
    is-equiv-left-factor
      ( precomp-Set-Quotient R C g X)
      ( precomp-Set-Quotient R B f X)
      ( precomp h (type-Set X))
      ( λ k →
        eq-htpy-reflecting-map-Eq-Rel R X
          ( precomp-Set-Quotient R C g X k)
          ( precomp-Set-Quotient R B f X (k ∘ h))
          ( inv-htpy (k ·l H)))
      ( Ug X)
      ( is-equiv-precomp-is-equiv h E (type-Set X))

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  (B : UU-Set l3) (f : reflecting-map-Eq-Rel R (type-Set B)) 
  (Uf : {l : Level} → is-set-quotient l R B f)
  (C : UU-Set l4) (g : reflecting-map-Eq-Rel R (type-Set C))
  (Ug : {l : Level} → is-set-quotient l R C g)
  where
  
  uniqueness-set-quotient :
    is-contr (Σ (type-Set B ≃ type-Set C) (λ e → (map-equiv e ∘ pr1 f) ~ pr1 g))
  uniqueness-set-quotient =
    is-contr-total-Eq-substructure
      ( universal-property-set-quotient R B f Uf C g)
      ( is-subtype-is-equiv)
      ( map-universal-property-set-quotient R B f Uf C g)
      ( triangle-universal-property-set-quotient R B f Uf C g)
      ( is-equiv-is-set-quotient-is-set-quotient R B f C g
        ( triangle-universal-property-set-quotient R B f Uf C g)
        ( Uf)
        ( Ug))

  equiv-uniqueness-set-quotient : type-Set B ≃ type-Set C
  equiv-uniqueness-set-quotient =
    pr1 (center uniqueness-set-quotient)

  map-equiv-uniqueness-set-quotient : type-Set B → type-Set C
  map-equiv-uniqueness-set-quotient =  map-equiv equiv-uniqueness-set-quotient

  triangle-uniqueness-set-quotient :
    ( map-equiv-uniqueness-set-quotient ∘ pr1 f) ~ pr1 g
  triangle-uniqueness-set-quotient =
    pr2 (center uniqueness-set-quotient)

is-surjective-and-effective :
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) {B : UU l3}
  (f : A → B) → UU (l1 ⊔ l2 ⊔ l3)
is-surjective-and-effective {A = A} R f =
  is-surjective f × is-effective R f

module _
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU-Set l3)
  (q : A → type-Set B)
  where

  is-effective-is-image :
    (i : type-Set B ↪ (A → UU-Prop l2)) →
    (T : (prop-Eq-Rel R) ~ ((map-emb i) ∘ q)) →
    ({l : Level} → is-image l (prop-Eq-Rel R) i (pair q T)) →
    is-effective R q
  is-effective-is-image i T H x y =
    ( is-effective-map-set-quotient R x y) ∘e
    ( ( inv-equiv (equiv-ap-emb (emb-im (prop-Eq-Rel R)))) ∘e
      ( ( inv-equiv (convert-eq-values-htpy T x y)) ∘e
        ( equiv-ap-emb i)))

  is-surjective-and-effective-is-image :
    (i : type-Set B ↪ (A → UU-Prop l2)) → 
    (T : (prop-Eq-Rel R) ~ ((map-emb i) ∘ q)) →
    ({l : Level} → is-image l (prop-Eq-Rel R) i (pair q T)) →
    is-surjective-and-effective R q
  is-surjective-and-effective-is-image i T H =
    pair
      ( is-surjective-is-image (prop-Eq-Rel R) i (pair q T) H)
      ( is-effective-is-image i T H)

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
      is-image l
        ( prop-Eq-Rel R)
        ( emb-is-surjective-and-effective H)
        ( pair q (triangle-emb-is-surjective-and-effective H)))
  is-image-is-surjective-and-effective H =
    is-image-is-surjective
      ( prop-Eq-Rel R)
      ( emb-is-surjective-and-effective H)
      ( pair q (triangle-emb-is-surjective-and-effective H))
      ( pr1 H)

  is-surjective-is-set-quotient :
    (H : reflects-Eq-Rel R q) →
    ({l : Level} → is-set-quotient l R B (pair q H)) →
    is-surjective q
  is-surjective-is-set-quotient H Q b =
    tr ( λ y → type-trunc-Prop (fib q y))
       ( htpy-eq
         ( ap pr1
           ( eq-is-contr
             ( universal-property-set-quotient R B (pair q H) Q B (pair q H))
             { pair (inclusion-im q ∘ β) δ}
             { pair id refl-htpy}))
         ( b))
       ( pr2 (β b))
    where
    α : reflects-Eq-Rel R (map-unit-im q)
    α {x} {y} r =
      is-injective-is-emb
        ( is-emb-inclusion-im q)
        ( map-equiv (convert-eq-values-htpy (triangle-unit-im q) x y) (H r))
    β : type-Set B → im q
    β = map-inv-is-equiv
          ( Q ( pair (im q) (is-set-im q (is-set-type-Set B))))
          ( pair (map-unit-im q) α)
    γ : (β ∘ q) ~ map-unit-im q
    γ = htpy-eq
          ( ap pr1
            ( issec-map-inv-is-equiv
              ( Q (pair (im q) (is-set-im q (is-set-type-Set B))))
              ( pair (map-unit-im q) α)))
    δ : ((inclusion-im q ∘ β) ∘ q) ~ q
    δ = (inclusion-im q ·l γ) ∙h (triangle-unit-im q)

  is-effective-is-set-quotient :
    (H : reflects-Eq-Rel R q) →
    ({l : Level} → is-set-quotient l R B (pair q H)) →
    is-effective R q
  is-effective-is-set-quotient H Q x y =
    inv-equiv (compute-P y) ∘e δ (q y)
    where
    α : Σ (A → UU-Prop l2) (reflects-Eq-Rel R)
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
    (H : reflects-Eq-Rel R q) →
    ({l : Level} → is-set-quotient l R B (pair q H)) →
    is-surjective-and-effective R q
  is-surjective-and-effective-is-set-quotient H Q =
    pair (is-surjective-is-set-quotient H Q) (is-effective-is-set-quotient H Q)

  reflects-Eq-Rel-is-surjective-and-effective :
    is-surjective-and-effective R q → reflects-Eq-Rel R q
  reflects-Eq-Rel-is-surjective-and-effective E {x} {y} =
    map-inv-equiv (pr2 E x y)

  universal-property-set-quotient-is-surjective-and-effective :
    {l : Level} (E : is-surjective-and-effective R q) (X : UU-Set l) →
    is-contr-map
      ( precomp-Set-Quotient R B
        ( pair q (reflects-Eq-Rel-is-surjective-and-effective E))
        ( X))
  universal-property-set-quotient-is-surjective-and-effective
    {l} E X (pair f H) =
    is-proof-irrelevant-is-prop
      ( is-prop-equiv
        ( fib (precomp q (type-Set X)) f)
        ( equiv-tot
          ( λ h → equiv-ap-pr1 (is-prop-reflects-Eq-Rel R X)))
        ( is-prop-map-is-emb (is-emb-precomp-is-surjective (pr1 E) X) f))
      ( pair
        ( λ b → pr1 (α b))
        ( eq-subtype
          ( is-prop-reflects-Eq-Rel R X)
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
    is-set-quotient l R B
      ( pair q (reflects-Eq-Rel-is-surjective-and-effective E))
  is-set-quotient-is-surjective-and-effective E X =
    is-equiv-is-contr-map
      ( universal-property-set-quotient-is-surjective-and-effective E X)

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

triangle-is-set-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  (is-settr-f : {l : Level} → is-set-truncation l B f) →
  (C : UU-Set l3) (g : A → type-Set C) →
  ((map-is-set-truncation B f is-settr-f C g) ∘ f) ~ g
triangle-is-set-truncation B f is-settr-f C g =
  pr2
    ( center
      ( universal-property-is-set-truncation _ B f is-settr-f C g))

is-set-truncation-id :
  {l1 : Level} {A : UU l1} (H : is-set A) →
  {l2 : Level} → is-set-truncation l2 (pair A H) id
is-set-truncation-id H B = is-equiv-precomp-is-equiv id is-equiv-id (type-Set B)

is-set-truncation-equiv :
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (e : A ≃ type-Set B) →
  {l : Level} → is-set-truncation l2 B (map-equiv e)
is-set-truncation-equiv B e C =
  is-equiv-precomp-is-equiv (map-equiv e) (is-equiv-map-equiv e) (type-Set C)

precomp-Π-Set :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU-Set l3) →
  ((b : B) → type-Set (C b)) → ((a : A) → type-Set (C (f a)))
precomp-Π-Set f C h a = h (f a)

dependent-universal-property-set-truncation :
  {l1 l2 : Level} (l : Level) {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  UU (l1 ⊔ l2 ⊔ lsuc l)
dependent-universal-property-set-truncation l {A} B f =
  (X : type-Set B → UU-Set l) → is-equiv (precomp-Π-Set f X)

mere-eq-Eq-Rel : {l1 : Level} (A : UU l1) → Eq-Rel l1 A
mere-eq-Eq-Rel A =
  pair
    mere-eq-Prop
    ( pair refl-mere-eq (pair symm-mere-eq trans-mere-eq))
  
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

is-set-truncation-dependent-universal-property :
  {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  ({l : Level} → dependent-universal-property-set-truncation l B f) →
  is-set-truncation l3 B f
is-set-truncation-dependent-universal-property B f H X =
  H (λ b → X)

reflects-mere-eq :
  {l1 l2 : Level} {A : UU l1} (X : UU-Set l2) (f : A → type-Set X) →
  reflects-Eq-Rel (mere-eq-Eq-Rel A) f
reflects-mere-eq X f {x} {y} r =
  apply-universal-property-trunc-Prop r
    ( Id-Prop X (f x) (f y))
    ( ap f)

reflecting-map-mere-eq :
  {l1 l2 : Level} {A : UU l1} (X : UU-Set l2) (f : A → type-Set X) →
  reflecting-map-Eq-Rel (mere-eq-Eq-Rel A) (type-Set X)
reflecting-map-mere-eq X f = pair f (reflects-mere-eq X f)

is-set-truncation-is-set-quotient :
  {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  ( {l : Level} →
    is-set-quotient l (mere-eq-Eq-Rel A) B (reflecting-map-mere-eq B f)) →
  is-set-truncation l3 B f
is-set-truncation-is-set-quotient {A = A} B f H X =
  is-equiv-comp
    ( precomp-Set f X)
    ( pr1)
    ( precomp-Set-Quotient (mere-eq-Eq-Rel A) B (reflecting-map-mere-eq B f) X)
    ( refl-htpy)
    ( H X)
    ( is-equiv-pr1-is-contr
      ( λ h →
        is-proof-irrelevant-is-prop
          ( is-prop-reflects-Eq-Rel (mere-eq-Eq-Rel A) X h)
          ( reflects-mere-eq X h)))

is-set-quotient-is-set-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  ( {l : Level} → is-set-truncation l B f) →
  is-set-quotient l3 (mere-eq-Eq-Rel A) B (reflecting-map-mere-eq B f)
is-set-quotient-is-set-truncation {A = A} B f H X =
  is-equiv-right-factor
    ( precomp-Set f X)
    ( pr1)
    ( precomp-Set-Quotient (mere-eq-Eq-Rel A) B (reflecting-map-mere-eq B f) X)
    ( refl-htpy)
    ( is-equiv-pr1-is-contr
      ( λ h →
        is-proof-irrelevant-is-prop
          ( is-prop-reflects-Eq-Rel (mere-eq-Eq-Rel A) X h)
          ( reflects-mere-eq X h)))
    ( H X)

module _
  {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B)
  (C : UU-Set l3) (g : A → type-Set C) {h : type-hom-Set B C}
  (H : (h ∘ f) ~ g)
  where

  is-equiv-is-set-truncation-is-set-truncation :
    ({l : Level} → is-set-truncation l B f) →
    ({l : Level} → is-set-truncation l C g) →
    is-equiv h
  is-equiv-is-set-truncation-is-set-truncation Sf Sg =
    is-equiv-is-set-quotient-is-set-quotient
      ( mere-eq-Eq-Rel A)
      ( B)
      ( reflecting-map-mere-eq B f)
      ( C)
      ( reflecting-map-mere-eq C g)
      ( H)
      ( λ {l} → is-set-quotient-is-set-truncation B f Sf)
      ( λ {l} → is-set-quotient-is-set-truncation C g Sg)

  is-set-truncation-is-equiv-is-set-truncation :
    ({l : Level} → is-set-truncation l C g) → is-equiv h → 
    {l : Level} → is-set-truncation l B f
  is-set-truncation-is-equiv-is-set-truncation Sg Eh =
    is-set-truncation-is-set-quotient B f
      ( is-set-quotient-is-equiv-is-set-quotient
        ( mere-eq-Eq-Rel A)
        ( B)
        ( reflecting-map-mere-eq B f)
        ( C)
        ( reflecting-map-mere-eq C g)
        ( H)
        ( is-set-quotient-is-set-truncation C g Sg)
        ( Eh))

  is-set-truncation-is-set-truncation-is-equiv :
    is-equiv h → ({l : Level} → is-set-truncation l B f) →
    {l : Level} → is-set-truncation l C g
  is-set-truncation-is-set-truncation-is-equiv Eh Sf =
    is-set-truncation-is-set-quotient C g
      ( is-set-quotient-is-set-quotient-is-equiv
        ( mere-eq-Eq-Rel A)
        ( B)
        ( reflecting-map-mere-eq B f)
        ( C)
        ( reflecting-map-mere-eq C g)
        ( H)
        ( Eh)
        ( is-set-quotient-is-set-truncation B f Sf))

module _
  {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B)
  (C : UU-Set l3) (g : A → type-Set C)
  (Sf : {l : Level} → is-set-truncation l B f)
  (Sg : {l : Level} → is-set-truncation l C g)
  where

  uniqueness-set-truncation :
    is-contr (Σ (type-Set B ≃ type-Set C) (λ e → (map-equiv e ∘ f) ~ g))
  uniqueness-set-truncation =
    uniqueness-set-quotient
      ( mere-eq-Eq-Rel A)
      ( B)
      ( reflecting-map-mere-eq B f)
      ( is-set-quotient-is-set-truncation B f Sf)
      ( C)
      ( reflecting-map-mere-eq C g)
      ( is-set-quotient-is-set-truncation C g Sg)
  
  equiv-uniqueness-set-truncation : type-Set B ≃ type-Set C
  equiv-uniqueness-set-truncation =
    pr1 (center uniqueness-set-truncation)

  map-equiv-uniqueness-set-truncation : type-Set B → type-Set C
  map-equiv-uniqueness-set-truncation =
    map-equiv equiv-uniqueness-set-truncation

  triangle-uniqueness-set-truncation :
    (map-equiv-uniqueness-set-truncation ∘ f) ~ g
  triangle-uniqueness-set-truncation =
    pr2 (center uniqueness-set-truncation)

postulate type-trunc-Set : {l : Level} → UU l → UU l

postulate
  is-set-type-trunc-Set : {l : Level} {A : UU l} → is-set (type-trunc-Set A)

trunc-Set : {l : Level} → UU l → UU-Set l
trunc-Set A = pair (type-trunc-Set A) is-set-type-trunc-Set

postulate unit-trunc-Set : {l : Level} {A : UU l} → A → type-Set (trunc-Set A)

postulate
  is-set-truncation-trunc-Set :
    {l1 l2 : Level} (A : UU l1) →
    is-set-truncation l2 (trunc-Set A) unit-trunc-Set

equiv-universal-property-trunc-Set :
  {l1 l2 : Level} (A : UU l1) (B : UU-Set l2) →
  (type-trunc-Set A → type-Set B) ≃ (A → type-Set B)
equiv-universal-property-trunc-Set A B =
  pair
    ( precomp-Set unit-trunc-Set B)
    ( is-set-truncation-trunc-Set A B)

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

triangle-universal-property-trunc-Set :
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) →
  (f : A → type-Set B) →
  (map-universal-property-trunc-Set B f ∘ unit-trunc-Set) ~ f
triangle-universal-property-trunc-Set {A = A} B f =
  triangle-is-set-truncation
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

apply-dependent-universal-property-trunc-Set :
  {l1 l2 : Level} {A : UU l1}
  (B : type-trunc-Set A → UU-Set l2) →
  ((x : A) → type-Set (B (unit-trunc-Set x))) →
  (x : type-trunc-Set A) → type-Set (B x)
apply-dependent-universal-property-trunc-Set B =
  map-inv-equiv (equiv-dependent-universal-property-trunc-Set B)

reflecting-map-mere-eq-unit-trunc-Set :
  {l : Level} (A : UU l) →
  reflecting-map-Eq-Rel (mere-eq-Eq-Rel A) (type-trunc-Set A)
reflecting-map-mere-eq-unit-trunc-Set A =
  pair unit-trunc-Set (reflects-mere-eq (trunc-Set A) unit-trunc-Set)

is-set-quotient-trunc-Set :
  {l1 l2 : Level} (A : UU l1) →
  is-set-quotient l2
    ( mere-eq-Eq-Rel A)
    ( trunc-Set A)
    ( reflecting-map-mere-eq-unit-trunc-Set A)
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
    ( reflects-mere-eq (trunc-Set A) unit-trunc-Set)
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

apply-effectiveness-unit-trunc-Set :
  {l1 : Level} {A : UU l1} {x y : A} →
  Id (unit-trunc-Set x) (unit-trunc-Set y) → mere-eq x y
apply-effectiveness-unit-trunc-Set {A = A} {x} {y} =
  map-equiv (is-effective-unit-trunc-Set A x y)

apply-effectiveness-unit-trunc-Set' :
  {l1 : Level} {A : UU l1} {x y : A} →
  mere-eq x y → Id (unit-trunc-Set x) (unit-trunc-Set y)
apply-effectiveness-unit-trunc-Set' {A = A} {x} {y} =
  map-inv-equiv (is-effective-unit-trunc-Set A x y)

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
  is-image l2
    ( mere-eq-Prop {A = A})
    ( emb-trunc-Set A)
    ( hom-slice-trunc-Set A)
is-image-trunc-Set A =
  is-image-is-surjective-and-effective
    ( mere-eq-Eq-Rel A)
    ( trunc-Set A)
    ( unit-trunc-Set)
    ( is-surjective-and-effective-unit-trunc-Set A)

module _
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B)
  {h : type-hom-Set B (trunc-Set A)} (H : (h ∘ f) ~ unit-trunc-Set)
  where

  is-equiv-is-set-truncation' :
    ({l : Level} → is-set-truncation l B f) → is-equiv h
  is-equiv-is-set-truncation' Sf =
    is-equiv-is-set-truncation-is-set-truncation
      ( B)
      ( f)
      ( trunc-Set A)
      ( unit-trunc-Set)
      ( H)
      ( Sf)
      ( λ {h} → is-set-truncation-trunc-Set A)

  is-set-truncation-is-equiv' :
    is-equiv h → ({l : Level} → is-set-truncation l B f)
  is-set-truncation-is-equiv' Eh =
    is-set-truncation-is-equiv-is-set-truncation
      ( B)
      ( f)
      ( trunc-Set A)
      ( unit-trunc-Set)
      ( H)
      ( λ {l} → is-set-truncation-trunc-Set A)
      ( Eh)

module _
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B)
  {h : type-hom-Set (trunc-Set A) B} (H : (h ∘ unit-trunc-Set) ~ f)
  where

  is-equiv-is-set-truncation :
    ({l : Level} → is-set-truncation l B f) → is-equiv h
  is-equiv-is-set-truncation Sf =
    is-equiv-is-set-truncation-is-set-truncation
      ( trunc-Set A)
      ( unit-trunc-Set)
      ( B)
      ( f)
      ( H)
      ( λ {l} → is-set-truncation-trunc-Set A)
      ( Sf)

  is-set-truncation-is-equiv :
    is-equiv h → ({l : Level} → is-set-truncation l B f)
  is-set-truncation-is-equiv Eh =
    is-set-truncation-is-set-truncation-is-equiv
      ( trunc-Set A)
      ( unit-trunc-Set)
      ( B)
      ( f)
      ( H)
      ( Eh)
      ( λ {l} → is-set-truncation-trunc-Set A)

is-equiv-unit-trunc-Set :
  {l : Level} (A : UU-Set l) → is-equiv (unit-trunc-Set {A = type-Set A})
is-equiv-unit-trunc-Set A =
  is-equiv-is-set-truncation' A id refl-htpy
    ( is-set-truncation-id (is-set-type-Set A))

equiv-unit-trunc-Set :
  {l : Level} (A : UU-Set l) → type-Set A ≃ type-trunc-Set (type-Set A)
equiv-unit-trunc-Set A =
  pair unit-trunc-Set (is-equiv-unit-trunc-Set A)

equiv-unit-trunc-empty-Set : empty ≃ type-trunc-Set empty
equiv-unit-trunc-empty-Set = equiv-unit-trunc-Set empty-Set

is-empty-trunc-Set :
  {l : Level} {A : UU l} → is-empty A → is-empty (type-trunc-Set A)
is-empty-trunc-Set f x = apply-universal-property-trunc-Set x empty-Set f

is-empty-is-empty-trunc-Set :
  {l : Level} {A : UU l} → is-empty (type-trunc-Set A) → is-empty A
is-empty-is-empty-trunc-Set f = f ∘ unit-trunc-Set

equiv-unit-trunc-unit-Set : unit ≃ type-trunc-Set unit
equiv-unit-trunc-unit-Set = equiv-unit-trunc-Set unit-Set

equiv-unit-trunc-ℕ-Set : ℕ ≃ type-trunc-Set ℕ
equiv-unit-trunc-ℕ-Set = equiv-unit-trunc-Set ℕ-Set

equiv-unit-trunc-ℤ-Set : ℤ ≃ type-trunc-Set ℤ
equiv-unit-trunc-ℤ-Set = equiv-unit-trunc-Set ℤ-Set

equiv-unit-trunc-Fin-Set : (k : ℕ) → Fin k ≃ type-trunc-Set (Fin k)
equiv-unit-trunc-Fin-Set k = equiv-unit-trunc-Set (Fin-Set k)

is-contr-trunc-Set :
  {l : Level} {A : UU l} → is-contr A → is-contr (type-trunc-Set A)
is-contr-trunc-Set {l} {A} H =
  is-contr-equiv'
    ( A)
    ( equiv-unit-trunc-Set (pair A (is-set-is-contr H)))
    ( H)

module _
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B)
  (Sf : {l : Level} → is-set-truncation l B f)
  where

  uniqueness-trunc-Set :
    is-contr
      ( Σ (type-trunc-Set A ≃ type-Set B)
      ( λ e → (map-equiv e ∘ unit-trunc-Set) ~ f))
  uniqueness-trunc-Set =
    uniqueness-set-truncation (trunc-Set A) unit-trunc-Set B f
      ( λ {l} → is-set-truncation-trunc-Set A)
      ( Sf)

  equiv-uniqueness-trunc-Set : type-trunc-Set A ≃ type-Set B
  equiv-uniqueness-trunc-Set =
    pr1 (center uniqueness-trunc-Set)

  map-equiv-uniqueness-trunc-Set : type-trunc-Set A → type-Set B
  map-equiv-uniqueness-trunc-Set =
    map-equiv equiv-uniqueness-trunc-Set

  triangle-uniqueness-trunc-Set :
    (map-equiv-uniqueness-trunc-Set ∘ unit-trunc-Set) ~ f
  triangle-uniqueness-trunc-Set =
    pr2 (center uniqueness-trunc-Set)

module _
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B)
  (Sf : {l : Level} → is-set-truncation l B f)
  where

  uniqueness-trunc-Set' :
    is-contr
      ( Σ ( type-Set B ≃ type-trunc-Set A)
          ( λ e → (map-equiv e ∘ f) ~ unit-trunc-Set))
  uniqueness-trunc-Set' =
    uniqueness-set-truncation B f (trunc-Set A) unit-trunc-Set Sf
      ( λ {l} → is-set-truncation-trunc-Set A)

  equiv-uniqueness-trunc-Set' : type-Set B ≃ type-trunc-Set A
  equiv-uniqueness-trunc-Set' =
    pr1 (center uniqueness-trunc-Set')

  map-equiv-uniqueness-trunc-Set' : type-Set B → type-trunc-Set A
  map-equiv-uniqueness-trunc-Set' =
    map-equiv equiv-uniqueness-trunc-Set'
  
  triangle-uniqueness-trunc-Set' :
    (map-equiv-uniqueness-trunc-Set' ∘ f) ~ unit-trunc-Set
  triangle-uniqueness-trunc-Set' =
    pr2 (center uniqueness-trunc-Set')

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  unique-map-trunc-Set :
    is-contr
      ( Σ ( type-trunc-Set A → type-trunc-Set B)
          ( λ h → (h ∘ unit-trunc-Set) ~ (unit-trunc-Set ∘ f)))
  unique-map-trunc-Set =
    universal-property-trunc-Set A (trunc-Set B) (unit-trunc-Set ∘ f)

  map-trunc-Set :
    type-trunc-Set A → type-trunc-Set B
  map-trunc-Set =
    pr1 (center unique-map-trunc-Set)

  naturality-trunc-Set :
    (map-trunc-Set ∘ unit-trunc-Set) ~ (unit-trunc-Set ∘ f)
  naturality-trunc-Set =
    pr2 (center unique-map-trunc-Set)

  htpy-map-trunc-Set :
    (h : type-trunc-Set A → type-trunc-Set B) →
    (H : (h ∘ unit-trunc-Set) ~ (unit-trunc-Set ∘ f)) →
    map-trunc-Set ~ h
  htpy-map-trunc-Set h H =
    htpy-eq
      ( ap pr1
        ( eq-is-contr unique-map-trunc-Set
          { pair map-trunc-Set naturality-trunc-Set}
          { pair h H}))

map-id-trunc-Set :
  {l1 : Level} {A : UU l1} → map-trunc-Set (id {A = A}) ~ id
map-id-trunc-Set {l1} {A} =
  htpy-eq
    ( ap pr1
      ( eq-is-contr
        ( universal-property-trunc-Set A (trunc-Set A) unit-trunc-Set)
        { pair (map-trunc-Set id) (naturality-trunc-Set id)}
        { pair id refl-htpy}))

map-comp-trunc-Set :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B) →
  map-trunc-Set (g ∘ f) ~ (map-trunc-Set g ∘ map-trunc-Set f)
map-comp-trunc-Set {A = A} {C = C} g f =
  htpy-eq
    ( ap pr1
      ( eq-is-contr
        ( universal-property-trunc-Set
          A
          (trunc-Set C)
          (unit-trunc-Set ∘ (g ∘ f)))
        { pair (map-trunc-Set (g ∘ f)) (naturality-trunc-Set (g ∘ f))}
        { pair ( map-trunc-Set g ∘ map-trunc-Set f)
               ( ( map-trunc-Set g ·l naturality-trunc-Set f) ∙h
                 ( naturality-trunc-Set g ·r f))}))

htpy-trunc-Set :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} →
  (f ~ g) → (map-trunc-Set f ~ map-trunc-Set g)
htpy-trunc-Set {B = B} {f = f} {g} H =
  map-inv-is-equiv
    ( dependent-universal-property-trunc-Set
      ( λ x →
        set-Prop
          ( Id-Prop (trunc-Set B) (map-trunc-Set f x) (map-trunc-Set g x))))
    ( λ a →
      ( naturality-trunc-Set f a) ∙
      ( ( ap unit-trunc-Set (H a)) ∙
        ( inv (naturality-trunc-Set g a))))

is-equiv-map-trunc-Set :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-equiv f → is-equiv (map-trunc-Set f)
is-equiv-map-trunc-Set {f = f} H =
  pair
    ( pair
      ( map-trunc-Set (pr1 (pr1 H)))
      ( ( inv-htpy (map-comp-trunc-Set f (pr1 (pr1 H)))) ∙h
        ( ( htpy-trunc-Set (pr2 (pr1 H))) ∙h
          ( map-id-trunc-Set))))
    ( pair
      ( map-trunc-Set (pr1 (pr2 H)))
      ( ( inv-htpy (map-comp-trunc-Set (pr1 (pr2 H)) f)) ∙h
        ( ( htpy-trunc-Set (pr2 (pr2 H))) ∙h
          ( map-id-trunc-Set))))

equiv-trunc-Set :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → (type-trunc-Set A ≃ type-trunc-Set B)
equiv-trunc-Set e =
  pair
    ( map-trunc-Set (map-equiv e))
    ( is-equiv-map-trunc-Set (is-equiv-map-equiv e))

map-equiv-trunc-Set :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → type-trunc-Set A → type-trunc-Set B
map-equiv-trunc-Set e = map-equiv (equiv-trunc-Set e)

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where
  
  distributive-trunc-coprod-Set :
    is-contr
      ( Σ ( type-equiv-Set
            ( trunc-Set (coprod A B))
            ( coprod-Set (trunc-Set A) (trunc-Set B)))
          ( λ e →
            ( map-equiv e ∘ unit-trunc-Set) ~
            ( map-coprod unit-trunc-Set unit-trunc-Set)))
  distributive-trunc-coprod-Set =
    uniqueness-trunc-Set
      ( coprod-Set (trunc-Set A) (trunc-Set B))
      ( map-coprod unit-trunc-Set unit-trunc-Set)
      ( λ {l} C →
        is-equiv-right-factor'
          ( ev-inl-inr (λ x → type-Set C))
          ( precomp-Set (map-coprod unit-trunc-Set unit-trunc-Set) C)
          ( universal-property-coprod (type-Set C))
          ( is-equiv-comp'
            ( map-prod
              ( precomp-Set unit-trunc-Set C)
              ( precomp-Set unit-trunc-Set C))
            ( ev-inl-inr (λ x → type-Set C))
            ( universal-property-coprod (type-Set C))
            ( is-equiv-map-prod
              ( precomp-Set unit-trunc-Set C)
              ( precomp-Set unit-trunc-Set C)
              ( is-set-truncation-trunc-Set A C)
              ( is-set-truncation-trunc-Set B C))))

  equiv-distributive-trunc-coprod-Set :
    type-equiv-Set
      ( trunc-Set (coprod A B))
      ( coprod-Set (trunc-Set A) (trunc-Set B))
  equiv-distributive-trunc-coprod-Set =
    pr1 (center distributive-trunc-coprod-Set)

  map-equiv-distributive-trunc-coprod-Set :
    type-hom-Set
      ( trunc-Set (coprod A B))
      ( coprod-Set (trunc-Set A) (trunc-Set B))
  map-equiv-distributive-trunc-coprod-Set =
    map-equiv equiv-distributive-trunc-coprod-Set

  triangle-distributive-trunc-coprod-Set :
    ( map-equiv-distributive-trunc-coprod-Set ∘ unit-trunc-Set) ~
    ( map-coprod unit-trunc-Set unit-trunc-Set)
  triangle-distributive-trunc-coprod-Set =
    pr2 (center distributive-trunc-coprod-Set)

module _
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2)
  where
  
  trunc-Σ-Set :
    is-contr
      ( Σ ( type-trunc-Set (Σ A B) ≃
            type-trunc-Set (Σ A (λ x → type-trunc-Set (B x))))
          ( λ e →
            ( map-equiv e ∘ unit-trunc-Set) ~
            ( unit-trunc-Set ∘ tot (λ x → unit-trunc-Set))))
  trunc-Σ-Set =
    uniqueness-trunc-Set
      ( trunc-Set (Σ A (λ x → type-trunc-Set (B x))))
      ( unit-trunc-Set ∘ tot (λ x → unit-trunc-Set))
      ( λ {l} C →
        is-equiv-right-factor'
          ( ev-pair)
          ( precomp-Set (unit-trunc-Set ∘ tot (λ x → unit-trunc-Set)) C)
          ( is-equiv-ev-pair)
          ( is-equiv-htpy-equiv
            ( ( equiv-map-Π
                ( λ x → equiv-universal-property-trunc-Set (B x) C)) ∘e
              ( ( equiv-ev-pair) ∘e
                ( equiv-universal-property-trunc-Set
                  ( Σ A (type-trunc-Set ∘ B)) C)))
            ( refl-htpy)))

  equiv-trunc-Σ-Set :
    type-trunc-Set (Σ A B) ≃ type-trunc-Set (Σ A (λ x → type-trunc-Set (B x)))
  equiv-trunc-Σ-Set =
    pr1 (center trunc-Σ-Set)

  map-equiv-trunc-Σ-Set :
    type-trunc-Set (Σ A B) → type-trunc-Set (Σ A (λ x → type-trunc-Set (B x)))
  map-equiv-trunc-Σ-Set =
    map-equiv equiv-trunc-Σ-Set

  square-trunc-Σ-Set :
    ( map-equiv-trunc-Σ-Set ∘ unit-trunc-Set) ~
    ( unit-trunc-Set ∘ tot (λ x → unit-trunc-Set))
  square-trunc-Σ-Set =
    pr2 (center trunc-Σ-Set)

  htpy-map-equiv-trunc-Σ-Set :
    map-trunc-Set (tot (λ x → unit-trunc-Set)) ~ map-equiv-trunc-Σ-Set
  htpy-map-equiv-trunc-Σ-Set =
    htpy-map-trunc-Set
      ( tot (λ x → unit-trunc-Set))
      ( map-equiv-trunc-Σ-Set)
      ( square-trunc-Σ-Set)

  is-equiv-map-trunc-tot-unit-trunc-Set :
    is-equiv (map-trunc-Set (tot (λ (x : A) → unit-trunc-Set {A = B x})))
  is-equiv-map-trunc-tot-unit-trunc-Set =
    is-equiv-htpy-equiv
      ( equiv-trunc-Σ-Set)
      ( htpy-map-equiv-trunc-Σ-Set)

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  distributive-trunc-prod-Set :
    is-contr
      ( Σ ( type-trunc-Set (A × B) ≃ ( type-trunc-Set A × type-trunc-Set B))
          ( λ e →
            ( map-equiv e ∘ unit-trunc-Set) ~
            ( map-prod unit-trunc-Set unit-trunc-Set)))
  distributive-trunc-prod-Set =
    uniqueness-trunc-Set
      ( prod-Set (trunc-Set A) (trunc-Set B))
      ( map-prod unit-trunc-Set unit-trunc-Set)
      ( λ {l} C →
        is-equiv-right-factor'
          ( ev-pair)
          ( precomp-Set (map-prod unit-trunc-Set unit-trunc-Set) C)
          ( is-equiv-ev-pair)
          ( is-equiv-htpy-equiv
            ( ( equiv-universal-property-trunc-Set A (Π-Set' B (λ y → C))) ∘e
              ( ( equiv-postcomp
                  ( type-trunc-Set A)
                  (equiv-universal-property-trunc-Set B C)) ∘e
                ( equiv-ev-pair)))
            ( refl-htpy)))

  equiv-distributive-trunc-prod-Set :
    type-trunc-Set (A × B) ≃ ( type-trunc-Set A × type-trunc-Set B)
  equiv-distributive-trunc-prod-Set =
    pr1 (center distributive-trunc-prod-Set)

  map-equiv-distributive-trunc-prod-Set :
    type-trunc-Set (A × B) → type-trunc-Set A × type-trunc-Set B
  map-equiv-distributive-trunc-prod-Set =
    map-equiv equiv-distributive-trunc-prod-Set

  triangle-distributive-trunc-prod-Set :
    ( map-equiv-distributive-trunc-prod-Set ∘ unit-trunc-Set) ~
    ( map-prod unit-trunc-Set unit-trunc-Set)
  triangle-distributive-trunc-prod-Set =
    pr2 (center distributive-trunc-prod-Set)

distributive-trunc-Π-Fin-Set :
  {l : Level} (k : ℕ) (A : Fin k → UU l) →
  is-contr
    ( Σ ( ( type-trunc-Set ((x : Fin k) → A x)) ≃
          ( (x : Fin k) → type-trunc-Set (A x)))
        ( λ e →
          ( map-equiv e ∘ unit-trunc-Set) ~
          ( map-Π (λ x → unit-trunc-Set))))
distributive-trunc-Π-Fin-Set zero-ℕ A =
  uniqueness-trunc-Set
    ( Π-Set empty-Set (λ x → trunc-Set (A x)))
    ( map-Π (λ x → unit-trunc-Set))
    ( λ {l} B →
      is-equiv-precomp-is-equiv
        ( map-Π (λ x → unit-trunc-Set))
        ( is-equiv-is-contr
          ( map-Π (λ x → unit-trunc-Set))
          ( dependent-universal-property-empty' A)
          ( dependent-universal-property-empty' (type-trunc-Set ∘ A)))
        ( type-Set B))
distributive-trunc-Π-Fin-Set (succ-ℕ k) A =
  uniqueness-trunc-Set
    ( Π-Set (Fin-Set (succ-ℕ k)) (λ x → trunc-Set (A x)))
    ( map-Π (λ x → unit-trunc-Set))
    ( λ {l} B →
      is-equiv-left-factor'
        ( precomp (map-Π (λ x → unit-trunc-Set)) (type-Set B))
        ( precomp (ev-Maybe {B = type-trunc-Set ∘ A}) (type-Set B))
        ( is-equiv-comp'
          ( precomp ev-Maybe (type-Set B))
          ( precomp
            ( map-prod (map-Π (λ x → unit-trunc-Set)) unit-trunc-Set)
            ( type-Set B))
          ( is-equiv-right-factor'
            ( ev-pair)
            ( precomp
              ( map-prod (map-Π (λ x → unit-trunc-Set)) unit-trunc-Set)
              ( type-Set B))
            ( is-equiv-ev-pair)
            ( is-equiv-htpy-equiv
              ( ( ( pair
                    ( precomp
                      ( (map-Π (λ x → unit-trunc-Set)))
                      ( A (inr star) → type-Set B))
                    ( is-set-truncation-is-equiv
                      ( Π-Set (Fin-Set k) (λ x → trunc-Set (A (inl x))))
                      ( map-Π (λ x → unit-trunc-Set))
                      { map-equiv
                        ( pr1
                          ( center
                            ( distributive-trunc-Π-Fin-Set k (A ∘ inl))))}
                      ( pr2
                        ( center (distributive-trunc-Π-Fin-Set k (A ∘ inl))))
                      ( is-equiv-map-equiv
                        ( pr1
                          ( center
                            ( distributive-trunc-Π-Fin-Set k (A ∘ inl)))))
                      ( Π-Set' (A (inr star)) (λ a → B)))) ∘e
                  ( equiv-postcomp
                    ( (x : Fin k) → type-trunc-Set (A (inl x)))
                    ( equiv-universal-property-trunc-Set (A (inr star)) B))) ∘e
                ( equiv-ev-pair))
              ( refl-htpy)))
          ( is-equiv-precomp-is-equiv
            ( ev-Maybe)
            ( dependent-universal-property-Maybe)
            ( type-Set B)))
        ( is-equiv-precomp-is-equiv
          ( ev-Maybe)
          ( dependent-universal-property-Maybe)
          ( type-Set B)))

module _
  {l : Level} (k : ℕ) (A : Fin k → UU l)
  where

  equiv-distributive-trunc-Π-Fin-Set :
    type-trunc-Set ((x : Fin k) → A x) ≃ ((x : Fin k) → type-trunc-Set (A x))
  equiv-distributive-trunc-Π-Fin-Set =
    pr1 (center (distributive-trunc-Π-Fin-Set k A))

  map-equiv-distributive-trunc-Π-Fin-Set :
    type-trunc-Set ((x : Fin k) → A x) → ((x : Fin k) → type-trunc-Set (A x))
  map-equiv-distributive-trunc-Π-Fin-Set =
    map-equiv equiv-distributive-trunc-Π-Fin-Set

  triangle-distributive-trunc-Π-Fin-Set :
    ( map-equiv-distributive-trunc-Π-Fin-Set ∘ unit-trunc-Set) ~
    ( map-Π (λ x → unit-trunc-Set))
  triangle-distributive-trunc-Π-Fin-Set =
    pr2 (center (distributive-trunc-Π-Fin-Set k A))

module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (c : count A)
  where
  
  distributive-trunc-Π-count-Set :
    is-contr
      ( Σ ( ( type-trunc-Set ((x : A) → B x)) ≃
            ( (x : A) → type-trunc-Set (B x)))
          ( λ e →
            ( map-equiv e ∘ unit-trunc-Set) ~
            ( map-Π (λ x → unit-trunc-Set))))
  distributive-trunc-Π-count-Set =
    is-contr-equiv
      ( Σ ( ( type-trunc-Set ((x : A) → B x)) ≃
            ( (x : Fin k) → type-trunc-Set (B (map-equiv e x))))
          ( λ f →
            ( map-equiv f ∘ unit-trunc-Set) ~
            ( map-Π (λ x → unit-trunc-Set) ∘ precomp-Π (map-equiv e) B)))
      ( equiv-Σ
        ( λ f →
          ( map-equiv f ∘ unit-trunc-Set) ~
          ( map-Π (λ x → unit-trunc-Set) ∘ precomp-Π (map-equiv e) B))
        ( equiv-postcomp-equiv
          ( equiv-precomp-Π e (type-trunc-Set ∘ B))
          ( type-trunc-Set ((x : A) → B x)))
        ( λ f →
          equiv-map-Π
            ( λ h →
              ( ( inv-equiv equiv-funext) ∘e
                ( equiv-precomp-Π e
                  ( λ x → Id ((map-equiv f ∘ unit-trunc-Set) h x)
                  ( map-Π (λ y → unit-trunc-Set) h x)))) ∘e
              ( equiv-funext))))
      ( is-contr-equiv'
        ( Σ ( ( type-trunc-Set ((x : Fin k) → B (map-equiv e x))) ≃
              ( (x : Fin k) → type-trunc-Set (B (map-equiv e x))))
            ( λ f →
              ( map-equiv f ∘ unit-trunc-Set) ~
              ( map-Π (λ x → unit-trunc-Set))))
        ( equiv-Σ
          ( λ f →
            ( map-equiv f ∘ unit-trunc-Set) ~
            ( map-Π (λ x → unit-trunc-Set) ∘ precomp-Π (map-equiv e) B))
          ( equiv-precomp-equiv
            ( equiv-trunc-Set (equiv-precomp-Π e B))
            ( (x : Fin k) → type-trunc-Set (B (map-equiv e x))))
          ( λ f →
            equiv-Π
              ( λ h →
                Id ( map-equiv f
                     ( map-equiv
                       ( equiv-trunc-Set (equiv-precomp-Π e B))
                       ( unit-trunc-Set h)))
                   ( map-Π (λ x → unit-trunc-Set) (λ x → h (map-equiv e x))))
              ( equiv-Π B e (λ x → equiv-id))
              ( λ h →
                ( ( inv-equiv equiv-funext) ∘e
                  ( equiv-Π
                    ( λ x →
                      Id ( map-equiv f
                           ( map-equiv-trunc-Set
                             ( equiv-precomp-Π e B)
                             ( unit-trunc-Set
                               ( map-equiv-Π B e (λ x → equiv-id) h)))
                           ( x))
                         ( unit-trunc-Set
                           ( map-equiv-Π B e
                             ( λ z → equiv-id)
                             ( h)
                             ( map-equiv e x))))
                    ( equiv-id)
                    ( λ x →
                      ( equiv-concat
                        ( ap
                          ( λ t → map-equiv f t x)
                          ( ( naturality-trunc-Set (precomp-Π (map-equiv e) B)
                              ( map-equiv-Π B e (λ _ → equiv-id) h)) ∙
                            ( ap
                              ( unit-trunc-Set)
                              ( eq-htpy
                                ( compute-map-equiv-Π B e
                                  ( λ _ → equiv-id)
                                  ( h))))))
                        ( unit-trunc-Set
                          ( map-equiv-Π B e
                            ( λ _ → equiv-id)
                            ( h)
                            ( map-equiv e x)))) ∘e
                      ( equiv-concat'
                        ( map-equiv f (unit-trunc-Set h) x)
                        ( ap unit-trunc-Set
                          ( inv
                            ( compute-map-equiv-Π B e
                              ( λ _ → equiv-id)
                              ( h)
                              ( x)))))))) ∘e
                ( equiv-funext))))
        ( distributive-trunc-Π-Fin-Set k (B ∘ map-equiv e)))
    where
    k = pr1 c
    e = pr2 c

  equiv-distributive-trunc-Π-count-Set :
    ( type-trunc-Set ((x : A) → B x)) ≃ ((x : A) → type-trunc-Set (B x))
  equiv-distributive-trunc-Π-count-Set =
    pr1 (center distributive-trunc-Π-count-Set)

  map-equiv-distributive-trunc-Π-count-Set :
    ( type-trunc-Set ((x : A) → B x)) → ((x : A) → type-trunc-Set (B x))
  map-equiv-distributive-trunc-Π-count-Set =
    map-equiv equiv-distributive-trunc-Π-count-Set

  triangle-distributive-trunc-Π-count-Set :
    ( map-equiv-distributive-trunc-Π-count-Set ∘ unit-trunc-Set) ~
    ( map-Π (λ x → unit-trunc-Set))
  triangle-distributive-trunc-Π-count-Set =
    pr2 (center distributive-trunc-Π-count-Set)

module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (H : is-finite A)
  where
  
  distributive-trunc-Π-is-finite-Set :
    is-contr
      ( Σ ( ( type-trunc-Set ((x : A) → B x)) ≃
            ( (x : A) → type-trunc-Set (B x)))
          ( λ e →
            ( map-equiv e ∘ unit-trunc-Set) ~
            ( map-Π (λ x → unit-trunc-Set))))
  distributive-trunc-Π-is-finite-Set =
    apply-universal-property-trunc-Prop H
      ( is-contr-Prop _)
      ( distributive-trunc-Π-count-Set B)

  equiv-distributive-trunc-Π-is-finite-Set :
    ( type-trunc-Set ((x : A) → B x)) ≃ ((x : A) → type-trunc-Set (B x))
  equiv-distributive-trunc-Π-is-finite-Set =
    pr1 (center distributive-trunc-Π-is-finite-Set)

  map-equiv-distributive-trunc-Π-is-finite-Set :
    ( type-trunc-Set ((x : A) → B x)) → ((x : A) → type-trunc-Set (B x))
  map-equiv-distributive-trunc-Π-is-finite-Set =
    map-equiv equiv-distributive-trunc-Π-is-finite-Set

  triangle-distributive-trunc-Π-is-finite-Set :
    ( map-equiv-distributive-trunc-Π-is-finite-Set ∘ unit-trunc-Set) ~
    ( map-Π (λ x → unit-trunc-Set))
  triangle-distributive-trunc-Π-is-finite-Set =
    pr2 (center distributive-trunc-Π-is-finite-Set)

is-path-connected-Prop : {l : Level} → UU l → UU-Prop l
is-path-connected-Prop A = is-contr-Prop (type-trunc-Set A)

is-path-connected : {l : Level} → UU l → UU l
is-path-connected A = type-Prop (is-path-connected-Prop A)

is-inhabited-is-path-connected :
  {l : Level} {A : UU l} → is-path-connected A → type-trunc-Prop A
is-inhabited-is-path-connected {l} {A} C =
  apply-universal-property-trunc-Set
    ( center C)
    ( set-Prop (trunc-Prop A))
    ( unit-trunc-Prop)

mere-eq-is-path-connected :
  {l : Level} {A : UU l} → is-path-connected A → (x y : A) → mere-eq x y
mere-eq-is-path-connected {A = A} H x y =
  apply-effectiveness-unit-trunc-Set (eq-is-contr H)

is-path-connected-mere-eq :
  {l : Level} {A : UU l} (a : A) → ((x : A) → mere-eq a x) → is-path-connected A
is-path-connected-mere-eq {l} {A} a e =
  pair
    ( unit-trunc-Set a)
    ( apply-dependent-universal-property-trunc-Set
        ( λ x → set-Prop (Id-Prop (trunc-Set A) (unit-trunc-Set a) x))
        ( λ x → apply-effectiveness-unit-trunc-Set' (e x)))

is-surjective-fiber-inclusion :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-path-connected A → (a : A) → is-surjective (fiber-inclusion B a)
is-surjective-fiber-inclusion {B = B} C a (pair x b) =
  apply-universal-property-trunc-Prop
    ( mere-eq-is-path-connected C a x)
    ( trunc-Prop (fib (fiber-inclusion B a) (pair x b)))
    ( λ { refl → unit-trunc-Prop (pair b refl)})

mere-eq-is-surjective-fiber-inclusion :
  {l1 : Level} {A : UU l1} (a : A) →
  ({l : Level} (B : A → UU l) → is-surjective (fiber-inclusion B a)) →
  (x : A) → mere-eq a x
mere-eq-is-surjective-fiber-inclusion a H x =
  apply-universal-property-trunc-Prop
    ( H (λ x → unit) (pair x star))
    ( mere-eq-Prop a x)
    ( λ u → unit-trunc-Prop (ap pr1 (pr2 u)))

is-path-connected-is-surjective-fiber-inclusion :
  {l1 : Level} {A : UU l1} (a : A) →
  ({l : Level} (B : A → UU l) → is-surjective (fiber-inclusion B a)) →
  is-path-connected A
is-path-connected-is-surjective-fiber-inclusion a H =
  is-path-connected-mere-eq a (mere-eq-is-surjective-fiber-inclusion a H)

mere-eq-mere-equiv :
  {l : Level} {A B : UU l} → mere-equiv A B → mere-eq A B
mere-eq-mere-equiv {l} {A} {B} = functor-trunc-Prop (eq-equiv A B)

is-path-connected-UU-Fin-Level :
  {l : Level} (n : ℕ) → is-path-connected (UU-Fin-Level l n)
is-path-connected-UU-Fin-Level {l} n =
  is-path-connected-mere-eq
    ( Fin-UU-Fin-Level l n)
    ( λ A →
      functor-trunc-Prop
        ( ( eq-equiv-UU-Fin-Level (Fin-UU-Fin-Level l n) A) ∘
          ( map-equiv
            ( equiv-precomp-equiv
              ( inv-equiv (equiv-raise l (Fin n)))
              ( type-UU-Fin-Level A))))
        ( pr2 A))

is-path-connected-UU-Fin :
  (n : ℕ) → is-path-connected (UU-Fin n)
is-path-connected-UU-Fin n =
  is-path-connected-mere-eq
    ( Fin-UU-Fin n)
    ( λ A → functor-trunc-Prop (eq-equiv-UU-Fin (Fin-UU-Fin n) A) (pr2 A))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where
  
  is-injective-map-trunc-Set :
    is-injective f → is-injective (map-trunc-Set f)
  is-injective-map-trunc-Set H {x} {y} =
    apply-dependent-universal-property-trunc-Set
      ( λ u →
        set-Prop
          ( function-Prop (Id (map-trunc-Set f u) (map-trunc-Set f y))
          ( Id-Prop (trunc-Set A) u y) ))
      ( λ a →
        apply-dependent-universal-property-trunc-Set
        ( λ v →
          set-Prop
            ( function-Prop
              ( Id (map-trunc-Set f (unit-trunc-Set a)) (map-trunc-Set f v))
              ( Id-Prop (trunc-Set A) (unit-trunc-Set a) v)))
        ( λ b p →
          apply-universal-property-trunc-Prop
            ( apply-effectiveness-unit-trunc-Set
              ( ( inv (naturality-trunc-Set f a)) ∙
                ( p ∙ (naturality-trunc-Set f b))))
            ( Id-Prop (trunc-Set A) (unit-trunc-Set a) (unit-trunc-Set b))
            ( λ q → ap unit-trunc-Set (H q)))
        ( y))
      ( x)

  is-surjective-map-trunc-Set :
    is-surjective f → is-surjective (map-trunc-Set f)
  is-surjective-map-trunc-Set H =
    apply-dependent-universal-property-trunc-Set
      ( λ x → set-Prop (trunc-Prop (fib (map-trunc-Set f) x)))
      ( λ b →
        apply-universal-property-trunc-Prop
          ( H b)
          ( trunc-Prop (fib (map-trunc-Set f) (unit-trunc-Set b)))
          ( λ { (pair a p) →
                unit-trunc-Prop
                  ( pair
                    ( unit-trunc-Set a)
                    ( naturality-trunc-Set f a ∙ ap unit-trunc-Set p))}))

  is-surjective-is-surjective-map-trunc-Set :
    is-surjective (map-trunc-Set f) → is-surjective f
  is-surjective-is-surjective-map-trunc-Set H b =
    apply-universal-property-trunc-Prop
      ( H (unit-trunc-Set b))
      ( trunc-Prop (fib f b))
      ( λ { (pair x p) →
            apply-universal-property-trunc-Prop
              ( is-surjective-unit-trunc-Set A x)
              ( trunc-Prop (fib f b))
              ( λ { (pair a refl) →
                    apply-universal-property-trunc-Prop
                      ( apply-effectiveness-unit-trunc-Set
                        ( inv (naturality-trunc-Set f a) ∙ p))
                      ( trunc-Prop (fib f b))
                      ( λ q → unit-trunc-Prop (pair a q))})})

im-Set :
  {l1 l2 : Level} {A : UU l2} (X : UU-Set l1) (f : A → type-Set X) →
  UU-Set (l1 ⊔ l2)
im-Set X f = pair (im f) (is-set-im f (is-set-type-Set X))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  inclusion-trunc-im-Set : type-trunc-Set (im f) → type-trunc-Set B
  inclusion-trunc-im-Set = map-trunc-Set (inclusion-im f)

  is-emb-inclusion-trunc-im-Set : is-emb inclusion-trunc-im-Set
  is-emb-inclusion-trunc-im-Set =
    is-emb-is-injective
      ( is-set-type-trunc-Set)
      ( is-injective-map-trunc-Set
        ( inclusion-im f)
        ( is-injective-is-emb (is-emb-inclusion-im f)))

  emb-trunc-im-Set : type-trunc-Set (im f) ↪ type-trunc-Set B
  emb-trunc-im-Set = pair inclusion-trunc-im-Set is-emb-inclusion-trunc-im-Set

  is-injective-inclusion-trunc-im-Set : is-injective inclusion-trunc-im-Set
  is-injective-inclusion-trunc-im-Set =
    is-injective-is-emb is-emb-inclusion-trunc-im-Set

  map-hom-slice-trunc-im-Set : type-trunc-Set A → type-trunc-Set (im f)
  map-hom-slice-trunc-im-Set = map-trunc-Set (map-unit-im f)

  triangle-hom-slice-trunc-im-Set :
    map-trunc-Set f ~ (inclusion-trunc-im-Set ∘ map-trunc-Set (map-unit-im f))
  triangle-hom-slice-trunc-im-Set =
    ( htpy-trunc-Set (triangle-unit-im f)) ∙h
    ( map-comp-trunc-Set (inclusion-im f) (map-unit-im f))

  hom-slice-trunc-im-Set : hom-slice (map-trunc-Set f) inclusion-trunc-im-Set
  hom-slice-trunc-im-Set =
    pair map-hom-slice-trunc-im-Set triangle-hom-slice-trunc-im-Set

  is-surjective-map-hom-slice-trunc-im-Set :
    is-surjective map-hom-slice-trunc-im-Set
  is-surjective-map-hom-slice-trunc-im-Set =
    is-surjective-map-trunc-Set
      ( map-unit-im f)
      ( is-surjective-map-unit-im f)
  
  is-image-trunc-im-Set :
    {l : Level} →
    is-image l
      ( map-trunc-Set f)
      ( emb-trunc-im-Set)
      ( hom-slice-trunc-im-Set)
  is-image-trunc-im-Set =
    is-image-is-surjective
      ( map-trunc-Set f)
      ( emb-trunc-im-Set)
      ( hom-slice-trunc-im-Set)
      ( is-surjective-map-hom-slice-trunc-im-Set)

  unique-equiv-trunc-im-Set :
    is-contr
      ( Σ ( equiv-slice (inclusion-im (map-trunc-Set f)) inclusion-trunc-im-Set)
          ( λ e →
            htpy-hom-slice (map-trunc-Set f)
              ( inclusion-trunc-im-Set)
              ( comp-hom-slice (map-trunc-Set f)
                ( inclusion-im (map-trunc-Set f))
                ( inclusion-trunc-im-Set)
                ( hom-equiv-slice
                  ( inclusion-im (map-trunc-Set f))
                  ( inclusion-trunc-im-Set)
                  ( e))
                ( hom-slice-im (map-trunc-Set f)))
              ( hom-slice-trunc-im-Set)))
  unique-equiv-trunc-im-Set =
    uniqueness-im
      ( map-trunc-Set f)
      ( emb-trunc-im-Set)
      ( hom-slice-trunc-im-Set)
      ( is-image-trunc-im-Set)

  equiv-slice-trunc-im-Set :
    equiv-slice (inclusion-im (map-trunc-Set f)) inclusion-trunc-im-Set
  equiv-slice-trunc-im-Set = pr1 (center unique-equiv-trunc-im-Set)

  equiv-trunc-im-Set : im (map-trunc-Set f) ≃ type-trunc-Set (im f)
  equiv-trunc-im-Set = pr1 equiv-slice-trunc-im-Set

  map-equiv-trunc-im-Set : im (map-trunc-Set f) → type-trunc-Set (im f)
  map-equiv-trunc-im-Set = map-equiv equiv-trunc-im-Set

  triangle-trunc-im-Set :
    ( inclusion-im (map-trunc-Set f)) ~
    ( inclusion-trunc-im-Set ∘ map-equiv-trunc-im-Set)
  triangle-trunc-im-Set = pr2 equiv-slice-trunc-im-Set

  htpy-hom-slice-trunc-im-Set :
    htpy-hom-slice
      ( map-trunc-Set f)
      ( inclusion-trunc-im-Set)
      ( comp-hom-slice
        ( map-trunc-Set f)
        ( inclusion-im (map-trunc-Set f))
        ( inclusion-trunc-im-Set)
        ( hom-equiv-slice
          ( inclusion-im (map-trunc-Set f))
          ( inclusion-trunc-im-Set)
          ( equiv-slice-trunc-im-Set))
        ( hom-slice-im (map-trunc-Set f)))
      ( hom-slice-trunc-im-Set)
  htpy-hom-slice-trunc-im-Set =
    pr2 (center unique-equiv-trunc-im-Set)

  htpy-map-hom-slice-trunc-im-Set :
    ( map-equiv-trunc-im-Set ∘ (map-unit-im (map-trunc-Set f))) ~
    ( map-hom-slice-trunc-im-Set)
  htpy-map-hom-slice-trunc-im-Set =
    pr1 htpy-hom-slice-trunc-im-Set

  tetrahedron-map-hom-slice-trunc-im-Set :
    ( ( triangle-trunc-im-Set ·r map-unit-im (map-trunc-Set f)) ∙h
      ( inclusion-trunc-im-Set ·l htpy-map-hom-slice-trunc-im-Set)) ~
    ( triangle-hom-slice-trunc-im-Set)
  tetrahedron-map-hom-slice-trunc-im-Set =
    pr2 htpy-hom-slice-trunc-im-Set

  unit-im-map-trunc-Set :
    im f → im (map-trunc-Set f)
  unit-im-map-trunc-Set x =
    pair
      ( unit-trunc-Set (pr1 x))
      ( apply-universal-property-trunc-Prop (pr2 x)
        ( trunc-Prop (fib (map-trunc-Set f) (unit-trunc-Set (pr1 x))))
        ( λ u →
          unit-trunc-Prop
            ( pair
              ( unit-trunc-Set (pr1 u))
              ( naturality-trunc-Set f (pr1 u) ∙ ap unit-trunc-Set (pr2 u)))))

  left-square-unit-im-map-trunc-Set :
    ( map-unit-im (map-trunc-Set f) ∘ unit-trunc-Set) ~
    ( unit-im-map-trunc-Set ∘ map-unit-im f)
  left-square-unit-im-map-trunc-Set a =
    eq-Eq-im
      ( map-trunc-Set f)
      ( map-unit-im (map-trunc-Set f) (unit-trunc-Set a))
      ( unit-im-map-trunc-Set (map-unit-im f a))
      ( naturality-trunc-Set f a)

  right-square-unit-im-map-trunc-Set :
    ( inclusion-im (map-trunc-Set f) ∘ unit-im-map-trunc-Set) ~
    ( unit-trunc-Set ∘ inclusion-im f)
  right-square-unit-im-map-trunc-Set x = refl
  
  is-set-truncation-im-map-trunc-Set :
    {l : Level} →
    is-set-truncation l
      ( im-Set (trunc-Set B) (map-trunc-Set f))
      ( unit-im-map-trunc-Set)
  is-set-truncation-im-map-trunc-Set =
    is-set-truncation-is-equiv-is-set-truncation
      ( im-Set (trunc-Set B) (map-trunc-Set f))
      ( unit-im-map-trunc-Set)
      ( trunc-Set (im f))
      ( unit-trunc-Set)
      ( λ b →
        is-injective-inclusion-trunc-im-Set
          ( ( inv (triangle-trunc-im-Set (unit-im-map-trunc-Set b))) ∙
            ( inv (naturality-trunc-Set (inclusion-im f) b))))
      ( is-set-truncation-trunc-Set (im f))
      ( is-equiv-map-equiv equiv-trunc-im-Set)

has-finite-components-Prop : {l : Level} → UU l → UU-Prop l
has-finite-components-Prop A = is-finite-Prop (type-trunc-Set A)

has-finite-components : {l : Level} → UU l → UU l
has-finite-components A = type-Prop (has-finite-components-Prop A)

has-cardinality-components-Prop : {l : Level} (k : ℕ) → UU l → UU-Prop l
has-cardinality-components-Prop k A =
  has-cardinality-Prop (type-trunc-Set A) k

has-cardinality-components : {l : Level} (k : ℕ) → UU l → UU l
has-cardinality-components k A =
  type-Prop (has-cardinality-components-Prop k A)

has-set-presentation-Prop :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU l2) → UU-Prop (l1 ⊔ l2)
has-set-presentation-Prop A B =
  ∃-Prop (λ (f : type-Set A → B) → is-equiv (unit-trunc-Set ∘ f))

has-finite-presentation-Prop :
  {l1 : Level} (k : ℕ) (A : UU l1) → UU-Prop l1
has-finite-presentation-Prop k A =
  has-set-presentation-Prop (Fin-Set k) A

has-finite-presentation :
  {l1 : Level} (k : ℕ) (A : UU l1) → UU l1
has-finite-presentation k A = type-Prop (has-finite-presentation-Prop k A)
  
has-finite-presentation-has-cardinality-components :
  {l : Level} {k : ℕ} {A : UU l} → has-cardinality-components k A →
  has-finite-presentation k A
has-finite-presentation-has-cardinality-components {l} {k} {A} H =
  apply-universal-property-trunc-Prop H
    ( has-finite-presentation-Prop k A)
    ( λ e →
      apply-universal-property-trunc-Prop
        ( P2 e)
        ( has-finite-presentation-Prop k A)
        ( λ g →
          unit-trunc-Prop
            ( pair
              ( λ x → pr1 (g x))
              ( is-equiv-htpy-equiv e (λ x → pr2 (g x))))))
  where
  P1 : (e : Fin k ≃ type-trunc-Set A) (x : Fin k) →
       type-trunc-Prop (fib unit-trunc-Set (map-equiv e x))
  P1 e x = is-surjective-unit-trunc-Set A (map-equiv e x)
  P2 : (e : Fin k ≃ type-trunc-Set A) →
       type-trunc-Prop ((x : Fin k) → fib unit-trunc-Set (map-equiv e x))
  P2 e = finite-choice-Fin (P1 e)

has-cardinality-components-has-finite-presentation :
  {l : Level} {k : ℕ} {A : UU l} → has-finite-presentation k A →
  has-cardinality-components k A
has-cardinality-components-has-finite-presentation {l} {k} {A} H =
  apply-universal-property-trunc-Prop H
    ( has-cardinality-components-Prop k A)
    ( λ { (pair f E) → unit-trunc-Prop (pair (unit-trunc-Set ∘ f) E)})

--------------------------------------------------------------------------------

-- Homotopy finiteness

has-finite-connected-components-Prop : {l : Level} → UU l → UU-Prop l
has-finite-connected-components-Prop A =
  is-finite-Prop (type-trunc-Set A)

has-finite-connected-components : {l : Level} → UU l → UU l
has-finite-connected-components A =
  type-Prop (has-finite-connected-components-Prop A)

number-of-connected-components :
  {l : Level} {X : UU l} → has-finite-connected-components X → ℕ
number-of-connected-components H = number-of-elements-is-finite H

mere-equiv-number-of-connected-components :
  {l : Level} {X : UU l} (H : has-finite-connected-components X) →
  mere-equiv
    ( Fin (number-of-connected-components H))
    ( type-trunc-Set X)
mere-equiv-number-of-connected-components H =
  mere-equiv-is-finite H

is-homotopy-finite-Prop : {l : Level} (k : ℕ) → UU l → UU-Prop l
is-homotopy-finite-Prop zero-ℕ X = has-finite-connected-components-Prop X
is-homotopy-finite-Prop (succ-ℕ k) X =
  prod-Prop ( is-homotopy-finite-Prop zero-ℕ X)
            ( Π-Prop X
              ( λ x → Π-Prop X (λ y → is-homotopy-finite-Prop k (Id x y))))

is-homotopy-finite : {l : Level} (k : ℕ) → UU l → UU l
is-homotopy-finite k X = type-Prop (is-homotopy-finite-Prop k X)

is-prop-is-homotopy-finite :
  {l : Level} (k : ℕ) (X : UU l) → is-prop (is-homotopy-finite k X)
is-prop-is-homotopy-finite k X =
  is-prop-type-Prop (is-homotopy-finite-Prop k X)

Homotopy-Finite : (l : Level) (k : ℕ) → UU (lsuc l)
Homotopy-Finite l k = Σ (UU l) (is-homotopy-finite k)

type-Homotopy-Finite :
  {l : Level} (k : ℕ) → Homotopy-Finite l k → UU l
type-Homotopy-Finite k = pr1

is-homotopy-finite-type-Homotopy-Finite :
  {l : Level} (k : ℕ) (A : Homotopy-Finite l k) →
  is-homotopy-finite k (type-Homotopy-Finite {l} k A)
is-homotopy-finite-type-Homotopy-Finite k = pr2

has-finite-connected-components-Σ-is-path-connected :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-path-connected A → is-homotopy-finite one-ℕ A →
  ((x : A) → has-finite-connected-components (B x)) →
  has-finite-connected-components (Σ A B)
has-finite-connected-components-Σ-is-path-connected {A = A} {B} C H K =
  apply-universal-property-trunc-Prop
    ( is-inhabited-is-path-connected C)
    ( is-homotopy-finite-Prop zero-ℕ (Σ A B))
    ( α)
    
  where
  α : A → is-homotopy-finite zero-ℕ (Σ A B)
  α a =
    is-finite-codomain-has-decidable-equality
      ( K a)
      ( is-surjective-map-trunc-Set
        ( fiber-inclusion B a)
        ( is-surjective-fiber-inclusion C a))
      ( apply-dependent-universal-property-trunc-Set
        ( λ x →
          set-Prop
            ( Π-Prop
              ( type-trunc-Set (Σ A B))
              ( λ y → is-decidable-Prop (Id-Prop (trunc-Set (Σ A B)) x y))))
        ( β))
        
    where
    β : (x : Σ A B) (v : type-trunc-Set (Σ A B)) →
        is-decidable (Id (unit-trunc-Set x) v)
    β (pair x y) =
      apply-dependent-universal-property-trunc-Set
        ( λ u →
          set-Prop
            ( is-decidable-Prop
              ( Id-Prop (trunc-Set (Σ A B)) (unit-trunc-Set (pair x y)) u)))
        ( γ)
        
      where
      γ : (v : Σ A B) →
          is-decidable (Id (unit-trunc-Set (pair x y)) (unit-trunc-Set v))
      γ (pair x' y') =
        is-decidable-equiv
          ( is-effective-unit-trunc-Set
            ( Σ A B)
            ( pair x y)
            ( pair x' y'))
          ( apply-universal-property-trunc-Prop
            ( mere-eq-is-path-connected C a x)
            ( is-decidable-Prop
              ( mere-eq-Prop (pair x y) (pair x' y')))
              ( δ))
              
        where
        δ : Id a x → is-decidable (mere-eq (pair x y) (pair x' y'))
        δ refl =
          apply-universal-property-trunc-Prop
            ( mere-eq-is-path-connected C a x')
            ( is-decidable-Prop
              ( mere-eq-Prop (pair a y) (pair x' y')))
            ( ε)
            
          where
          ε : Id a x' → is-decidable (mere-eq (pair x y) (pair x' y'))
          ε refl =
            is-decidable-equiv e
              ( is-decidable-type-trunc-Prop-is-finite
                ( is-finite-Σ
                  ( pr2 H a a)
                  ( λ ω → is-finite-is-decidable-Prop (P ω) (d ω))))
            
            where
            ℙ : is-contr
                ( Σ ( type-hom-Set (trunc-Set (Id a a)) (UU-Prop-Set _))
                    ( λ h →
                      ( λ a₁ → h (unit-trunc-Set a₁)) ~
                      ( λ ω₁ → trunc-Prop (Id (tr B ω₁ y) y'))))
            ℙ = universal-property-trunc-Set
                ( Id a a)
                ( UU-Prop-Set _)
                ( λ ω → trunc-Prop (Id (tr B ω y) y'))
            P : type-trunc-Set (Id a a) → UU-Prop _
            P = pr1 (center ℙ)
            compute-P :
              ( ω : Id a a) →
              type-Prop (P (unit-trunc-Set ω)) ≃
              type-trunc-Prop (Id (tr B ω y) y') 
            compute-P ω = equiv-eq (ap pr1 (pr2 (center ℙ) ω))
            d : (t : type-trunc-Set (Id a a)) → is-decidable (type-Prop (P t))
            d = apply-dependent-universal-property-trunc-Set
                ( λ t → set-Prop (is-decidable-Prop (P t)))
                ( λ ω →
                  is-decidable-equiv'
                    ( inv-equiv (compute-P ω))
                    ( is-decidable-equiv'
                      ( is-effective-unit-trunc-Set (B a) (tr B ω y) y')
                      ( has-decidable-equality-is-finite
                        ( K a)
                        ( unit-trunc-Set (tr B ω y))
                        ( unit-trunc-Set y'))))
            f : type-hom-Prop
                ( trunc-Prop (Σ (type-trunc-Set (Id a a)) (type-Prop ∘ P)))
                ( mere-eq-Prop {A = Σ A B} (pair a y) (pair a y'))
            f t = apply-universal-property-trunc-Prop t
                    ( mere-eq-Prop (pair a y) (pair a y'))
                     λ { (pair u v) →
                         apply-dependent-universal-property-trunc-Set
                           ( λ u' →
                             hom-Set
                               ( set-Prop (P u'))
                               ( set-Prop
                                 ( mere-eq-Prop (pair a y) (pair a y'))))
                           ( λ ω v' →
                             apply-universal-property-trunc-Prop
                               ( map-equiv (compute-P ω) v')
                               ( mere-eq-Prop (pair a y) (pair a y'))
                               ( λ p → unit-trunc-Prop (eq-pair-Σ ω p)))
                           ( u)
                           ( v)}
            e : mere-eq {A = Σ A B} (pair a y) (pair a y') ≃
                type-trunc-Prop (Σ (type-trunc-Set (Id a a)) (type-Prop ∘ P))
            e = equiv-iff
                  ( mere-eq-Prop (pair a y) (pair a y'))
                  ( trunc-Prop (Σ (type-trunc-Set (Id a a)) (type-Prop ∘ P)))
                  ( λ t →
                    apply-universal-property-trunc-Prop t
                      ( trunc-Prop _)
                      ( ( λ { (pair ω r) →
                            unit-trunc-Prop
                              ( pair
                                ( unit-trunc-Set ω)
                                ( map-inv-equiv
                                  ( compute-P ω)
                                  ( unit-trunc-Prop r)))}) ∘
                        ( pair-eq-Σ)))
                  ( f)

is-coprod-codomain :
  {l1 l2 l3 : Level} {A1 : UU l1} {A2 : UU l2} {B : UU l3}
  (f : coprod A1 A2 → B) (e : coprod A1 A2 ≃ type-trunc-Set B)
  (H : (unit-trunc-Set ∘ f) ~ map-equiv e) →
  coprod (im (f ∘ inl)) (im (f ∘ inr)) ≃ B
is-coprod-codomain {B = B} f e H =
  pair α (is-equiv-is-emb-is-surjective is-surj-α is-emb-α)
  where
  α : coprod (im (f ∘ inl)) (im (f ∘ inr)) → B
  α = ind-coprod (λ x → B) pr1 pr1
  triangle-α : (α ∘ map-coprod (map-unit-im (f ∘ inl)) (map-unit-im (f ∘ inr))) ~ f
  triangle-α (inl a1) = refl
  triangle-α (inr a2) = refl
  is-emb-α : is-emb α
  is-emb-α =
    is-emb-coprod
      ( is-emb-pr1 (λ b → is-prop-type-trunc-Prop))
      ( is-emb-pr1 (λ b → is-prop-type-trunc-Prop))
      ( λ { (pair b1 u) (pair b2 v) →
          apply-universal-property-trunc-Prop u
            ( function-Prop _ empty-Prop)
            ( λ
              { (pair x refl) →
                apply-universal-property-trunc-Prop v
                  ( function-Prop _ empty-Prop)
                  ( λ
                    { (pair y refl) r →
                      map-compute-eq-coprod-inl-inr x y
                        ( is-injective-is-equiv
                          ( is-equiv-map-equiv e)
                          ( ( inv (H (inl x))) ∙
                            ( ( ap unit-trunc-Set r) ∙
                              ( H (inr y)))))})})})
  is-surj-α : is-surjective α
  is-surj-α b =
    apply-universal-property-trunc-Prop
      ( apply-effectiveness-unit-trunc-Set
        ( inv (issec-map-inv-equiv e (unit-trunc-Set b)) ∙ inv (H a)))
      ( trunc-Prop (fib α b))
      ( λ p →
        unit-trunc-Prop
          ( pair
            ( map-coprod (map-unit-im (f ∘ inl)) (map-unit-im (f ∘ inr)) a)
            ( triangle-α a ∙ inv p)))
    where
    a = map-inv-equiv e (unit-trunc-Set b)

is-path-connected-unit : is-path-connected unit
is-path-connected-unit =
  is-contr-equiv' unit equiv-unit-trunc-unit-Set is-contr-unit

is-contr-im :
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) {f : A → type-Set B}
  (a : A) (H : f ~ const A (type-Set B) (f a)) → is-contr (im f)
is-contr-im B {f} a H =
  pair
    ( map-unit-im f a)
    ( λ { (pair x u) →
      apply-dependent-universal-property-trunc-Prop
        ( λ v → Id-Prop (im-Set B f) (map-unit-im f a) (pair x v))
        ( u)
        ( λ { (pair a' refl) →
              eq-Eq-im f (map-unit-im f a) (map-unit-im f a') (inv (H a'))})})

is-path-connected-im :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-path-connected A → is-path-connected (im f)
is-path-connected-im {l1} {l2} {A} {B} f C =
  apply-universal-property-trunc-Prop
    ( is-inhabited-is-path-connected C)
    ( is-contr-Prop _)
    ( λ a →
      is-contr-equiv'
        ( im (map-trunc-Set f))
        ( equiv-trunc-im-Set f)
        ( is-contr-im
          ( trunc-Set B)
          ( unit-trunc-Set a)
          ( apply-dependent-universal-property-trunc-Set
            ( λ x →
              set-Prop
                ( Id-Prop
                  ( trunc-Set B)
                  ( map-trunc-Set f x)
                  ( map-trunc-Set f (unit-trunc-Set a))))
            ( λ a' →
              apply-universal-property-trunc-Prop
                ( mere-eq-is-path-connected C a' a)
                ( Id-Prop
                  ( trunc-Set B)
                  ( map-trunc-Set f (unit-trunc-Set a'))
                  ( map-trunc-Set f (unit-trunc-Set a)))
                ( λ {refl → refl})))))

is-path-connected-im-unit :
  {l1 : Level} {A : UU l1} (f : unit → A) → is-path-connected (im f)
is-path-connected-im-unit f =
  is-path-connected-im f is-path-connected-unit

is-homotopy-finite-empty : (k : ℕ) → is-homotopy-finite k empty
is-homotopy-finite-empty zero-ℕ =
  is-finite-equiv equiv-unit-trunc-empty-Set is-finite-empty
is-homotopy-finite-empty (succ-ℕ k) =
  pair (is-homotopy-finite-empty zero-ℕ) ind-empty

empty-Homotopy-Finite : (k : ℕ) → Homotopy-Finite lzero k
empty-Homotopy-Finite k = pair empty (is-homotopy-finite-empty k)

is-homotopy-finite-is-empty :
  {l : Level} (k : ℕ) {A : UU l} → is-empty A → is-homotopy-finite k A
is-homotopy-finite-is-empty zero-ℕ f =
  is-finite-is-empty (is-empty-trunc-Set f)
is-homotopy-finite-is-empty (succ-ℕ k) f =
  pair
    ( is-homotopy-finite-is-empty zero-ℕ f)
    ( λ a → ex-falso (f a))

is-homotopy-finite-is-contr :
  {l : Level} (k : ℕ) {A : UU l} → is-contr A → is-homotopy-finite k A
is-homotopy-finite-is-contr zero-ℕ H =
  is-finite-is-contr (is-contr-trunc-Set H)
is-homotopy-finite-is-contr (succ-ℕ k) H =
  pair
    ( is-homotopy-finite-is-contr zero-ℕ H)
    ( λ x y →
      is-homotopy-finite-is-contr k ( is-prop-is-contr H x y))

is-homotopy-finite-unit :
  (k : ℕ) → is-homotopy-finite k unit
is-homotopy-finite-unit k = is-homotopy-finite-is-contr k is-contr-unit

unit-Homotopy-Finite : (k : ℕ) → Homotopy-Finite lzero k
unit-Homotopy-Finite k = pair unit (is-homotopy-finite-unit k)

is-homotopy-finite-equiv :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-homotopy-finite k B → is-homotopy-finite k A
is-homotopy-finite-equiv zero-ℕ e H =
  is-finite-equiv' (equiv-trunc-Set e) H
is-homotopy-finite-equiv (succ-ℕ k) e H =
  pair
    ( is-homotopy-finite-equiv zero-ℕ e (pr1 H))
    ( λ a b →
      is-homotopy-finite-equiv k
        ( equiv-ap e a b)
        ( pr2 H (map-equiv e a) (map-equiv e b)))

is-homotopy-finite-equiv' :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-homotopy-finite k A → is-homotopy-finite k B
is-homotopy-finite-equiv' k e = is-homotopy-finite-equiv k (inv-equiv e)

has-finite-connected-components-is-path-connected :
  {l : Level} {A : UU l} →
  is-path-connected A → has-finite-connected-components A
has-finite-connected-components-is-path-connected C =
  is-finite-is-contr C

is-homotopy-finite-coprod :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} →
  is-homotopy-finite k A → is-homotopy-finite k B →
  is-homotopy-finite k (coprod A B)
is-homotopy-finite-coprod zero-ℕ H K =
  is-finite-equiv'
    ( equiv-distributive-trunc-coprod-Set _ _)
    ( is-finite-coprod H K)
is-homotopy-finite-coprod (succ-ℕ k) H K =
  pair
    ( is-homotopy-finite-coprod zero-ℕ (pr1 H) (pr1 K))
    ( λ { (inl x) (inl y) →
          is-homotopy-finite-equiv k
            ( compute-eq-coprod-inl-inl x y)
            ( pr2 H x y) ;
          (inl x) (inr y) →
          is-homotopy-finite-equiv k
            ( compute-eq-coprod-inl-inr x y)
            ( is-homotopy-finite-empty k) ;
          (inr x) (inl y) →
          is-homotopy-finite-equiv k
            ( compute-eq-coprod-inr-inl x y)
            ( is-homotopy-finite-empty k) ;
          (inr x) (inr y) →
          is-homotopy-finite-equiv k
            ( compute-eq-coprod-inr-inr x y)
            ( pr2 K x y)})

coprod-Homotopy-Finite :
  {l1 l2 : Level} (k : ℕ) →
  Homotopy-Finite l1 k → Homotopy-Finite l2 k → Homotopy-Finite (l1 ⊔ l2) k
coprod-Homotopy-Finite k A B =
  pair
    ( coprod (type-Homotopy-Finite k A) (type-Homotopy-Finite k B))
    ( is-homotopy-finite-coprod k
      ( is-homotopy-finite-type-Homotopy-Finite k A)
      ( is-homotopy-finite-type-Homotopy-Finite k B))

is-homotopy-finite-Maybe :
  {l : Level} (k : ℕ) {A : UU l} →
  is-homotopy-finite k A → is-homotopy-finite k (Maybe A)
is-homotopy-finite-Maybe k H =
  is-homotopy-finite-coprod k H (is-homotopy-finite-unit k)

is-homotopy-finite-Fin :
  (k n : ℕ) → is-homotopy-finite k (Fin n)
is-homotopy-finite-Fin k zero-ℕ =
  is-homotopy-finite-empty k
is-homotopy-finite-Fin k (succ-ℕ n) =
  is-homotopy-finite-Maybe k (is-homotopy-finite-Fin k n)

Fin-Homotopy-Finite : (k : ℕ) (n : ℕ) → Homotopy-Finite lzero k
Fin-Homotopy-Finite k n =
  pair (Fin n) (is-homotopy-finite-Fin k n)

is-homotopy-finite-count :
  {l : Level} (k : ℕ) {A : UU l} → count A → is-homotopy-finite k A
is-homotopy-finite-count k (pair n e) =
  is-homotopy-finite-equiv' k e (is-homotopy-finite-Fin k n)

is-homotopy-finite-is-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-finite A → is-homotopy-finite k A
is-homotopy-finite-is-finite k {A} H =
  apply-universal-property-trunc-Prop H
    ( is-homotopy-finite-Prop k A)
    ( is-homotopy-finite-count k)

is-homotopy-finite-UU-Fin :
  (k n : ℕ) → is-homotopy-finite k (UU-Fin n)
is-homotopy-finite-UU-Fin zero-ℕ n =
  has-finite-connected-components-is-path-connected
    ( is-path-connected-UU-Fin n)
is-homotopy-finite-UU-Fin (succ-ℕ k) n =
  pair
    ( is-homotopy-finite-UU-Fin zero-ℕ n)
    ( λ x y →
      is-homotopy-finite-equiv k
        ( equiv-equiv-eq-UU-Fin x y)
        ( is-homotopy-finite-is-finite k
          ( is-finite-≃
            ( is-finite-has-finite-cardinality (pair n (pr2 x)))
            ( is-finite-has-finite-cardinality (pair n (pr2 y))))))

is-homotopy-finite-UU-Fin-Level :
  {l : Level} (k n : ℕ) → is-homotopy-finite k (UU-Fin-Level l n)
is-homotopy-finite-UU-Fin-Level {l} zero-ℕ n =
  has-finite-connected-components-is-path-connected
    ( is-path-connected-UU-Fin-Level n)
is-homotopy-finite-UU-Fin-Level {l} (succ-ℕ k) n =
  pair
    ( is-homotopy-finite-UU-Fin-Level zero-ℕ n)
    ( λ x y →
      is-homotopy-finite-equiv k
        ( equiv-equiv-eq-UU-Fin-Level x y)
        ( is-homotopy-finite-is-finite k
          ( is-finite-≃
            ( is-finite-has-finite-cardinality (pair n (pr2 x)))
            ( is-finite-has-finite-cardinality (pair n (pr2 y))))))

is-finite-has-finite-connected-components :
  {l : Level} {A : UU l} →
  is-set A → has-finite-connected-components A → is-finite A
is-finite-has-finite-connected-components H =
  is-finite-equiv' (equiv-unit-trunc-Set (pair _ H))

has-finite-connected-components-is-homotopy-finite :
  {l : Level} (k : ℕ) {A : UU l} →
  is-homotopy-finite k A → has-finite-connected-components A
has-finite-connected-components-is-homotopy-finite zero-ℕ H = H
has-finite-connected-components-is-homotopy-finite (succ-ℕ k) H = pr1 H

is-homotopy-finite-is-homotopy-finite-succ-ℕ :
  {l : Level} (k : ℕ) {A : UU l} →
  is-homotopy-finite (succ-ℕ k) A → is-homotopy-finite k A
is-homotopy-finite-is-homotopy-finite-succ-ℕ zero-ℕ H =
  has-finite-connected-components-is-homotopy-finite one-ℕ H
is-homotopy-finite-is-homotopy-finite-succ-ℕ (succ-ℕ k) H =
  pair
    ( has-finite-connected-components-is-homotopy-finite (succ-ℕ (succ-ℕ k)) H)
    ( λ x y → is-homotopy-finite-is-homotopy-finite-succ-ℕ k (pr2 H x y))

is-homotopy-finite-one-is-homotopy-finite-succ-ℕ :
  {l : Level} (k : ℕ) {A : UU l} →
  is-homotopy-finite (succ-ℕ k) A → is-homotopy-finite one-ℕ A
is-homotopy-finite-one-is-homotopy-finite-succ-ℕ zero-ℕ H = H
is-homotopy-finite-one-is-homotopy-finite-succ-ℕ (succ-ℕ k) H =
  is-homotopy-finite-one-is-homotopy-finite-succ-ℕ k
    ( is-homotopy-finite-is-homotopy-finite-succ-ℕ (succ-ℕ k) H)

is-finite-is-homotopy-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-set A →
  is-homotopy-finite k A → is-finite A
is-finite-is-homotopy-finite k H K =
  is-finite-equiv'
    ( equiv-unit-trunc-Set (pair _ H))
    ( has-finite-connected-components-is-homotopy-finite k K)

has-finite-connected-components-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (k : ℕ) → (Fin k ≃ (type-trunc-Set A)) →
  ((x y : A) → has-finite-connected-components (Id x y)) → 
  ((x : A) → has-finite-connected-components (B x)) →
  has-finite-connected-components (Σ A B)
has-finite-connected-components-Σ' zero-ℕ e H K =
  is-homotopy-finite-is-empty zero-ℕ
    ( is-empty-is-empty-trunc-Set (map-inv-equiv e) ∘ pr1)
has-finite-connected-components-Σ' {l1} {l2} {A} {B} (succ-ℕ k) e H K =
  apply-universal-property-trunc-Prop
    ( has-finite-presentation-has-cardinality-components (unit-trunc-Prop e))
    ( has-finite-connected-components-Prop (Σ A B))
    ( α)
  where
  α : Σ (Fin (succ-ℕ k) → A) (λ f → is-equiv (unit-trunc-Set ∘ f)) →
      has-finite-connected-components (Σ A B)
  α (pair f Eηf) =
    is-finite-equiv
      ( equiv-trunc-Set g)
      ( is-finite-equiv'
        ( equiv-distributive-trunc-coprod-Set
          ( Σ (im (f ∘ inl)) (B ∘ pr1))
          ( Σ (im (f ∘ inr)) (B ∘ pr1)))
        ( is-finite-coprod
          ( has-finite-connected-components-Σ' k
            ( h)
            ( λ x y →
              is-finite-equiv'
                ( equiv-trunc-Set
                  ( equiv-ap-emb
                    ( pair pr1
                      ( is-emb-pr1
                        ( λ u → is-prop-type-trunc-Prop)))))
                ( H (pr1 x) (pr1 y)))
            ( λ x → K (pr1 x)))
          ( has-finite-connected-components-Σ-is-path-connected
            ( is-path-connected-im (f ∘ inr) is-path-connected-unit)
            ( pair
              ( is-finite-is-contr
                ( is-path-connected-im (f ∘ inr) is-path-connected-unit))
              ( λ x y →
                is-homotopy-finite-equiv zero-ℕ
                  ( equiv-Eq-eq-im (f ∘ inr) x y)
                  ( H (pr1 x) (pr1 y))))
            ( λ x → K (pr1 x)))))
    where
    g : coprod (Σ (im (f ∘ inl)) (B ∘ pr1)) (Σ (im (f ∘ inr)) (B ∘ pr1)) ≃
        Σ A B
    g = ( equiv-Σ B
          ( is-coprod-codomain f
            ( pair (unit-trunc-Set ∘ f) Eηf)
            ( refl-htpy))
          ( λ { (inl x) → equiv-id ;
                (inr x) → equiv-id})) ∘e
        ( inv-equiv
          ( right-distributive-Σ-coprod
            ( im (f ∘ inl))
            ( im (f ∘ inr))
            ( ind-coprod (λ x → UU _) (B ∘ pr1) (B ∘ pr1))))
    i : Fin k → type-trunc-Set (im (f ∘ inl))
    i = unit-trunc-Set ∘ map-unit-im (f ∘ inl)
    is-surjective-i : is-surjective i
    is-surjective-i =
      is-surjective-comp'
        ( is-surjective-unit-trunc-Set _)
        ( is-surjective-map-unit-im (f ∘ inl))
    is-emb-i : is-emb i
    is-emb-i =
      is-emb-right-factor
        ( (unit-trunc-Set ∘ f) ∘ inl)
        ( inclusion-trunc-im-Set (f ∘ inl))
        ( i)
        ( ( inv-htpy (naturality-trunc-Set (inclusion-im (f ∘ inl)))) ·r
          ( map-unit-im (f ∘ inl)))
        ( is-emb-inclusion-trunc-im-Set (f ∘ inl))
        ( is-emb-comp'
          ( unit-trunc-Set ∘ f)
          ( inl)
          ( is-emb-is-equiv Eηf)
          ( is-emb-inl (Fin k) unit))
    h : Fin k ≃ type-trunc-Set (im (f ∘ inl))
    h = pair i (is-equiv-is-emb-is-surjective is-surjective-i is-emb-i)

has-finite-connected-components-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-homotopy-finite one-ℕ A →
  ((x : A) → has-finite-connected-components (B x)) →
  has-finite-connected-components (Σ A B)
has-finite-connected-components-Σ {l1} {l2} {A} {B} H K =
  apply-universal-property-trunc-Prop
    ( pr1 H)
    ( has-finite-connected-components-Prop (Σ A B))
    ( λ { (pair k e) →
          has-finite-connected-components-Σ' k e (λ x y → pr2 H x y) K})

is-homotopy-finite-Σ :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : A → UU l2} →
  is-homotopy-finite (succ-ℕ k) A → ((x : A) → is-homotopy-finite k (B x)) →
  is-homotopy-finite k (Σ A B)
is-homotopy-finite-Σ zero-ℕ {A} {B} H K = has-finite-connected-components-Σ H K
is-homotopy-finite-Σ (succ-ℕ k) H K =
  pair
    ( has-finite-connected-components-Σ
      ( is-homotopy-finite-one-is-homotopy-finite-succ-ℕ (succ-ℕ k) H)
      ( λ x →
        has-finite-connected-components-is-homotopy-finite (succ-ℕ k) (K x)))
    ( λ { (pair x u) (pair y v) →
          is-homotopy-finite-equiv k
            ( equiv-pair-eq-Σ (pair x u) (pair y v))
            ( is-homotopy-finite-Σ k
              ( pr2 H x y)
              ( λ { refl → pr2 (K x) u v}))})

Homotopy-Finite-Σ :
  {l1 l2 : Level} (k : ℕ) (A : Homotopy-Finite l1 (succ-ℕ k))
  (B : (x : type-Homotopy-Finite (succ-ℕ k) A) → Homotopy-Finite l2 k) →
  Homotopy-Finite (l1 ⊔ l2) k
Homotopy-Finite-Σ k A B =
  pair
    ( Σ ( type-Homotopy-Finite (succ-ℕ k) A)
        ( λ x → type-Homotopy-Finite k (B x)))
    ( is-homotopy-finite-Σ k
      ( is-homotopy-finite-type-Homotopy-Finite (succ-ℕ k) A)
      ( λ x → is-homotopy-finite-type-Homotopy-Finite k (B x)))

has-associative-mul : {l : Level} (X : UU l) → UU l
has-associative-mul X =
  Σ (X → X → X) (λ μ → (x y z : X) → Id (μ (μ x y) z) (μ x (μ y z)))

has-associative-mul-Set :
  {l : Level} (X : UU-Set l) → UU l
has-associative-mul-Set X =
  has-associative-mul (type-Set X)

Semi-Group :
  (l : Level) → UU (lsuc l)
Semi-Group l = Σ (UU-Set l) has-associative-mul-Set

set-Semi-Group :
  {l : Level} → Semi-Group l → UU-Set l
set-Semi-Group G = pr1 G

type-Semi-Group :
  {l : Level} → Semi-Group l → UU l
type-Semi-Group G = pr1 (set-Semi-Group G)

is-set-type-Semi-Group :
  {l : Level} (G : Semi-Group l) → is-set (type-Semi-Group G)
is-set-type-Semi-Group G = pr2 (set-Semi-Group G)

associative-mul-Semi-Group :
  {l : Level} (G : Semi-Group l) →
  has-associative-mul (type-Semi-Group G)
associative-mul-Semi-Group G = pr2 G

mul-Semi-Group :
  {l : Level} (G : Semi-Group l) →
  type-Semi-Group G →
    type-Semi-Group G → type-Semi-Group G
mul-Semi-Group G = pr1 (associative-mul-Semi-Group G)

is-associative-mul-Semi-Group :
  {l : Level} (G : Semi-Group l) (x y z : type-Semi-Group G) →
  Id ( mul-Semi-Group G (mul-Semi-Group G x y) z)
     ( mul-Semi-Group G x (mul-Semi-Group G y z))
is-associative-mul-Semi-Group G = pr2 (associative-mul-Semi-Group G)

is-unital :
  {l : Level} → Semi-Group l → UU l
is-unital G =
  Σ ( type-Semi-Group G)
    ( λ e →
      ( (y : type-Semi-Group G) → Id (mul-Semi-Group G e y) y) ×
      ( (x : type-Semi-Group G) → Id (mul-Semi-Group G x e) x))

Monoid :
  (l : Level) → UU (lsuc l)
Monoid l = Σ (Semi-Group l) is-unital

semi-group-Monoid :
  {l : Level} (M : Monoid l) → Semi-Group l
semi-group-Monoid M = pr1 M

type-Monoid :
  {l : Level} (M : Monoid l) → UU l
type-Monoid M = type-Semi-Group (semi-group-Monoid M)

is-set-type-Monoid :
  {l : Level} (M : Monoid l) → is-set (type-Monoid M)
is-set-type-Monoid M = is-set-type-Semi-Group (semi-group-Monoid M)

mul-Monoid :
  {l : Level} (M : Monoid l) → type-Monoid M → type-Monoid M → type-Monoid M
mul-Monoid M = mul-Semi-Group (semi-group-Monoid M)

is-associative-mul-Monoid :
  {l : Level} (M : Monoid l) (x y z : type-Monoid M) →
  Id (mul-Monoid M (mul-Monoid M x y) z) (mul-Monoid M x (mul-Monoid M y z))
is-associative-mul-Monoid M =
  is-associative-mul-Semi-Group (semi-group-Monoid M)

unit-Monoid :
  {l : Level} (M : Monoid l) → type-Monoid M
unit-Monoid M = pr1 (pr2 M)

left-unit-law-Monoid :
  {l : Level} (M : Monoid l) (x : type-Monoid M) →
  Id (mul-Monoid M (unit-Monoid M) x) x
left-unit-law-Monoid M = pr1 (pr2 (pr2 M))

right-unit-law-Monoid :
  {l : Level} (M : Monoid l) (x : type-Monoid M) →
  Id (mul-Monoid M x (unit-Monoid M)) x
right-unit-law-Monoid M = pr2 (pr2 (pr2 M))

all-elements-equal-is-unital :
  {l : Level} (G : Semi-Group l) → all-elements-equal (is-unital G)
all-elements-equal-is-unital (pair (pair X is-set-X) (pair μ assoc-μ))
  (pair e (pair left-unit-e right-unit-e))
  (pair e' (pair left-unit-e' right-unit-e')) =
  eq-subtype
    ( λ e → is-prop-prod
      ( is-prop-Π (λ y → is-set-X (μ e y) y))
      ( is-prop-Π (λ x → is-set-X (μ x e) x)))
    ( (inv (left-unit-e' e)) ∙ (right-unit-e e'))

is-prop-is-unital :
  {l : Level} (G : Semi-Group l) → is-prop (is-unital G)
is-prop-is-unital G =
  is-prop-all-elements-equal (all-elements-equal-is-unital G)

is-unital-Prop : {l : Level} (G : Semi-Group l) → UU-Prop l
is-unital-Prop G = pair (is-unital G) (is-prop-is-unital G)

is-invertible-Monoid :
  {l : Level} (M : Monoid l) → type-Monoid M → UU l
is-invertible-Monoid M x =
  Σ ( type-Monoid M)
    ( λ y →
      Id (mul-Monoid M y x) (unit-Monoid M) ×
      Id (mul-Monoid M x y) (unit-Monoid M))

all-elements-equal-is-invertible-Monoid :
  {l : Level} (M : Monoid l) (x : type-Monoid M) →
  all-elements-equal (is-invertible-Monoid M x)
all-elements-equal-is-invertible-Monoid M x (pair y (pair p q)) (pair y' (pair p' q')) =
  eq-subtype
    ( ( λ z →
      is-prop-prod
        ( is-set-type-Monoid M (mul-Monoid M z x) (unit-Monoid M))
        ( is-set-type-Monoid M (mul-Monoid M x z) (unit-Monoid M))))
    ( ( inv (left-unit-law-Monoid M y)) ∙
      ( ( inv (ap (λ z → mul-Monoid M z y) p')) ∙
        ( ( is-associative-mul-Monoid M y' x y) ∙
          ( ( ap (mul-Monoid M y') q) ∙
            ( right-unit-law-Monoid M y')))))

is-prop-is-invertible-Monoid :
  {l : Level} (M : Monoid l) (x : type-Monoid M) →
  is-prop (is-invertible-Monoid M x)
is-prop-is-invertible-Monoid M x =
  is-prop-all-elements-equal (all-elements-equal-is-invertible-Monoid M x)

is-group' :
  {l : Level} (G : Semi-Group l) → is-unital G → UU l
is-group' G is-unital-G =
  Σ ( type-Semi-Group G → type-Semi-Group G)
    ( λ i →
      ( (x : type-Semi-Group G) →
        Id (mul-Semi-Group G (i x) x) (pr1 is-unital-G)) ×
      ( (x : type-Semi-Group G) →
        Id (mul-Semi-Group G x (i x)) (pr1 is-unital-G)))

is-group :
  {l : Level} (G : Semi-Group l) → UU l
is-group G =
  Σ (is-unital G) (is-group' G)

Group :
  (l : Level) → UU (lsuc l)
Group l = Σ (Semi-Group l) is-group

module _
  {l : Level} (G : Group l)
  where
  
  semi-group-Group : Semi-Group l
  semi-group-Group = pr1 G
  
  set-Group : UU-Set l
  set-Group = pr1 semi-group-Group
  
  type-Group : UU l
  type-Group = pr1 set-Group
  
  is-set-type-Group : is-set type-Group
  is-set-type-Group = pr2 set-Group
  
  associative-mul-Group : has-associative-mul type-Group
  associative-mul-Group = pr2 semi-group-Group
  
  mul-Group : type-Group → type-Group → type-Group
  mul-Group = pr1 associative-mul-Group
  
  mul-Group' : type-Group → type-Group → type-Group
  mul-Group' x y = mul-Group y x
  
  is-associative-mul-Group :
    (x y z : type-Group) →
    Id (mul-Group (mul-Group x y) z) (mul-Group x (mul-Group y z))
  is-associative-mul-Group = pr2 associative-mul-Group
    
  is-group-Group : is-group semi-group-Group
  is-group-Group = pr2 G
  
  is-unital-Group : is-unital semi-group-Group
  is-unital-Group = pr1 is-group-Group
  
  unit-Group : type-Group
  unit-Group = pr1 is-unital-Group
  
  left-unit-law-Group :
    (x : type-Group) → Id (mul-Group unit-Group x) x
  left-unit-law-Group = pr1 (pr2 is-unital-Group)
  
  right-unit-law-Group :
    (x : type-Group) → Id (mul-Group x unit-Group) x
  right-unit-law-Group = pr2 (pr2 is-unital-Group)
  
  has-inverses-Group : is-group' semi-group-Group is-unital-Group
  has-inverses-Group = pr2 is-group-Group
  
  inv-Group : type-Group → type-Group
  inv-Group = pr1 has-inverses-Group
  
  left-inverse-law-Group :
    (x : type-Group) → Id (mul-Group (inv-Group x) x) unit-Group
  left-inverse-law-Group = pr1 (pr2 has-inverses-Group)
  
  right-inverse-law-Group :
    (x : type-Group) → Id (mul-Group x (inv-Group x)) unit-Group
  right-inverse-law-Group = pr2 (pr2 has-inverses-Group)
  
  is-equiv-mul-Group : (x : type-Group) → is-equiv (mul-Group x)
  is-equiv-mul-Group x =
    is-equiv-has-inverse
      ( mul-Group (inv-Group x))
      ( λ y →
        ( inv (is-associative-mul-Group _ _ _)) ∙
        ( ( ap (mul-Group' y) (right-inverse-law-Group x)) ∙
          ( left-unit-law-Group y)))
      ( λ y →
        ( inv (is-associative-mul-Group _ _ _)) ∙
        ( ( ap (mul-Group' y) (left-inverse-law-Group x)) ∙
          ( left-unit-law-Group y)))
  
  equiv-mul-Group : (x : type-Group) → type-Group ≃ type-Group
  equiv-mul-Group x = pair (mul-Group x) (is-equiv-mul-Group x)
  
  is-equiv-mul-Group' : (x : type-Group) → is-equiv (mul-Group' x)
  is-equiv-mul-Group' x =
    is-equiv-has-inverse
    ( mul-Group' (inv-Group x))
      ( λ y →
        ( is-associative-mul-Group _ _ _) ∙
        ( ( ap (mul-Group y) (left-inverse-law-Group x)) ∙
          ( right-unit-law-Group y)))
      ( λ y →
        ( is-associative-mul-Group _ _ _) ∙
        ( ( ap (mul-Group y) (right-inverse-law-Group x)) ∙
          ( right-unit-law-Group y)))
  
  equiv-mul-Group' : (x : type-Group) → type-Group ≃ type-Group
  equiv-mul-Group' x = pair (mul-Group' x) (is-equiv-mul-Group' x)

all-elements-equal-is-group :
  {l : Level} (G : Semi-Group l) (e : is-unital G) →
  all-elements-equal (is-group' G e)
all-elements-equal-is-group
  ( pair (pair G is-set-G) (pair μ assoc-G))
  ( pair e (pair left-unit-G right-unit-G))
  ( pair i (pair left-inv-i right-inv-i))
  ( pair i' (pair left-inv-i' right-inv-i')) =
  eq-subtype
    ( λ i →
      is-prop-prod
        ( is-prop-Π (λ x → is-set-G (μ (i x) x) e))
        ( is-prop-Π (λ x → is-set-G (μ x (i x)) e)))
    ( eq-htpy
      ( λ x →                                             -- ix
        ( inv (left-unit-G (i x))) ∙                      -- = 1·(ix)
        ( ( ap (λ y → μ y (i x)) (inv (left-inv-i' x))) ∙ -- = (i'x·x)·(ix)
          ( ( assoc-G (i' x) x (i x)) ∙                   -- = (i'x)·(x·ix)
            ( ( ap (μ (i' x)) (right-inv-i x)) ∙          -- = (i'x)·1
              ( right-unit-G (i' x)))))))                 -- = i'x

is-prop-is-group :
  {l : Level} (G : Semi-Group l) → is-prop (is-group G)
is-prop-is-group G =
  is-prop-Σ
    ( is-prop-is-unital G)
    ( λ e →
      is-prop-all-elements-equal (all-elements-equal-is-group G e))

is-group-Prop : {l : Level} (G : Semi-Group l) → UU-Prop l
is-group-Prop G = pair (is-group G) (is-prop-is-group G)

Semi-Group-of-Order' : (l : Level) (n : ℕ) → UU (lsuc l)
Semi-Group-of-Order' l n =
  Σ (UU-Fin-Level l n) (λ X → has-associative-mul (type-UU-Fin-Level X))

Semi-Group-of-Order : (l : Level) (n : ℕ) → UU (lsuc l)
Semi-Group-of-Order l n =
  Σ (Semi-Group l) (λ G → mere-equiv (Fin n) (type-Semi-Group G))

is-finite-has-associative-mul :
  {l : Level} {X : UU l} → is-finite X → is-finite (has-associative-mul X)
is-finite-has-associative-mul H =
  is-finite-Σ
    ( is-finite-function-type H (is-finite-function-type H H))
    ( λ μ →
      is-finite-Π H
        ( λ x →
          is-finite-Π H
            ( λ y →
              is-finite-Π H
                ( λ z →
                  is-finite-eq (has-decidable-equality-is-finite H)))))

is-homotopy-finite-Semi-Group-of-Order' :
  {l : Level} (k n : ℕ) → is-homotopy-finite k (Semi-Group-of-Order' l n)
is-homotopy-finite-Semi-Group-of-Order' k n =
  is-homotopy-finite-Σ k
    ( is-homotopy-finite-UU-Fin-Level (succ-ℕ k) n)
    ( λ x →
      is-homotopy-finite-is-finite k
        ( is-finite-has-associative-mul
          ( is-finite-type-UU-Fin-Level x)))

is-homotopy-finite-Semi-Group-of-Order :
  {l : Level} (k n : ℕ) → is-homotopy-finite k (Semi-Group-of-Order l n)
is-homotopy-finite-Semi-Group-of-Order {l} k n =
  is-homotopy-finite-equiv k e
    ( is-homotopy-finite-Semi-Group-of-Order' k n)
  where
  e : Semi-Group-of-Order l n ≃ Semi-Group-of-Order' l n
  e = ( equiv-Σ
        ( has-associative-mul ∘ type-UU-Fin-Level)
        ( ( right-unit-law-Σ-is-contr
            ( λ X →
              is-proof-irrelevant-is-prop
                ( is-prop-is-set _)
                ( is-set-is-finite
                  ( is-finite-has-cardinality (pr2 X))))) ∘e
          ( equiv-right-swap-Σ))
        ( λ X → equiv-id)) ∘e
      ( equiv-right-swap-Σ
        { A = UU-Set l}
        { B = has-associative-mul-Set}
        { C = mere-equiv (Fin n) ∘ type-Set})

number-of-semi-groups-of-order : ℕ → ℕ
number-of-semi-groups-of-order n =
  number-of-connected-components
    ( is-homotopy-finite-Semi-Group-of-Order {lzero} zero-ℕ n)

mere-equiv-number-of-semi-groups-of-order :
  (n : ℕ) →
  mere-equiv
    ( Fin (number-of-semi-groups-of-order n))
    ( type-trunc-Set (Semi-Group-of-Order lzero n))
mere-equiv-number-of-semi-groups-of-order n =
  mere-equiv-number-of-connected-components
    ( is-homotopy-finite-Semi-Group-of-Order {lzero} zero-ℕ n)

Group-of-Order : (l : Level) (n : ℕ) → UU (lsuc l)
Group-of-Order l n = Σ (Group l) (λ M → mere-equiv (Fin n) (type-Group M))

is-finite-is-group :
  {l : Level} {n : ℕ} (G : Semi-Group-of-Order l n) →
  is-finite {l} (is-group (pr1 G))
is-finite-is-group {l} {n} G =
  apply-universal-property-trunc-Prop
    ( pr2 G)
    ( is-finite-Prop _)
    ( λ e →
      is-finite-is-decidable-Prop
        ( is-group-Prop (pr1 G))
        ( is-decidable-Σ-count
          ( count-Σ
            ( pair n e)
            ( λ u →
              count-prod
                ( count-Π
                  ( pair n e)
                  ( λ x →
                    count-eq
                      ( has-decidable-equality-count (pair n e))
                      ( mul-Semi-Group (pr1 G) u x)
                      ( x)))
                ( count-Π
                  ( pair n e)
                  ( λ x →
                    count-eq
                      ( has-decidable-equality-count (pair n e))
                      ( mul-Semi-Group (pr1 G) x u)
                      ( x)))))
          ( λ u →
            is-decidable-Σ-count
              ( count-function-type (pair n e) (pair n e))
              ( λ i →
                is-decidable-prod
                  ( is-decidable-Π-count
                    ( pair n e)
                    ( λ x →
                      has-decidable-equality-count
                        ( pair n e)
                        ( mul-Semi-Group (pr1 G) (i x) x)
                        ( pr1 u)))
                  ( is-decidable-Π-count
                    ( pair n e)
                    ( λ x →
                      has-decidable-equality-count
                        ( pair n e)
                        ( mul-Semi-Group (pr1 G) x (i x))
                        ( pr1 u)))))))

is-homotopy-finite-Group-of-Order :
  {l : Level} (k n : ℕ) → is-homotopy-finite k (Group-of-Order l n)
is-homotopy-finite-Group-of-Order {l} k n =
  is-homotopy-finite-equiv k e
    ( is-homotopy-finite-Σ k
      ( is-homotopy-finite-Semi-Group-of-Order (succ-ℕ k) n)
      ( λ X →
        is-homotopy-finite-is-finite k
          ( is-finite-is-group X)))
  where
  e : Group-of-Order l n ≃
      Σ (Semi-Group-of-Order l n) (λ X → is-group (pr1 X))
  e = equiv-right-swap-Σ

number-of-groups-of-order : ℕ → ℕ
number-of-groups-of-order n =
  number-of-connected-components
    ( is-homotopy-finite-Group-of-Order {lzero} zero-ℕ n)

mere-equiv-number-of-groups-of-order :
  (n : ℕ) →
  mere-equiv
    ( Fin (number-of-groups-of-order n))
    ( type-trunc-Set (Group-of-Order lzero n))
mere-equiv-number-of-groups-of-order n =
  mere-equiv-number-of-connected-components
    ( is-homotopy-finite-Group-of-Order {lzero} zero-ℕ n)
