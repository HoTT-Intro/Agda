{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module extra.pigeonhole-principle where

open import book public

{-------------------------------------------------------------------------------

  The Pigeonhole Principle
  ------------------------

  In this file we prove some facts related to the pigeonhole principle, which
  asserts that for n < m, a map f : X → Y from a set X with m elements to a set
  Y with n elements, maps at least two distinct elements in X to the same
  element in Y.

-------------------------------------------------------------------------------}

-- We define the predicate that the value of f at x is a value of f at another y

is-repetition :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (a : A) → UU (l1 ⊔ l2)
is-repetition {l1} {l2} {A} {B} f a = Σ A (λ x → ¬ (Id a x) × (Id (f a) (f x)))

-- On the standard finite sets, is-repetition f a is decidable

is-decidable-is-repetition-Fin :
  {k l : ℕ} (f : Fin k → Fin l) (x : Fin k) → is-decidable (is-repetition f x)
is-decidable-is-repetition-Fin f x =
  is-decidable-Σ-Fin
    ( λ y →
      is-decidable-prod
        ( is-decidable-neg (has-decidable-equality-Fin x y))
        ( has-decidable-equality-Fin (f x) (f y)))

-- We define the predicate that f maps two different elements to the same value

has-repetition :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → UU (l1 ⊔ l2)
has-repetition {A = A} f = Σ A (is-repetition f)

has-repetition-comp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (g : B → C)
  {f : A → B} → has-repetition f → has-repetition (g ∘ f)
has-repetition-comp g (pair x (pair y (pair s t))) =
  pair x (pair y (pair s (ap g t)))

has-repetition-left-factor :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {g : B → C}
  {f : A → B} → is-emb f → has-repetition (g ∘ f) → has-repetition g
has-repetition-left-factor {g = g} {f} H (pair a (pair b (pair K p))) =
  pair (f a) (pair (f b) (pair (λ q → K (is-injective-is-emb H q)) p))

has-repetition-right-factor :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {g : B → C}
  {f : A → B} → is-emb g → has-repetition (g ∘ f) → has-repetition f
has-repetition-right-factor {g = g} {f} H (pair a (pair b (pair K p))) =
  pair a (pair b (pair K (is-injective-is-emb H p)))

-- On the standard finite sets, has-repetition f is decidable

is-decidable-has-repetition-Fin :
  {k l : ℕ} (f : Fin k → Fin l) → is-decidable (has-repetition f)
is-decidable-has-repetition-Fin f =
  is-decidable-Σ-Fin (is-decidable-is-repetition-Fin f)

-- If f is not injective, then it has a repetition.

is-injective-map-Fin-zero-Fin :
  {k : ℕ} (f : Fin zero-ℕ → Fin k) → is-injective f
is-injective-map-Fin-zero-Fin f {()} {y}

is-injective-map-Fin-one-Fin :
  {k : ℕ} (f : Fin one-ℕ → Fin k) → is-injective f
is-injective-map-Fin-one-Fin f {inr star} {inr star} p = refl

has-repetition-is-not-injective-Fin :
  {k l : ℕ} (f : Fin l → Fin k) → is-not-injective f → has-repetition f
has-repetition-is-not-injective-Fin {l = zero-ℕ} f H =
  ex-falso (H (is-injective-map-Fin-zero-Fin f))
has-repetition-is-not-injective-Fin {l = succ-ℕ l} f H with
  is-decidable-is-repetition-Fin f (inr star)
... | inl r = pair (inr star) r
... | inr g = α (has-repetition-is-not-injective-Fin {l = l} (f ∘ inl) K)
  where
  K : is-not-injective (f ∘ inl)
  K I = H (λ {x} {y} → J x y)
    where
    J : (x y : Fin (succ-ℕ l)) → Id (f x) (f y) → Id x y
    J (inl x) (inl y) p = ap inl (I p)
    J (inl x) (inr star) p = ex-falso (g (triple (inl x) Eq-Fin-eq (inv p)))
    J (inr star) (inl y) p = ex-falso (g (triple (inl y) Eq-Fin-eq p))
    J (inr star) (inr star) p = refl
  α : has-repetition (f ∘ inl) → has-repetition f
  α (pair x (pair y (pair h q))) =
    pair (inl x) (pair (inl y) (pair (λ r → h (is-injective-inl r)) q))

-- If f : Fin k → Fin l and l < k, then f has a repetition

has-repetition-le-Fin :
  {k l : ℕ} (f : Fin k → Fin l) → le-ℕ l k → has-repetition f
has-repetition-le-Fin f p =
  has-repetition-is-not-injective-Fin f (is-not-injective-le-Fin f p)

has-repetition-le-count :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (eA : count A) (eB : count B) →
  (f : A → B) →
  le-ℕ (number-of-elements-count eB) (number-of-elements-count eA) →
  has-repetition f
has-repetition-le-count eA eB f p =
  has-repetition-right-factor
    ( is-emb-is-equiv (is-equiv-map-inv-equiv (equiv-count eB)))
    ( has-repetition-left-factor
      ( is-emb-is-equiv (is-equiv-map-equiv (equiv-count eA)))
      ( has-repetition-le-Fin
        ( map-equiv (inv-equiv-count eB) ∘ (f ∘ map-equiv-count eA))
        ( p)))

has-repetition-Fin-succ-to-Fin :
  {k : ℕ} (f : Fin (succ-ℕ k) → Fin k) → has-repetition f
has-repetition-Fin-succ-to-Fin {k} f =
  has-repetition-le-Fin f (le-succ-ℕ {k})

has-repetition-nat-to-Fin :
  {k : ℕ} (f : ℕ → Fin k) → has-repetition f
has-repetition-nat-to-Fin {k} f =
  has-repetition-left-factor
    ( is-emb-nat-Fin {succ-ℕ k})
    ( has-repetition-Fin-succ-to-Fin (f ∘ nat-Fin))

has-repetition-nat-to-count :
  {l : Level} {A : UU l} (e : count A) (f : ℕ → A) → has-repetition f
has-repetition-nat-to-count e f =
  has-repetition-right-factor
    ( is-emb-is-equiv (is-equiv-map-inv-equiv (equiv-count e)))
    ( has-repetition-nat-to-Fin (map-inv-equiv-count e ∘ f))

--------------------------------------------------------------------------------

{- We also formalize ordered repetitions of maps ℕ → A -}

is-ordered-repetition-ℕ :
  {l1 : Level} {A : UU l1} (f : ℕ → A) (x : ℕ) → UU l1
is-ordered-repetition-ℕ f x = Σ ℕ (λ y → (le-ℕ y x) × Id (f y) (f x))

is-decidable-is-ordered-repetition-ℕ-Fin :
  {k : ℕ} (f : ℕ → Fin k) (x : ℕ) → is-decidable (is-ordered-repetition-ℕ f x)
is-decidable-is-ordered-repetition-ℕ-Fin f x =
  is-decidable-strictly-bounded-Σ-ℕ' x
    ( λ y → Id (f y) (f x))
    ( λ y → has-decidable-equality-Fin (f y) (f x))

is-decidable-is-ordered-repetition-ℕ-count :
  {l : Level} {A : UU l} (e : count A) (f : ℕ → A) (x : ℕ) →
  is-decidable (is-ordered-repetition-ℕ f x)
is-decidable-is-ordered-repetition-ℕ-count e f x =
  is-decidable-strictly-bounded-Σ-ℕ' x
    ( λ y → Id (f y) (f x))
    ( λ y → has-decidable-equality-count e (f y) (f x))

has-ordered-repetition-ℕ :
  {l1 : Level} {A : UU l1} (f : ℕ → A) → UU l1
has-ordered-repetition-ℕ f = Σ ℕ (is-ordered-repetition-ℕ f)

has-ordered-repetition-comp-ℕ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (g : A → B) {f : ℕ → A} →
  has-ordered-repetition-ℕ f → has-ordered-repetition-ℕ (g ∘ f)
has-ordered-repetition-comp-ℕ g (pair a (pair b (pair H p))) =
  pair a (pair b (pair H (ap g p)))

has-ordered-repetition-right-factor-ℕ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {g : A → B} {f : ℕ → A} →
  is-emb g → has-ordered-repetition-ℕ (g ∘ f) → has-ordered-repetition-ℕ f
has-ordered-repetition-right-factor-ℕ E (pair a (pair b (pair H p))) =
  pair a (pair b (pair H (is-injective-is-emb E p)))

has-ordered-repetition-nat-to-Fin :
  {k : ℕ} (f : ℕ → Fin k) → has-ordered-repetition-ℕ f
has-ordered-repetition-nat-to-Fin f with
  has-repetition-nat-to-Fin f
... | pair x (pair y (pair H p)) with is-decidable-le-ℕ y x
... | inl t = pair x (pair y (pair t (inv p)))
... | inr t = pair y (pair x (pair L p))
  where
  L : le-ℕ x y
  L = map-left-unit-law-coprod-is-empty
        ( Id y x)
        ( le-ℕ x y)
        ( λ q → H (inv q))
        ( map-left-unit-law-coprod-is-empty
          ( le-ℕ y x)
          ( coprod (Id y x)
          ( le-ℕ x y))
          ( t)
          ( linear-le-ℕ y x))

has-ordered-repetition-nat-to-count :
  {l : Level} {A : UU l} (e : count A) (f : ℕ → A) → has-ordered-repetition-ℕ f
has-ordered-repetition-nat-to-count e f =
  has-ordered-repetition-right-factor-ℕ
    ( is-emb-is-equiv (is-equiv-map-inv-equiv (equiv-count e)))
    ( has-ordered-repetition-nat-to-Fin
      ( map-inv-equiv-count e ∘ f))

first-repetition-nat-to-Fin :
  {k : ℕ} (f : ℕ → Fin k) →
  minimal-element-ℕ (λ x → Σ ℕ (λ y → (le-ℕ y x) × (Id (f y) (f x))))
first-repetition-nat-to-Fin f =
  well-ordering-principle-ℕ
    ( λ x → Σ ℕ (λ y → (le-ℕ y x) × (Id (f y) (f x))))
    ( λ x → is-decidable-strictly-bounded-Σ-ℕ' x
              ( λ y → Id (f y) (f x))
              ( λ y → has-decidable-equality-Fin (f y) (f x)))
    ( has-ordered-repetition-nat-to-Fin f)
