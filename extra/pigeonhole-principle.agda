{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module extra.pigeonhole-principle where

open import book.16-finite-types public

-- We show that every function Fin k → Fin l repeats itself if l < k.

is-repetition :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (a : A) → UU (l1 ⊔ l2)
is-repetition {l1} {l2} {A} {B} f a = Σ A (λ x → ¬ (Id a x) × (Id (f a) (f x)))

is-decidable-is-repetition-Fin :
  {k l : ℕ} (f : Fin k → Fin l) (x : Fin k) → is-decidable (is-repetition f x)
is-decidable-is-repetition-Fin f x =
  is-decidable-Σ-Fin
    ( λ y →
      is-decidable-prod
        ( is-decidable-neg (has-decidable-equality-Fin x y))
        ( has-decidable-equality-Fin (f x) (f y)))

has-repetition :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → UU (l1 ⊔ l2)
has-repetition {A = A} f = Σ A (is-repetition f)

is-decidable-has-repetition-Fin :
  {k l : ℕ} (f : Fin k → Fin l) → is-decidable (has-repetition f)
is-decidable-has-repetition-Fin f =
  is-decidable-Σ-Fin (is-decidable-is-repetition-Fin f)

exists-not-not-forall-Fin :
  {l : Level} {k : ℕ} {P : Fin k → UU l} → (is-decidable-fam P) →
  ¬ ((x : Fin k) → P x) → Σ (Fin k) (λ x → ¬ (P x))
exists-not-not-forall-Fin {l} {zero-ℕ} d H = ex-falso (H ind-empty)
exists-not-not-forall-Fin {l} {succ-ℕ k} {P} d H with d (inr star)
... | inl p =
  map-Σ
    ( λ x → ¬ (P x))
    ( inl)
    ( λ x → id)
    ( exists-not-not-forall-Fin
      ( λ x → d (inl x))
      ( λ f → H (ind-coprod P f (ind-unit p))))
... | inr f = pair (inr star) f

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

has-repetition-le-Fin :
  {k l : ℕ} (f : Fin k → Fin l) → le-ℕ l k → has-repetition f
has-repetition-le-Fin f p =
  has-repetition-is-not-injective-Fin f (is-not-injective-le-Fin f p)

has-repetition-Fin-succ-to-Fin :
  {k : ℕ} (f : Fin (succ-ℕ k) → Fin k) → has-repetition f
has-repetition-Fin-succ-to-Fin {k} f =
  has-repetition-le-Fin f (le-succ-ℕ {k})

has-repetition-left-factor :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {g : B → C}
  {f : A → B} → is-injective f → has-repetition (g ∘ f) → has-repetition g
has-repetition-left-factor {g = g} {f} H (pair a (pair b (pair K p))) =
  pair (f a) (pair (f b) (pair (λ q → K (H q)) p))

has-repetition-nat-to-Fin :
  {k : ℕ} (f : ℕ → Fin k) → has-repetition f
has-repetition-nat-to-Fin {k} f =
  has-repetition-left-factor
    ( is-injective-nat-Fin {succ-ℕ k})
    ( has-repetition-Fin-succ-to-Fin (f ∘ nat-Fin))

has-ordered-repetition-ℕ :
  {l1 : Level} {A : UU l1} (f : ℕ → A) → UU l1
has-ordered-repetition-ℕ f = Σ ℕ (λ x → Σ ℕ (λ y → (le-ℕ y x) × Id (f y) (f x)))

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

first-repetition-nat-to-Fin :
  {k : ℕ} (f : ℕ → Fin k) →
  minimal-element-ℕ (λ x → Σ ℕ (λ y → (le-ℕ y x) × (Id (f y) (f x))))
first-repetition-nat-to-Fin f =
  well-ordering-principle-ℕ
    ( λ x → Σ ℕ (λ y → (le-ℕ y x) × (Id (f y) (f x))))
    ( λ x →
      is-decidable-strictly-bounded-Σ-ℕ
        ( λ y → le-ℕ y x)
        ( λ y → Id (f y) (f x))
        ( λ y → is-decidable-le-ℕ y x)
        ( λ y → has-decidable-equality-Fin (f y) (f x))
        ( x)
        ( λ y → id))
    ( has-ordered-repetition-nat-to-Fin f)
