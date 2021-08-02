{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module extra.pigeonhole-principle where

open import book.16-finite-types public

-- We show that every function ℕ → Fin k repeats itself

is-not-injective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → UU (l1 ⊔ l2)
is-not-injective f = ¬ (is-injective f)

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
  

is-repetition-nat-to-Fin :
  (k : ℕ) (f : ℕ → Fin k) (x : ℕ) → UU lzero
is-repetition-nat-to-Fin k f x = Σ ℕ (λ y → (le-ℕ y x) × (Id (f x) (f y)))

is-decidable-is-repetition-nat-to-Fin :
  (k : ℕ) (f : ℕ → Fin k) (x : ℕ) →
  is-decidable (is-repetition-nat-to-Fin k f x)
is-decidable-is-repetition-nat-to-Fin k f x =
  is-decidable-strictly-bounded-Σ-ℕ'
    ( λ y → Id (f x) (f y))
    ( λ y → has-decidable-equality-Fin (f x) (f y))
    ( x)

repeats-nat-to-Fin' :
  (k : ℕ) (f : ℕ → Fin k) →
  Σ ℕ (λ x → (leq-ℕ x (succ-ℕ k)) × (is-repetition-nat-to-Fin k f x))
repeats-nat-to-Fin' zero-ℕ f = ex-falso (f zero-ℕ)
repeats-nat-to-Fin' (succ-ℕ k) f with
  is-decidable-is-repetition-nat-to-Fin (succ-ℕ k) f (succ-ℕ (succ-ℕ k))
... | inl r =
  pair
    ( succ-ℕ (succ-ℕ k))
    ( pair
      ( refl-leq-ℕ (succ-ℕ (succ-ℕ k)))
      ( r))
... | inr g = {!!}
