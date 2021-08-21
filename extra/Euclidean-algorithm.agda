{-# OPTIONS --without-K --exact-split #-}

module extra.Euclidean-algorithm where

open import book public

-- The Euclidean algorithm

subtract-ℕ : ℕ → ℕ → ℕ
subtract-ℕ zero-ℕ zero-ℕ = zero-ℕ
subtract-ℕ zero-ℕ (succ-ℕ b) = zero-ℕ
subtract-ℕ (succ-ℕ a) zero-ℕ = succ-ℕ a
subtract-ℕ (succ-ℕ a) (succ-ℕ b) = subtract-ℕ a b

leq-subtract-ℕ : (a b : ℕ) → leq-ℕ (subtract-ℕ a b) a
leq-subtract-ℕ zero-ℕ zero-ℕ = star
leq-subtract-ℕ zero-ℕ (succ-ℕ b) = star
leq-subtract-ℕ (succ-ℕ a) zero-ℕ = refl-leq-ℕ a
leq-subtract-ℕ (succ-ℕ a) (succ-ℕ b) =
  transitive-leq-ℕ (subtract-ℕ a b) a (succ-ℕ a)
    ( leq-subtract-ℕ a b)
    ( succ-leq-ℕ a)

decide-order-ℕ : (a b : ℕ) → coprod (leq-ℕ b a) (le-ℕ a b)
decide-order-ℕ zero-ℕ zero-ℕ = inl star
decide-order-ℕ zero-ℕ (succ-ℕ b) = inr star
decide-order-ℕ (succ-ℕ a) zero-ℕ = inl star
decide-order-ℕ (succ-ℕ a) (succ-ℕ b) = decide-order-ℕ a b

cases-gcd-euclid :
  ( a b : ℕ)
  ( F : (x : ℕ) (p : leq-ℕ x a) → ℕ → ℕ)
  ( G : (y : ℕ) (q : leq-ℕ y b) → ℕ) →
  ( coprod (leq-ℕ b a) (le-ℕ a b)) → ℕ
cases-gcd-euclid a b F G (inl t) =
  F (subtract-ℕ a b) (leq-subtract-ℕ a b) (succ-ℕ b)
cases-gcd-euclid a b F G (inr t) =
  G (subtract-ℕ b a) (leq-subtract-ℕ b a)

succ-gcd-euclid : (a : ℕ) (F : (x : ℕ) → (leq-ℕ x a) → ℕ → ℕ) → ℕ → ℕ
succ-gcd-euclid a F =
  strong-ind-ℕ
    ( λ x → ℕ)
    ( succ-ℕ a)
    ( λ b G →
      ind-coprod
        { A = leq-ℕ b a}
        { B = le-ℕ a b}
        ( λ x → ℕ)
        ( λ t → F (subtract-ℕ a b) (leq-subtract-ℕ a b) (succ-ℕ b))
        ( λ t → G (subtract-ℕ b a) (leq-subtract-ℕ b a))
        ( decide-order-ℕ a b))

comp-zero-succ-gcd-euclid :
  (a : ℕ) (F : (x : ℕ) → (leq-ℕ x a) → ℕ → ℕ) →
  Id (succ-gcd-euclid a F zero-ℕ) (succ-ℕ a)
comp-zero-succ-gcd-euclid a F =
  comp-zero-strong-ind-ℕ
    ( λ x → ℕ)
    ( succ-ℕ a)
    ( λ b G →
      ind-coprod
        { A = leq-ℕ b a}
        { B = le-ℕ a b}
        ( λ x → ℕ)
        ( λ t → F (subtract-ℕ a b) (leq-subtract-ℕ a b) (succ-ℕ b))
        ( λ t → G (subtract-ℕ b a) (leq-subtract-ℕ b a))
        ( decide-order-ℕ a b))

comp-succ-succ-gcd-euclid :
  (a : ℕ) (F : (x : ℕ) → (leq-ℕ x a) → ℕ → ℕ) (b : ℕ) →
  Id (succ-gcd-euclid a F (succ-ℕ b))
     ( ind-coprod
       { A = leq-ℕ b a}
       { B = le-ℕ a b}
       ( λ x → ℕ)
       ( λ t → F (subtract-ℕ a b) (leq-subtract-ℕ a b) (succ-ℕ b))
       ( λ t → succ-gcd-euclid a F (subtract-ℕ b a))
       ( decide-order-ℕ a b))
comp-succ-succ-gcd-euclid a F b =
  comp-succ-strong-ind-ℕ
    ( λ x → ℕ)
    ( succ-ℕ a)
    ( λ k z →
         ind-coprod (λ _ → ℕ)
         (λ x → F (subtract-ℕ a k) (leq-subtract-ℕ a k) (succ-ℕ k))
         (λ y → z (subtract-ℕ k a) (leq-subtract-ℕ k a))
         (decide-order-ℕ a k))
    ( b)

gcd-euclid : ℕ → ℕ → ℕ
gcd-euclid =
  strong-ind-ℕ
    ( λ x → ℕ → ℕ)
    ( id)
    ( succ-gcd-euclid)

comp-succ-gcd-euclid :
  (a : ℕ) →
  Id (gcd-euclid (succ-ℕ a)) (succ-gcd-euclid a (λ x p → gcd-euclid x))
comp-succ-gcd-euclid =
  comp-succ-strong-ind-ℕ (λ x → ℕ → ℕ) id succ-gcd-euclid

-- Properties of the greatest common divisor

left-zero-law-gcd-euclid : (gcd-euclid zero-ℕ) ~ id
left-zero-law-gcd-euclid =
  htpy-eq (comp-zero-strong-ind-ℕ (λ x → ℕ → ℕ) id succ-gcd-euclid)

right-zero-law-gcd-euclid : (a : ℕ) → Id (gcd-euclid a zero-ℕ) a
right-zero-law-gcd-euclid zero-ℕ = refl
right-zero-law-gcd-euclid (succ-ℕ a) =
   ( ap
     ( λ t →
       cases-succ-strong-ind-ℕ (λ x → ℕ → ℕ) succ-gcd-euclid a
       ( induction-strong-ind-ℕ
         ( λ x → ℕ → ℕ)
         ( zero-strong-ind-ℕ (λ x → ℕ → ℕ) (λ a₁ → a₁))
         ( λ k H m p →
           cases-succ-strong-ind-ℕ (λ x → ℕ → ℕ) succ-gcd-euclid k H m
           (cases-leq-succ-ℕ p))
         ( a))
       ( succ-ℕ a) t zero-ℕ)
     cases-leq-succ-reflexive-leq-ℕ) ∙
  ( comp-zero-succ-gcd-euclid a (λ x _ z → z))

is-prop-le-ℕ : (a b : ℕ) → is-prop (le-ℕ a b)
is-prop-le-ℕ zero-ℕ zero-ℕ = is-prop-empty
is-prop-le-ℕ zero-ℕ (succ-ℕ b) = is-prop-unit
is-prop-le-ℕ (succ-ℕ a) zero-ℕ = is-prop-empty
is-prop-le-ℕ (succ-ℕ a) (succ-ℕ b) = is-prop-le-ℕ a b

all-elements-equal-le-ℕ : (a b : ℕ) → all-elements-equal (le-ℕ a b)
all-elements-equal-le-ℕ a b = eq-is-prop' (is-prop-le-ℕ a b)
