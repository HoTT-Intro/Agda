{-# OPTIONS --without-K --exact-split --safe #-}

module 08-decidability-in-number-theory where

import 07-finite-types
open 07-finite-types public

--------------------------------------------------------------------------------

-- Section 8 Decidability in elementary number theory

is-decidable-leq-ℕ :
  (m n : ℕ) → is-decidable (leq-ℕ m n)
is-decidable-leq-ℕ zero-ℕ zero-ℕ = inl star
is-decidable-leq-ℕ zero-ℕ (succ-ℕ n) = inl star
is-decidable-leq-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-leq-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-leq-ℕ m n

is-decidable-le-ℕ :
  (m n : ℕ) → is-decidable (le-ℕ m n)
is-decidable-le-ℕ zero-ℕ zero-ℕ = inr id
is-decidable-le-ℕ zero-ℕ (succ-ℕ n) = inl star
is-decidable-le-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-le-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-le-ℕ m n

--------------------------------------------------------------------------------

-- Section 8.1 Decidability and decidable equality

--------------------------------------------------------------------------------

-- Section 8.2 The well-ordering principle of ℕ

--------------------------------------------------------------------------------

-- Section 8.3 The greatest common divisor

--------------------------------------------------------------------------------

-- Section 8.4 The infinitude of primes
