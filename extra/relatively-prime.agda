{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module extra.relatively-prime where

open import book.08-decidability-in-number-theory public

{-------------------------------------------------------------------------------

  Some basic results about relatively prime numbers

-------------------------------------------------------------------------------}

relatively-prime-ℕ : ℕ → ℕ → UU lzero
relatively-prime-ℕ x y = (d : ℕ) → is-common-divisor-ℕ x y d → is-one-ℕ d

concatenate-eq-relatively-prime-ℕ :
  {x y z : ℕ} → Id x y → relatively-prime-ℕ y z → relatively-prime-ℕ x z
concatenate-eq-relatively-prime-ℕ refl = id

concatenate-relatively-prime-eq-ℕ :
  {x y z : ℕ} → relatively-prime-ℕ x y → Id y z → relatively-prime-ℕ x z
concatenate-relatively-prime-eq-ℕ H refl = H

concatenate-eq-relatively-prime-eq-ℕ :
  {x y z w : ℕ} → Id x y → relatively-prime-ℕ y z → Id z w →
  relatively-prime-ℕ x w
concatenate-eq-relatively-prime-eq-ℕ refl H refl = H

is-one-gcd-relatively-prime-ℕ :
  (x y : ℕ) → relatively-prime-ℕ x y → is-one-ℕ (gcd-ℕ x y)
is-one-gcd-relatively-prime-ℕ x y H =
  H (gcd-ℕ x y) (is-common-divisor-gcd-ℕ x y)

relatively-prime-is-one-gcd-ℕ :
  (x y : ℕ) → is-one-ℕ (gcd-ℕ x y) → relatively-prime-ℕ x y
relatively-prime-is-one-gcd-ℕ x y p d H =
  is-one-div-one-ℕ d
    ( concatenate-div-eq-ℕ (div-gcd-is-common-divisor-ℕ x y d H) p)

is-decidable-relatively-prime-ℕ :
  (x y : ℕ) → is-decidable (relatively-prime-ℕ x y)
is-decidable-relatively-prime-ℕ x y =
  is-decidable-iff
    ( relatively-prime-is-one-gcd-ℕ x y)
    ( is-one-gcd-relatively-prime-ℕ x y)
    ( is-decidable-is-one-ℕ (gcd-ℕ x y))

antireflexive-relatively-prime-ℕ :
  (x : ℕ) → relatively-prime-ℕ x x → is-one-ℕ x
antireflexive-relatively-prime-ℕ x H = H x (refl-is-common-divisor-ℕ x)

symmetric-relatively-prime-ℕ :
  {x y : ℕ} → relatively-prime-ℕ x y → relatively-prime-ℕ y x
symmetric-relatively-prime-ℕ H d (pair k l) = H d (pair l k)

relatively-prime-one-ℕ :
  (x : ℕ) → relatively-prime-ℕ one-ℕ x
relatively-prime-one-ℕ x d (pair k l) = is-one-div-one-ℕ d k

relatively-prime-one-ℕ' :
  (x : ℕ) → relatively-prime-ℕ x one-ℕ
relatively-prime-one-ℕ' x d (pair k l) = is-one-div-one-ℕ d l

relatively-prime-is-one-ℕ :
  (x y : ℕ) → is-one-ℕ x → relatively-prime-ℕ x y
relatively-prime-is-one-ℕ .one-ℕ y refl = relatively-prime-one-ℕ y

relatively-prime-is-one-ℕ' :
  (x y : ℕ) → is-one-ℕ y → relatively-prime-ℕ x y
relatively-prime-is-one-ℕ' x .one-ℕ refl = relatively-prime-one-ℕ' x

translation-relatively-prime' :
  (x y : ℕ) → relatively-prime-ℕ x y → relatively-prime-ℕ x (add-ℕ y x)
translation-relatively-prime' x y H d (pair k l) =
  H d (pair k (div-left-summand-ℕ d y x k l))

translation-relatively-prime :
  (k x y : ℕ) → relatively-prime-ℕ x y →
  relatively-prime-ℕ x (add-ℕ y (mul-ℕ k x))
translation-relatively-prime zero-ℕ x y H = H
translation-relatively-prime (succ-ℕ k) x y H =
  concatenate-relatively-prime-eq-ℕ
    ( translation-relatively-prime' x
      ( add-ℕ y (mul-ℕ k x))
      ( translation-relatively-prime k x y H))
    ( associative-add-ℕ y (mul-ℕ k x) x)

relatively-prime-Fibonacci-ℕ :
  (n : ℕ) → relatively-prime-ℕ (Fibonacci-ℕ n) (Fibonacci-ℕ (succ-ℕ n))
relatively-prime-Fibonacci-ℕ zero-ℕ =
  relatively-prime-one-ℕ' zero-ℕ
relatively-prime-Fibonacci-ℕ (succ-ℕ n) =
  concatenate-relatively-prime-eq-ℕ
    ( translation-relatively-prime'
      ( Fibonacci-ℕ (succ-ℕ n))
      ( Fibonacci-ℕ n)
      ( symmetric-relatively-prime-ℕ (relatively-prime-Fibonacci-ℕ n)))
    ( commutative-add-ℕ (Fibonacci-ℕ n) (Fibonacci-ℕ (succ-ℕ n)))

relatively-prime-is-prime-ℕ :
  (x p : ℕ) → is-prime-ℕ p → ¬ (div-ℕ p x) → relatively-prime-ℕ x p
relatively-prime-is-prime-ℕ x p H f d (pair k l) =
  pr1 (H d) (pair (λ q → f (concatenate-eq-div-ℕ (inv q) k)) l)

decide-relatively-prime-is-prime-ℕ :
  (x p : ℕ) → is-prime-ℕ p → coprod (div-ℕ p x) (relatively-prime-ℕ x p)
decide-relatively-prime-is-prime-ℕ x p H =
  map-coprod id (relatively-prime-is-prime-ℕ x p H) (is-decidable-div-ℕ p x)

div-right-factor-ℕ :
  (x y z : ℕ) → relatively-prime-ℕ x y → div-ℕ x (mul-ℕ y z) → div-ℕ x z
div-right-factor-ℕ x y z H1 H2 = {!!}

A ↪ A × A
Σ (X : U), ||X ≃ Fin n||
Π (A : Bℤ₂), A+A ≃ A×A

Π (A : U) → (is an n-element set (A)) -> (A ↪ A×A)

∥[n]≃X∥
