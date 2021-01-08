{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module extra.cofibonacci where

import book
open book public

--------------------------------------------------------------------------------

-- We show that every function ℕ → Fin k repeats itself

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
      ( reflexive-leq-ℕ (succ-ℕ (succ-ℕ k)))
      ( r))
... | inr g = {!!}

--------------------------------------------------------------------------------

subtype-cofibonacci : ℕ → ℕ → UU lzero
subtype-cofibonacci m n =
  (is-nonzero-ℕ m) → (is-nonzero-ℕ n) × (div-ℕ m (Fibonacci-ℕ n))

is-decidable-subtype-cofibonacci :
  (m n : ℕ) → is-decidable (subtype-cofibonacci m n)
is-decidable-subtype-cofibonacci m n =
  is-decidable-function-type
    ( is-decidable-is-nonzero-ℕ m)
    ( is-decidable-prod
      ( is-decidable-is-nonzero-ℕ n)
      ( is-decidable-div-ℕ m (Fibonacci-ℕ n)))

{- In order to show that for each m, there is an n such that
   subtype-cofibonacci m n holds, we compute the m-th Pisano period. -}

Fibonacci-Fin : (k : ℕ) → ℕ → Fin (succ-ℕ k)
Fibonacci-Fin k zero-ℕ = zero-Fin
Fibonacci-Fin k (succ-ℕ zero-ℕ) = one-Fin
Fibonacci-Fin k (succ-ℕ (succ-ℕ n)) =
  add-Fin (Fibonacci-Fin k (succ-ℕ n)) (Fibonacci-Fin k n)

eq-remainder-Fibonacci-ℕ :
  (k n : ℕ) → Id (mod-succ-ℕ k (Fibonacci-ℕ n)) (Fibonacci-Fin k n)
eq-remainder-Fibonacci-ℕ k zero-ℕ = refl
eq-remainder-Fibonacci-ℕ k (succ-ℕ zero-ℕ) = refl
eq-remainder-Fibonacci-ℕ k (succ-ℕ (succ-ℕ n)) = {!!}

pair-Fibonacci-Fin : (k : ℕ) → ℕ → (Fin (succ-ℕ k)) × (Fin (succ-ℕ k))
pair-Fibonacci-Fin k n = pair (Fibonacci-Fin k n) (Fibonacci-Fin k (succ-ℕ n))

-- We show that F(m+1)F(n+1) + F(m)F(n) = F(m+n+1)

identity-Fibonacci :
  (m n : ℕ) → Id ( add-ℕ
                   ( mul-ℕ (Fibonacci-ℕ (succ-ℕ m)) (Fibonacci-ℕ (succ-ℕ n)))
                   ( mul-ℕ (Fibonacci-ℕ m) (Fibonacci-ℕ n)))
                 ( Fibonacci-ℕ (succ-ℕ (add-ℕ m n)))
identity-Fibonacci zero-ℕ n =
  ( ap-add-ℕ
    ( left-unit-law-mul-ℕ (Fibonacci-ℕ (succ-ℕ n)))
    ( left-zero-law-mul-ℕ (Fibonacci-ℕ n))) ∙
  ( inv (ap Fibonacci-ℕ (left-unit-law-add-ℕ (succ-ℕ n))))
identity-Fibonacci (succ-ℕ m) n =
  ( ap ( add-ℕ' (mul-ℕ (Fibonacci-ℕ (succ-ℕ m)) (Fibonacci-ℕ n)))
       ( right-distributive-mul-add-ℕ
         ( Fibonacci-ℕ (succ-ℕ m))
         ( Fibonacci-ℕ m)
         ( Fibonacci-ℕ (succ-ℕ n)))) ∙
  ( ( commutative-add-ℕ
      ( add-ℕ
        ( mul-ℕ (Fibonacci-ℕ (succ-ℕ m)) (Fibonacci-ℕ (succ-ℕ n)))
        ( mul-ℕ (Fibonacci-ℕ m) (Fibonacci-ℕ (succ-ℕ n))))
      ( mul-ℕ (Fibonacci-ℕ (succ-ℕ m)) (Fibonacci-ℕ n))) ∙
    ( inv
      ( associative-add-ℕ
        ( mul-ℕ (Fibonacci-ℕ (succ-ℕ m)) (Fibonacci-ℕ n))
        ( mul-ℕ (Fibonacci-ℕ (succ-ℕ m)) (Fibonacci-ℕ (succ-ℕ n)))
        ( mul-ℕ (Fibonacci-ℕ m) (Fibonacci-ℕ (succ-ℕ n)))) ∙
      ( ( ap ( add-ℕ' ( mul-ℕ (Fibonacci-ℕ m) (Fibonacci-ℕ (succ-ℕ n))))
             ( ( commutative-add-ℕ
                 ( mul-ℕ (Fibonacci-ℕ (succ-ℕ m)) (Fibonacci-ℕ n))
                 ( mul-ℕ (Fibonacci-ℕ (succ-ℕ m)) (Fibonacci-ℕ (succ-ℕ n)))) ∙
               ( inv
                 ( left-distributive-mul-add-ℕ
                   ( Fibonacci-ℕ (succ-ℕ m))
                   ( Fibonacci-ℕ (succ-ℕ n))
                   ( Fibonacci-ℕ n))))) ∙
        ( ( identity-Fibonacci m (succ-ℕ n)) ∙
          ( inv (ap Fibonacci-ℕ (left-successor-law-add-ℕ m (succ-ℕ n))))))))
