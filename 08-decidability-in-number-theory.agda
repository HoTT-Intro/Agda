{-# OPTIONS --without-K --exact-split --safe #-}

module 08-decidability-in-number-theory where

import 07-finite-types
open 07-finite-types public

--------------------------------------------------------------------------------

{- Section 8 Decidability in elementary number theory -}

--------------------------------------------------------------------------------

{- Section 8.1 Decidability and decidable equality -}

{- Definition 8.1.1 -}

is-decidable : {l : Level} (A : UU l) → UU l
is-decidable A = coprod A (¬ A)

{- Example 8.1.2 -}

is-decidable-unit : is-decidable unit
is-decidable-unit = inl star

is-decidable-empty : is-decidable empty
is-decidable-empty = inr id

{- Example 8.1.3 -}

is-decidable-Eq-ℕ :
  (m n : ℕ) → is-decidable (Eq-ℕ m n)
is-decidable-Eq-ℕ zero-ℕ zero-ℕ = inl star
is-decidable-Eq-ℕ zero-ℕ (succ-ℕ n) = inr id
is-decidable-Eq-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-Eq-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-Eq-ℕ m n

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

{- Definition 8.1.4 -}
   
has-decidable-equality : {l : Level} (A : UU l) → UU l
has-decidable-equality A = (x y : A) → is-decidable (Id x y)

{- Proposition 8.1.5 -}

{- The type ℕ is an example of a type with decidable equality. -}

is-decidable-iff :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A → B) → (B → A) → is-decidable A → is-decidable B
is-decidable-iff f g =
  functor-coprod f (functor-neg g)

has-decidable-equality-ℕ : has-decidable-equality ℕ
has-decidable-equality-ℕ x y =
  is-decidable-iff (eq-Eq-ℕ x y) Eq-ℕ-eq (is-decidable-Eq-ℕ x y)

{- Proposition 8.1.6 -}

{- We show that Fin k has decidable equality, for each k : ℕ. -}

is-decidable-Eq-Fin :
  (k : ℕ) (x y : Fin k) → is-decidable (Eq-Fin k x y)
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inl y) = is-decidable-Eq-Fin k x y
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inr y) = inr id
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inl y) = inr id
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inr y) = inl star

has-decidable-equality-Fin :
  (k : ℕ) (x y : Fin k) → is-decidable (Id x y)
has-decidable-equality-Fin k x y =
  functor-coprod eq-Eq-Fin (functor-neg Eq-Fin-eq) (is-decidable-Eq-Fin k x y)

{- Corollary 8.1.7 -}

is-decidable-div-ℕ :
  (d x : ℕ) → is-decidable (div-ℕ d x)
is-decidable-div-ℕ zero-ℕ x =
  is-decidable-iff
    ( div-eq-ℕ zero-ℕ x)
    ( inv ∘ (eq-zero-div-zero-ℕ x))
    ( has-decidable-equality-ℕ zero-ℕ x)
is-decidable-div-ℕ (succ-ℕ d) x =
  is-decidable-iff
    ( div-succ-eq-zero-ℕ d x)
    ( eq-zero-div-succ-ℕ d x)
    ( has-decidable-equality-Fin (succ-ℕ d) (mod-succ-ℕ d x) zero-Fin)

--------------------------------------------------------------------------------

{- Section 8.2 The well-ordering principle of ℕ -}

--------------------------------------------------------------------------------

{- Section 8.3 The greatest common divisor -}

--------------------------------------------------------------------------------

{- Section 8.4 The infinitude of primes -}

--------------------------------------------------------------------------------

{- Proposition 7.2.6 -}

{- Section 7.3 Definitions by case analysis -}

{- We define an alternative definition of the predecessor function with manual 
   with-abstraction. -}

cases-pred-Fin-2 :
  {k : ℕ} (x : Fin (succ-ℕ k))
  (d : is-decidable (Eq-Fin (succ-ℕ k) x zero-Fin)) → Fin (succ-ℕ k)
cases-pred-Fin-2 {zero-ℕ} (inr star) d = zero-Fin
cases-pred-Fin-2 {succ-ℕ k} (inl x) (inl e) = neg-one-Fin
cases-pred-Fin-2 {succ-ℕ k} (inl x) (inr f) =
  inl (cases-pred-Fin-2 {k} x (inr f))
cases-pred-Fin-2 {succ-ℕ k} (inr star) (inr f) = inl neg-one-Fin

pred-Fin-2 : {k : ℕ} → Fin k → Fin k
pred-Fin-2 {succ-ℕ k} x =
  cases-pred-Fin-2 {k} x (is-decidable-Eq-Fin (succ-ℕ k) x zero-Fin)

{- We give a solution to the exercise for the alternative definition of the
   predecessor function, using with-abstraction. -}

pred-zero-Fin-2 :
  {k : ℕ} → Id (pred-Fin-2 {succ-ℕ k} zero-Fin) neg-one-Fin
pred-zero-Fin-2 {k} with is-decidable-Eq-Fin (succ-ℕ k) zero-Fin zero-Fin
pred-zero-Fin-2 {zero-ℕ} | d = refl
pred-zero-Fin-2 {succ-ℕ k} | inl e = refl
pred-zero-Fin-2 {succ-ℕ k} | inr f =
  ex-falso (f (refl-Eq-Fin {succ-ℕ k} zero-Fin))
  
cases-succ-pred-Fin-2 :
  {k : ℕ} (x : Fin (succ-ℕ k))
  (d : is-decidable (Eq-Fin (succ-ℕ k) x zero-Fin)) →
  Id (succ-Fin (cases-pred-Fin-2 x d)) x
cases-succ-pred-Fin-2 {zero-ℕ} (inr star) d =
  refl
cases-succ-pred-Fin-2 {succ-ℕ k} (inl x) (inl e) =
  inv (eq-Eq-Fin e)
cases-succ-pred-Fin-2 {succ-ℕ zero-ℕ} (inl (inr x)) (inr f) =
  ex-falso (f star)
cases-succ-pred-Fin-2 {succ-ℕ (succ-ℕ k)} (inl (inl x)) (inr f) =
  ap inl (cases-succ-pred-Fin-2 (inl x) (inr f))
cases-succ-pred-Fin-2 {succ-ℕ (succ-ℕ k)} (inl (inr star)) (inr f) =
  refl
cases-succ-pred-Fin-2 {succ-ℕ k} (inr star) (inr f) =
  refl

succ-pred-Fin-2 :
  {k : ℕ} (x : Fin k) → Id (succ-Fin (pred-Fin-2 x)) x
succ-pred-Fin-2 {succ-ℕ k} x =
  cases-succ-pred-Fin-2 x (is-decidable-Eq-Fin (succ-ℕ k) x zero-Fin)

pred-inl-Fin-2 :
  {k : ℕ} (x : Fin (succ-ℕ k)) (f : ¬ (Eq-Fin (succ-ℕ k) x zero-Fin)) →
  Id (pred-Fin-2 (inl x)) (inl (pred-Fin-2 x))
pred-inl-Fin-2 {k} x f with is-decidable-Eq-Fin (succ-ℕ k) x zero-Fin
... | inl e = ex-falso (f e)
... | inr f' = refl

nEq-zero-succ-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) →
  ¬ (Eq-Fin (succ-ℕ (succ-ℕ k)) (succ-Fin (inl x)) zero-Fin)
nEq-zero-succ-Fin {succ-ℕ k} (inl (inl x)) e = nEq-zero-succ-Fin (inl x) e
nEq-zero-succ-Fin {succ-ℕ k} (inl (inr star)) ()
nEq-zero-succ-Fin {succ-ℕ k} (inr star) ()

pred-succ-Fin-2 :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (pred-Fin-2 (succ-Fin x)) x
pred-succ-Fin-2 {zero-ℕ} (inr star) = refl
pred-succ-Fin-2 {succ-ℕ zero-ℕ} (inl (inr star)) = refl
pred-succ-Fin-2 {succ-ℕ zero-ℕ} (inr star) = refl
pred-succ-Fin-2 {succ-ℕ (succ-ℕ k)} (inl (inl (inl x))) =
  ( pred-inl-Fin-2 (inl (succ-Fin (inl x))) (nEq-zero-succ-Fin (inl x))) ∙
  ( ( ap inl (pred-inl-Fin-2 (succ-Fin (inl x)) (nEq-zero-succ-Fin (inl x)))) ∙
    ( ap (inl ∘ inl) (pred-succ-Fin-2 (inl x))))
pred-succ-Fin-2 {succ-ℕ (succ-ℕ k)} (inl (inl (inr star))) = refl
pred-succ-Fin-2 {succ-ℕ (succ-ℕ k)} (inl (inr star)) = refl
pred-succ-Fin-2 {succ-ℕ (succ-ℕ k)} (inr star) = pred-zero-Fin-2
