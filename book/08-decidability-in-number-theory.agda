{-# OPTIONS --without-K --exact-split --safe #-}

module book.08-decidability-in-number-theory where

import book.07-finite-types
open book.07-finite-types public

--------------------------------------------------------------------------------

{- Section 8 Decidability in elementary number theory -}

--------------------------------------------------------------------------------

{- Section 8.1 Decidability and decidable equality -}

{- Definition 8.1.1 -}

is-decidable : {l : Level} (A : UU l) → UU l
is-decidable A = coprod A (¬ A)

is-decidable-fam :
  {l1 l2 : Level} {A : UU l1} (P : A → UU l2) → UU (l1 ⊔ l2)
is-decidable-fam {A = A} P = (x : A) → is-decidable (P x)

{- Example 8.1.2 -}

is-decidable-unit : is-decidable unit
is-decidable-unit = inl star

is-decidable-empty : is-decidable empty
is-decidable-empty = inr id

{- Example 8.1.3 -}

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

{- Example 8.1.4 -}

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

{- Definition 8.1.5 -}
   
has-decidable-equality : {l : Level} (A : UU l) → UU l
has-decidable-equality A = (x y : A) → is-decidable (Id x y)

{- Proposition 8.1.6 -}

is-decidable-iff :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A → B) → (B → A) → is-decidable A → is-decidable B
is-decidable-iff f g =
  functor-coprod f (functor-neg g)

{- Proposition 8.1.7 -}

has-decidable-equality-ℕ : has-decidable-equality ℕ
has-decidable-equality-ℕ x y =
  is-decidable-iff (eq-Eq-ℕ x y) Eq-ℕ-eq (is-decidable-Eq-ℕ x y)

-- We record some immediate corollaries

is-decidable-is-zero-ℕ : (n : ℕ) → is-decidable (is-zero-ℕ n)
is-decidable-is-zero-ℕ n = has-decidable-equality-ℕ n zero-ℕ

is-decidable-is-zero-ℕ' : (n : ℕ) → is-decidable (is-zero-ℕ' n)
is-decidable-is-zero-ℕ' n = has-decidable-equality-ℕ zero-ℕ n

is-decidable-is-nonzero-ℕ : (n : ℕ) → is-decidable (is-nonzero-ℕ n)
is-decidable-is-nonzero-ℕ n =
  is-decidable-neg (is-decidable-is-zero-ℕ n)

is-decidable-is-one-ℕ : (n : ℕ) → is-decidable (is-one-ℕ n)
is-decidable-is-one-ℕ n = has-decidable-equality-ℕ n one-ℕ

is-decidable-is-one-ℕ' : (n : ℕ) → is-decidable (is-one-ℕ' n)
is-decidable-is-one-ℕ' n = has-decidable-equality-ℕ one-ℕ n

is-decidable-is-not-one-ℕ :
  (x : ℕ) → is-decidable (is-not-one-ℕ x)
is-decidable-is-not-one-ℕ x =
  is-decidable-neg (is-decidable-is-one-ℕ x)

{- Proposition 8.1.8 -}

is-decidable-Eq-Fin : (k : ℕ) (x y : Fin k) → is-decidable (Eq-Fin k x y)
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inl y) = is-decidable-Eq-Fin k x y
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inr y) = inr id
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inl y) = inr id
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inr y) = inl star

has-decidable-equality-Fin :
  (k : ℕ) (x y : Fin k) → is-decidable (Id x y)
has-decidable-equality-Fin k x y =
  functor-coprod eq-Eq-Fin (functor-neg Eq-Fin-eq) (is-decidable-Eq-Fin k x y)

is-decidable-is-zero-Fin :
  {k : ℕ} (x : Fin k) → is-decidable (is-zero-Fin x)
is-decidable-is-zero-Fin {succ-ℕ k} x =
  has-decidable-equality-Fin (succ-ℕ k) x zero-Fin

is-decidable-is-neg-one-Fin :
  {k : ℕ} (x : Fin k) → is-decidable (is-neg-one-Fin x)
is-decidable-is-neg-one-Fin {succ-ℕ k} x =
  has-decidable-equality-Fin (succ-ℕ k) x neg-one-Fin

is-decidable-is-one-Fin :
  {k : ℕ} (x : Fin k) → is-decidable (is-one-Fin x)
is-decidable-is-one-Fin {succ-ℕ k} x =
  has-decidable-equality-Fin (succ-ℕ k) x one-Fin

{- Theorem 8.1.9 -}

is-decidable-div-ℕ : (d x : ℕ) → is-decidable (div-ℕ d x)
is-decidable-div-ℕ zero-ℕ x =
  is-decidable-iff
    ( div-eq-ℕ zero-ℕ x)
    ( inv ∘ (is-zero-div-zero-ℕ x))
    ( is-decidable-is-zero-ℕ' x)
is-decidable-div-ℕ (succ-ℕ d) x =
  is-decidable-iff
    ( div-succ-eq-zero-ℕ d x)
    ( eq-zero-div-succ-ℕ d x)
    ( is-decidable-is-zero-Fin (mod-succ-ℕ d x))

is-decidable-is-even-ℕ : (x : ℕ) → is-decidable (is-even-ℕ x)
is-decidable-is-even-ℕ x = is-decidable-div-ℕ two-ℕ x

is-decidable-is-odd-ℕ : (x : ℕ) → is-decidable (is-odd-ℕ x)
is-decidable-is-odd-ℕ x = is-decidable-neg (is-decidable-is-even-ℕ x)

--------------------------------------------------------------------------------

{- Section 8.2 Case analysis and definitions by with-abstraction -}

{- Definition 8.2.2 -}

collatz : ℕ → ℕ
collatz n with is-decidable-div-ℕ two-ℕ n
... | inl (pair y p) = y
... | inr f = succ-ℕ (mul-ℕ three-ℕ n)

{- Proposition 8.2.3 -}

is-decidable-function-type' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → (A → is-decidable B) → is-decidable (A → B)
is-decidable-function-type' (inl a) d with d a
... | inl b = inl (λ x → b)
... | inr nb = inr (λ f → nb (f a))
is-decidable-function-type' (inr na) d = inl (ex-falso ∘ na)

is-decidable-prod' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → (A → is-decidable B) → is-decidable (A × B)
is-decidable-prod' (inl a) d with d a
... | inl b = inl (pair a b)
... | inr nb = inr (nb ∘ pr2)
is-decidable-prod' (inr na) d = inr (na ∘ pr1)

{- Proposition 8.2.4 -}

-- There's a really cool application of with-abstraction here, on the recursive
-- call of the function itself!

is-decidable-Π-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) (m : ℕ) →
  is-decidable ((x : ℕ) → (leq-ℕ m x) → P x) → is-decidable ((x : ℕ) → P x)
is-decidable-Π-ℕ P d zero-ℕ (inr nH) = inr (λ f → nH (λ x y → f x))
is-decidable-Π-ℕ P d zero-ℕ (inl H) = inl (λ x → H x (leq-zero-ℕ x))
is-decidable-Π-ℕ P d (succ-ℕ m) (inr nH) = inr (λ f → nH (λ x y → f x))
is-decidable-Π-ℕ P d (succ-ℕ m) (inl H) with d zero-ℕ
... | inr np = inr (λ f → np (f zero-ℕ))
... | inl p with
  is-decidable-Π-ℕ
    ( λ x → P (succ-ℕ x))
    ( λ x → d (succ-ℕ x))
    ( m)
    ( inl (λ x → H (succ-ℕ x)))
... | inl g = inl (ind-ℕ p (λ x y → g x))
... | inr ng = inr (λ f → ng (λ x → f (succ-ℕ x)))

{- Corollary 8.2.5 -}

is-upper-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) → UU l
is-upper-bound-ℕ P n =
  (m : ℕ) → P m → leq-ℕ m n

is-decidable-bounded-Π-ℕ :
  {l1 l2 : Level} (P : ℕ → UU l1) (Q : ℕ → UU l2) (dP : is-decidable-fam P) →
  (dQ : is-decidable-fam Q) (m : ℕ) (H : is-upper-bound-ℕ P m) →
  is-decidable ((x : ℕ) → P x → Q x)
is-decidable-bounded-Π-ℕ P Q dP dQ m H =
  is-decidable-Π-ℕ
    ( λ x → P x → Q x)
    ( λ x → is-decidable-function-type (dP x) (dQ x))
    ( succ-ℕ m)
    ( inl (λ x l p → ex-falso (contradiction-leq-ℕ x m (H x p) l)))

--------------------------------------------------------------------------------

{- Section 8.3 The well-ordering principle of ℕ -}

{- Definition 8.3.2 -}

is-lower-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) → UU l
is-lower-bound-ℕ P n =
  (m : ℕ) → P m → leq-ℕ n m

{- Theorem 8.3.3 (The well-ordering principle of ℕ) -}

minimal-element-ℕ :
  {l : Level} (P : ℕ → UU l) → UU l
minimal-element-ℕ P = Σ ℕ (λ n → (P n) × (is-lower-bound-ℕ P n))

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

{- Also show that the well-ordering principle returns 0 if P 0 holds,
   independently of the input (pair n p) : Σ ℕ P. -}

is-zero-well-ordering-principle-succ-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P)
  (n : ℕ) (p : P (succ-ℕ n)) (d0 : is-decidable (P zero-ℕ)) →
  (x : minimal-element-ℕ (λ m → P (succ-ℕ m))) (p0 : P zero-ℕ) →
  Id (pr1 (well-ordering-principle-succ-ℕ P d n p d0 x)) zero-ℕ
is-zero-well-ordering-principle-succ-ℕ P d n p (inl p0) x q0 =
  refl
is-zero-well-ordering-principle-succ-ℕ P d n p (inr np0) x q0 =
  ex-falso (np0 q0)

is-zero-well-ordering-principle-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) →
  (x : Σ ℕ P) → P zero-ℕ → Id (number-well-ordering-principle-ℕ P d x) zero-ℕ
is-zero-well-ordering-principle-ℕ P d (pair zero-ℕ p) p0 = refl
is-zero-well-ordering-principle-ℕ P d (pair (succ-ℕ m) p) =
  is-zero-well-ordering-principle-succ-ℕ P d m p (d zero-ℕ)
    ( well-ordering-principle-ℕ
      ( λ z → P (succ-ℕ z))
      ( λ x → d (succ-ℕ x))
      ( pair m p))

--------------------------------------------------------------------------------

{- Section 8.4 The greatest common divisor -}

{- Definition 8.4.1 -}

is-common-divisor-ℕ : (a b x : ℕ) → UU lzero
is-common-divisor-ℕ a b x = (div-ℕ x a) × (div-ℕ x b)

is-decidable-is-common-divisor-ℕ :
  (a b : ℕ) → is-decidable-fam (is-common-divisor-ℕ a b)
is-decidable-is-common-divisor-ℕ a b x =
  is-decidable-prod
    ( is-decidable-div-ℕ x a)
    ( is-decidable-div-ℕ x b)

is-gcd-ℕ : (a b d : ℕ) → UU lzero
is-gcd-ℕ a b d =
  (x : ℕ) →
    ( (is-common-divisor-ℕ a b x) → (div-ℕ x d)) ×
    ( (div-ℕ x d) → (is-common-divisor-ℕ a b x))

{- Proposition 8.4.2 -}

is-common-divisor-is-gcd-ℕ :
  (a b d : ℕ) → is-gcd-ℕ a b d → is-common-divisor-ℕ a b d
is-common-divisor-is-gcd-ℕ a b d H = pr2 (H d) (refl-div-ℕ d)

uniqueness-is-gcd-ℕ :
  (a b d d' : ℕ) → is-gcd-ℕ a b d → is-gcd-ℕ a b d' → Id d d'
uniqueness-is-gcd-ℕ a b d d' H H' =
  anti-symmetric-div-ℕ d d'
    ( pr1 (H' d) (is-common-divisor-is-gcd-ℕ a b d H))
    ( pr1 (H d') (is-common-divisor-is-gcd-ℕ a b d' H'))

{- Definition 8.4.3 -}

is-multiple-of-gcd-ℕ : (a b n : ℕ) → UU lzero
is-multiple-of-gcd-ℕ a b n =
  is-nonzero-ℕ (add-ℕ a b) →
  (is-nonzero-ℕ n) × ((x : ℕ) → is-common-divisor-ℕ a b x → div-ℕ x n)

{- Corollary 8.4.6 -}

leq-div-succ-ℕ : (d x : ℕ) → div-ℕ d (succ-ℕ x) → leq-ℕ d (succ-ℕ x)
leq-div-succ-ℕ d x (pair (succ-ℕ k) p) =
  concatenate-leq-eq-ℕ d (leq-mul-ℕ' k d) p

leq-div-ℕ : (d x : ℕ) → is-nonzero-ℕ x → div-ℕ d x → leq-ℕ d x
leq-div-ℕ d x f H with is-successor-is-nonzero-ℕ x f
... | (pair y refl) = leq-div-succ-ℕ d y H

leq-sum-is-common-divisor-ℕ' :
  (a b d : ℕ) →
  is-successor-ℕ (add-ℕ a b) → is-common-divisor-ℕ a b d → leq-ℕ d (add-ℕ a b)
leq-sum-is-common-divisor-ℕ' a zero-ℕ d (pair k p) H =
  concatenate-leq-eq-ℕ d
    ( leq-div-succ-ℕ d k (tr (div-ℕ d) p (pr1 H)))
    ( inv p)
leq-sum-is-common-divisor-ℕ' a (succ-ℕ b) d (pair k p) H =
  leq-div-succ-ℕ d (add-ℕ a b) (div-add-ℕ d a (succ-ℕ b) (pr1 H) (pr2 H))

leq-sum-is-common-divisor-ℕ :
  (a b d : ℕ) →
  is-nonzero-ℕ (add-ℕ a b) → is-common-divisor-ℕ a b d → leq-ℕ d (add-ℕ a b)
leq-sum-is-common-divisor-ℕ a b d H =
  leq-sum-is-common-divisor-ℕ' a b d (is-successor-is-nonzero-ℕ (add-ℕ a b) H)

is-decidable-is-multiple-of-gcd-ℕ :
  (a b : ℕ) → is-decidable-fam (is-multiple-of-gcd-ℕ a b)
is-decidable-is-multiple-of-gcd-ℕ a b n =
  is-decidable-function-type'
    ( is-decidable-neg (is-decidable-is-zero-ℕ (add-ℕ a b)))
    ( λ np →
      is-decidable-prod
        ( is-decidable-neg (is-decidable-is-zero-ℕ n))
        ( is-decidable-bounded-Π-ℕ
          ( is-common-divisor-ℕ a b)
          ( λ x → div-ℕ x n)
          ( is-decidable-is-common-divisor-ℕ a b)
          ( λ x → is-decidable-div-ℕ x n)
          ( add-ℕ a b)
          ( λ x → leq-sum-is-common-divisor-ℕ a b x np)))

{- Lemma 8.4.7 -}

sum-is-multiple-of-gcd-ℕ : (a b : ℕ) → is-multiple-of-gcd-ℕ a b (add-ℕ a b)
sum-is-multiple-of-gcd-ℕ a b np =
  pair np (λ x H → div-add-ℕ x a b (pr1 H) (pr2 H))

{- Definition 8.4.8 The greatest common divisor -}

abstract
  GCD-ℕ : (a b : ℕ) → minimal-element-ℕ (is-multiple-of-gcd-ℕ a b)
  GCD-ℕ a b =
    well-ordering-principle-ℕ
      ( is-multiple-of-gcd-ℕ a b)
      ( is-decidable-is-multiple-of-gcd-ℕ a b)
      ( pair (add-ℕ a b) (sum-is-multiple-of-gcd-ℕ a b))

gcd-ℕ : ℕ → ℕ → ℕ
gcd-ℕ a b = pr1 (GCD-ℕ a b)

is-multiple-of-gcd-gcd-ℕ : (a b : ℕ) → is-multiple-of-gcd-ℕ a b (gcd-ℕ a b)
is-multiple-of-gcd-gcd-ℕ a b = pr1 (pr2 (GCD-ℕ a b))

is-lower-bound-gcd-ℕ :
  (a b : ℕ) → is-lower-bound-ℕ (is-multiple-of-gcd-ℕ a b) (gcd-ℕ a b)
is-lower-bound-gcd-ℕ a b = pr2 (pr2 (GCD-ℕ a b))

{- Theorem 8.4.9 -}

is-nonzero-gcd-ℕ :
  (a b : ℕ) → is-nonzero-ℕ (add-ℕ a b) → is-nonzero-ℕ (gcd-ℕ a b)
is-nonzero-gcd-ℕ a b ne = pr1 (is-multiple-of-gcd-gcd-ℕ a b ne)

is-successor-gcd-ℕ :
  (a b : ℕ) → is-nonzero-ℕ (add-ℕ a b) → is-successor-ℕ (gcd-ℕ a b)
is-successor-gcd-ℕ a b ne =
  is-successor-is-nonzero-ℕ (gcd-ℕ a b) (is-nonzero-gcd-ℕ a b ne)

is-zero-gcd-ℕ :
  (a b : ℕ) → is-zero-ℕ (add-ℕ a b) → is-zero-ℕ (gcd-ℕ a b)
is-zero-gcd-ℕ a b p =
  is-zero-leq-zero-ℕ
    ( gcd-ℕ a b)
    ( concatenate-leq-eq-ℕ
      ( gcd-ℕ a b)
      ( is-lower-bound-gcd-ℕ a b
        ( add-ℕ a b)
        ( sum-is-multiple-of-gcd-ℕ a b))
      ( p))

div-gcd-is-common-divisor-ℕ :
  (a b x : ℕ) → is-common-divisor-ℕ a b x → div-ℕ x (gcd-ℕ a b)
div-gcd-is-common-divisor-ℕ a b x H with
  is-decidable-is-zero-ℕ (add-ℕ a b)
... | inl p = tr (div-ℕ x) (inv (is-zero-gcd-ℕ a b p)) (div-zero-ℕ x)
... | inr np = pr2 (is-multiple-of-gcd-gcd-ℕ a b np) x H

is-zero-is-common-divisor-le-gcd-ℕ :
  (a b r : ℕ) → le-ℕ r (gcd-ℕ a b) →
  ((x : ℕ) → is-common-divisor-ℕ a b x → div-ℕ x r) → is-zero-ℕ r
is-zero-is-common-divisor-le-gcd-ℕ a b r l d with is-decidable-is-zero-ℕ r
... | inl H = H
... | inr x =
  ex-falso
    ( contradiction-le-ℕ r (gcd-ℕ a b) l
      ( is-lower-bound-gcd-ℕ a b r (λ np → pair x d)))

is-divisor-left-div-gcd-ℕ :
  (a b x : ℕ) → div-ℕ x (gcd-ℕ a b) → div-ℕ x a
is-divisor-left-div-gcd-ℕ a b x d with
  is-decidable-is-zero-ℕ (add-ℕ a b)
... | inl p =
  tr (div-ℕ x) (inv (is-zero-left-is-zero-add-ℕ a b p)) (div-zero-ℕ x)
... | inr np =
  transitive-div-ℕ x (gcd-ℕ a b) a d
    ( pair q
      ( ( α ∙ ( ap ( dist-ℕ a)
               ( is-zero-is-common-divisor-le-gcd-ℕ a b r B
                 ( λ x H →
                   div-right-summand-ℕ x (mul-ℕ q (gcd-ℕ a b)) r
                     ( div-mul-ℕ q x (gcd-ℕ a b)
                       ( div-gcd-is-common-divisor-ℕ a b x H))
                     ( tr (div-ℕ x) (inv β) (pr1 H)))))) ∙
        ( right-unit-law-dist-ℕ a)))
  where
  r = remainder-euclidean-division-ℕ (gcd-ℕ a b) a (is-nonzero-gcd-ℕ a b np)
  q = quotient-euclidean-division-ℕ (gcd-ℕ a b) a (is-nonzero-gcd-ℕ a b np)
  α = eq-quotient-euclidean-division-ℕ (gcd-ℕ a b) a (is-nonzero-gcd-ℕ a b np)
  B = strict-upper-bound-remainder-euclidean-division-ℕ (gcd-ℕ a b) a
       ( is-nonzero-gcd-ℕ a b np)
  β = eq-euclidean-division-ℕ (gcd-ℕ a b) a (is-nonzero-gcd-ℕ a b np)

is-divisor-right-div-gcd-ℕ :
  (a b x : ℕ) → div-ℕ x (gcd-ℕ a b) → div-ℕ x b
is-divisor-right-div-gcd-ℕ a b x d with
  is-decidable-is-zero-ℕ (add-ℕ a b)
... | inl p =
  tr (div-ℕ x) (inv (is-zero-right-is-zero-add-ℕ a b p)) (div-zero-ℕ x)
... | inr np =
  transitive-div-ℕ x (gcd-ℕ a b) b d
    ( pair q
      ( ( α ∙ ( ap ( dist-ℕ b)
               ( is-zero-is-common-divisor-le-gcd-ℕ a b r B
                 ( λ x H →
                   div-right-summand-ℕ x (mul-ℕ q (gcd-ℕ a b)) r
                     ( div-mul-ℕ q x (gcd-ℕ a b)
                       ( div-gcd-is-common-divisor-ℕ a b x H))
                     ( tr (div-ℕ x) (inv β) (pr2 H)))))) ∙
        ( right-unit-law-dist-ℕ b)))
  where
  r = remainder-euclidean-division-ℕ (gcd-ℕ a b) b (is-nonzero-gcd-ℕ a b np)
  q = quotient-euclidean-division-ℕ (gcd-ℕ a b) b (is-nonzero-gcd-ℕ a b np)
  α = eq-quotient-euclidean-division-ℕ (gcd-ℕ a b) b (is-nonzero-gcd-ℕ a b np)
  B = strict-upper-bound-remainder-euclidean-division-ℕ (gcd-ℕ a b) b
       ( is-nonzero-gcd-ℕ a b np)
  β = eq-euclidean-division-ℕ (gcd-ℕ a b) b (is-nonzero-gcd-ℕ a b np)

is-common-divisor-div-gcd-ℕ :
  (a b x : ℕ) → div-ℕ x (gcd-ℕ a b) → is-common-divisor-ℕ a b x
is-common-divisor-div-gcd-ℕ a b x d =
  pair (is-divisor-left-div-gcd-ℕ a b x d) (is-divisor-right-div-gcd-ℕ a b x d)

is-common-divisor-gcd-ℕ : (a b : ℕ) → is-common-divisor-ℕ a b (gcd-ℕ a b)
is-common-divisor-gcd-ℕ a b =
  is-common-divisor-div-gcd-ℕ a b (gcd-ℕ a b) (refl-div-ℕ (gcd-ℕ a b))

is-gcd-gcd-ℕ : (a b : ℕ) → is-gcd-ℕ a b (gcd-ℕ a b)
is-gcd-gcd-ℕ a b x =
  pair
    ( div-gcd-is-common-divisor-ℕ a b x)
    ( is-common-divisor-div-gcd-ℕ a b x)

--------------------------------------------------------------------------------

{- Section 8.5 The infinitude of primes -}

{- Definition 8.5.1 -}

is-proper-divisor-ℕ : ℕ → ℕ → UU lzero
is-proper-divisor-ℕ n d = ¬ (Id d n) × div-ℕ d n

is-one-is-proper-divisor-ℕ : ℕ → UU lzero
is-one-is-proper-divisor-ℕ n =
  (x : ℕ) → is-proper-divisor-ℕ n x → is-one-ℕ x

is-prime-ℕ : ℕ → UU lzero
is-prime-ℕ n = (x : ℕ) → (is-proper-divisor-ℕ n x ↔ is-one-ℕ x) 

{- Proposition 8.5.2 -}

is-prime-easy-ℕ : ℕ → UU lzero
is-prime-easy-ℕ n = (is-not-one-ℕ n) × (is-one-is-proper-divisor-ℕ n)

is-not-one-is-prime-ℕ : (n : ℕ) → is-prime-ℕ n → is-not-one-ℕ n
is-not-one-is-prime-ℕ n H p = pr1 (pr2 (H one-ℕ) refl) (inv p)

is-prime-easy-is-prime-ℕ : (n : ℕ) → is-prime-ℕ n → is-prime-easy-ℕ n
is-prime-easy-is-prime-ℕ n H =
  pair (is-not-one-is-prime-ℕ n H) (λ x → pr1 (H x))

is-prime-is-prime-easy-ℕ : (n : ℕ) → is-prime-easy-ℕ n → is-prime-ℕ n
is-prime-is-prime-easy-ℕ n H x =
  pair ( pr2 H x)
       ( λ p → tr ( is-proper-divisor-ℕ n)
                  ( inv p)
                  ( pair (λ q → pr1 H (inv q)) (div-one-ℕ n)))

is-decidable-is-proper-divisor-ℕ :
  (n d : ℕ) → is-decidable (is-proper-divisor-ℕ n d)
is-decidable-is-proper-divisor-ℕ n d =
  is-decidable-prod
    ( is-decidable-neg (has-decidable-equality-ℕ d n))
    ( is-decidable-div-ℕ d n)

is-proper-divisor-zero-succ-ℕ : (n : ℕ) → is-proper-divisor-ℕ zero-ℕ (succ-ℕ n)
is-proper-divisor-zero-succ-ℕ n =
  pair (λ p → Peano-8 n p) (div-zero-ℕ (succ-ℕ n))

is-decidable-is-prime-easy-ℕ : (n : ℕ) → is-decidable (is-prime-easy-ℕ n)
is-decidable-is-prime-easy-ℕ zero-ℕ =
  inr
    ( λ H →
      is-not-one-two-ℕ (pr2 H two-ℕ (is-proper-divisor-zero-succ-ℕ one-ℕ)))
is-decidable-is-prime-easy-ℕ (succ-ℕ n) =
  is-decidable-prod
    ( is-decidable-neg (is-decidable-is-one-ℕ (succ-ℕ n)))
    ( is-decidable-bounded-Π-ℕ
      ( is-proper-divisor-ℕ (succ-ℕ n))
      ( is-one-ℕ)
      ( is-decidable-is-proper-divisor-ℕ (succ-ℕ n))
      ( is-decidable-is-one-ℕ)
      ( succ-ℕ n)
      ( λ x H → leq-div-succ-ℕ x n (pr2 H)))

is-decidable-is-prime-ℕ : (n : ℕ) → is-decidable (is-prime-ℕ n)
is-decidable-is-prime-ℕ n =
  is-decidable-iff
    ( is-prime-is-prime-easy-ℕ n)
    ( is-prime-easy-is-prime-ℕ n)
    ( is-decidable-is-prime-easy-ℕ n)

is-one-is-proper-divisor-two-ℕ : is-one-is-proper-divisor-ℕ two-ℕ
is-one-is-proper-divisor-two-ℕ zero-ℕ (pair f (pair k p)) =
  ex-falso (f (inv (right-zero-law-mul-ℕ k) ∙ p))
is-one-is-proper-divisor-two-ℕ (succ-ℕ zero-ℕ) (pair f H) = refl
is-one-is-proper-divisor-two-ℕ (succ-ℕ (succ-ℕ zero-ℕ)) (pair f H) =
  ex-falso (f refl)
is-one-is-proper-divisor-two-ℕ (succ-ℕ (succ-ℕ (succ-ℕ x))) (pair f H) =
  ex-falso (leq-div-succ-ℕ (succ-ℕ (succ-ℕ (succ-ℕ x))) one-ℕ H)

is-prime-easy-two-ℕ : is-prime-easy-ℕ two-ℕ
is-prime-easy-two-ℕ = pair Eq-ℕ-eq is-one-is-proper-divisor-two-ℕ

is-prime-two-ℕ : is-prime-ℕ two-ℕ
is-prime-two-ℕ =
  is-prime-is-prime-easy-ℕ two-ℕ is-prime-easy-two-ℕ

{- Definition 8.5.3 -}

is-one-is-divisor-below-ℕ : ℕ → ℕ → UU lzero
is-one-is-divisor-below-ℕ n a =
  (x : ℕ) → leq-ℕ x n → div-ℕ x a → is-one-ℕ x

in-sieve-of-eratosthenes-ℕ : ℕ → ℕ → UU lzero
in-sieve-of-eratosthenes-ℕ n a =
  (le-ℕ n a) × (is-one-is-divisor-below-ℕ n a)

le-in-sieve-of-eratosthenes-ℕ :
  (n a : ℕ) → in-sieve-of-eratosthenes-ℕ n a → le-ℕ n a
le-in-sieve-of-eratosthenes-ℕ n a = pr1

{- Lemma 8.5.4 -}

is-decidable-in-sieve-of-eratosthenes-ℕ :
  (n a : ℕ) → is-decidable (in-sieve-of-eratosthenes-ℕ n a)
is-decidable-in-sieve-of-eratosthenes-ℕ n a =
  is-decidable-prod
    ( is-decidable-le-ℕ n a)
    ( is-decidable-bounded-Π-ℕ
      ( λ x → leq-ℕ x n)
      ( λ x → div-ℕ x a → is-one-ℕ x)
      ( λ x → is-decidable-leq-ℕ x n)
      ( λ x →
        is-decidable-function-type
          ( is-decidable-div-ℕ x a)
          ( is-decidable-is-one-ℕ x))
      ( n)
      ( λ x → id))

{- Lemma 8.5.5 -}

is-nonzero-factorial-ℕ :
  (x : ℕ) → is-nonzero-ℕ (factorial-ℕ x)
is-nonzero-factorial-ℕ zero-ℕ = Eq-ℕ-eq
is-nonzero-factorial-ℕ (succ-ℕ x) =
  is-nonzero-mul-ℕ
    ( factorial-ℕ x)
    ( succ-ℕ x)
    ( is-nonzero-factorial-ℕ x)
    ( Peano-8 x)

leq-factorial-ℕ :
  (n : ℕ) → leq-ℕ n (factorial-ℕ n)
leq-factorial-ℕ zero-ℕ = leq-zero-ℕ one-ℕ
leq-factorial-ℕ (succ-ℕ n) =
  leq-mul-is-nonzero-ℕ'
    ( factorial-ℕ n)
    ( succ-ℕ n)
    ( is-nonzero-factorial-ℕ n) 

in-sieve-of-eratosthenes-succ-factorial-ℕ :
  (n : ℕ) → in-sieve-of-eratosthenes-ℕ n (succ-ℕ (factorial-ℕ n))
in-sieve-of-eratosthenes-succ-factorial-ℕ zero-ℕ =
  pair
    ( star)
    ( λ x l d →
      ex-falso
        ( Eq-ℕ-eq
          ( is-zero-is-zero-div-ℕ x two-ℕ d (is-zero-leq-zero-ℕ x l))))
in-sieve-of-eratosthenes-succ-factorial-ℕ (succ-ℕ n) =
  pair
    ( concatenate-leq-le-ℕ
      { succ-ℕ n}
      { factorial-ℕ (succ-ℕ n)}
      { succ-ℕ (factorial-ℕ (succ-ℕ n))} 
      ( leq-factorial-ℕ (succ-ℕ n))
      ( le-succ-ℕ {factorial-ℕ (succ-ℕ n)}))
    ( α)
  where
  α : (x : ℕ) → leq-ℕ x (succ-ℕ n) →
        div-ℕ x (succ-ℕ (factorial-ℕ (succ-ℕ n))) → is-one-ℕ x
  α x l (pair y p) with is-decidable-is-zero-ℕ x
  ... | inl refl =
    ex-falso
      ( Peano-8
        ( factorial-ℕ (succ-ℕ n))
        ( inv p ∙ (right-zero-law-mul-ℕ y)))
  ... | inr f =
    is-one-div-ℕ x
      ( factorial-ℕ (succ-ℕ n))
      ( div-factorial-is-nonzero-ℕ (succ-ℕ n) x l f)
      ( pair y p)

{- Theorem 8.5.6 The infinitude of primes -}

minimal-element-in-sieve-of-eratosthenes-ℕ :
  (n : ℕ) → minimal-element-ℕ (in-sieve-of-eratosthenes-ℕ n)
minimal-element-in-sieve-of-eratosthenes-ℕ n =
  well-ordering-principle-ℕ
    ( in-sieve-of-eratosthenes-ℕ n)
    ( is-decidable-in-sieve-of-eratosthenes-ℕ n)
    ( pair
      ( succ-ℕ (factorial-ℕ n))
      ( in-sieve-of-eratosthenes-succ-factorial-ℕ n))

larger-prime-ℕ : ℕ → ℕ
larger-prime-ℕ n = pr1 (minimal-element-in-sieve-of-eratosthenes-ℕ n)

in-sieve-of-eratosthenes-larger-prime-ℕ :
  (n : ℕ) → in-sieve-of-eratosthenes-ℕ n (larger-prime-ℕ n)
in-sieve-of-eratosthenes-larger-prime-ℕ n =
  pr1 (pr2 (minimal-element-in-sieve-of-eratosthenes-ℕ n))

is-one-is-divisor-below-larger-prime-ℕ :
  (n : ℕ) → is-one-is-divisor-below-ℕ n (larger-prime-ℕ n)
is-one-is-divisor-below-larger-prime-ℕ n =
  pr2 (in-sieve-of-eratosthenes-larger-prime-ℕ n)

le-larger-prime-ℕ : (n : ℕ) → le-ℕ n (larger-prime-ℕ n)
le-larger-prime-ℕ n = pr1 (in-sieve-of-eratosthenes-larger-prime-ℕ n)

is-nonzero-larger-prime-ℕ : (n : ℕ) → is-nonzero-ℕ (larger-prime-ℕ n)
is-nonzero-larger-prime-ℕ n =
  is-nonzero-le-ℕ n (larger-prime-ℕ n) (le-larger-prime-ℕ n)

is-lower-bound-larger-prime-ℕ :
  (n : ℕ) → is-lower-bound-ℕ (in-sieve-of-eratosthenes-ℕ n) (larger-prime-ℕ n)
is-lower-bound-larger-prime-ℕ n =
  pr2 (pr2 (minimal-element-in-sieve-of-eratosthenes-ℕ n))

is-not-one-larger-prime-ℕ :
  (n : ℕ) → is-nonzero-ℕ n → is-not-one-ℕ (larger-prime-ℕ n)
is-not-one-larger-prime-ℕ n H p with is-successor-is-nonzero-ℕ n H
... | pair k refl =
  neq-le-ℕ {one-ℕ} {larger-prime-ℕ n}
    ( concatenate-leq-le-ℕ {one-ℕ} {succ-ℕ k} {larger-prime-ℕ n} star
      ( le-larger-prime-ℕ (succ-ℕ k)))
    ( inv p)

neg-left-factor-neg-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → ¬ (A × B) → B → ¬ A
neg-left-factor-neg-prod f b a = f (pair a b)

neg-right-factor-neg-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → ¬ (A × B) → A → ¬ B
neg-right-factor-neg-prod f a b = f (pair a b)

le-is-proper-divisor-ℕ :
  (x y : ℕ) → is-nonzero-ℕ y → is-proper-divisor-ℕ y x → le-ℕ x y
le-is-proper-divisor-ℕ x y H K =
  le-leq-neq-ℕ (leq-div-ℕ x y H (pr2 K)) (pr1 K)

not-in-sieve-of-eratosthenes-is-proper-divisor-larger-prime-ℕ :
  (n x : ℕ) → is-proper-divisor-ℕ (larger-prime-ℕ n) x →
  ¬ (in-sieve-of-eratosthenes-ℕ n x)
not-in-sieve-of-eratosthenes-is-proper-divisor-larger-prime-ℕ n x H K =
  ex-falso
    ( contradiction-le-ℕ x (larger-prime-ℕ n)
      ( le-is-proper-divisor-ℕ x (larger-prime-ℕ n)
        ( is-nonzero-larger-prime-ℕ n)
        ( H))
      ( is-lower-bound-larger-prime-ℕ n x K))

is-one-is-proper-divisor-larger-prime-ℕ :
  (n : ℕ) → is-nonzero-ℕ n → is-one-is-proper-divisor-ℕ (larger-prime-ℕ n)
is-one-is-proper-divisor-larger-prime-ℕ n H x (pair f K) =
  is-one-is-divisor-below-larger-prime-ℕ n x
    ( leq-not-le-ℕ n x
      ( neg-left-factor-neg-prod
        ( not-in-sieve-of-eratosthenes-is-proper-divisor-larger-prime-ℕ n x
          ( pair f K))
        ( λ y l d →
          is-one-is-divisor-below-larger-prime-ℕ n y l
            ( transitive-div-ℕ y x (larger-prime-ℕ n) d K))))
    ( K)

is-prime-larger-prime-ℕ :
  (n : ℕ) → is-nonzero-ℕ n → is-prime-ℕ (larger-prime-ℕ n)
is-prime-larger-prime-ℕ n H =
  is-prime-is-prime-easy-ℕ
    ( larger-prime-ℕ n)
    ( pair
      ( is-not-one-larger-prime-ℕ n H)
      ( is-one-is-proper-divisor-larger-prime-ℕ n H))

infinitude-of-primes-ℕ :
  (n : ℕ) → Σ ℕ (λ p → is-prime-ℕ p × le-ℕ n p)
infinitude-of-primes-ℕ n with is-decidable-is-zero-ℕ n
... | inl refl = pair two-ℕ (pair is-prime-two-ℕ star)
... | inr H =
  pair
    ( larger-prime-ℕ n)
    ( pair
      ( is-prime-larger-prime-ℕ n H)
      ( le-larger-prime-ℕ n))

--------------------------------------------------------------------------------

{- Section 8.6 Boolean reflection -}

{- Definition 8.6.1 -}

booleanization : {l : Level} {A : UU l} → is-decidable A → bool
booleanization (inl a) = true
booleanization (inr f) = false

{- Proposition 8.6.2 -}

inv-boolean-reflection :
  {l : Level} {A : UU l} (d : is-decidable A) → A → Id (booleanization d) true
inv-boolean-reflection (inl a) x = refl
inv-boolean-reflection (inr f) x = ex-falso (f x)

boolean-reflection :
  {l : Level} {A : UU l} (d : is-decidable A) → Id (booleanization d) true → A
boolean-reflection (inl a) p = a
boolean-reflection (inr f) p = ex-falso (Eq-eq-𝟚 p)

{-
four-hundred-and-nine-ℕ : ℕ
four-hundred-and-nine-ℕ = add-ℕ (mul-ℕ twenty-ℕ twenty-ℕ) nine-ℕ

is-prime-four-hundred-and-nine-ℕ : is-prime-ℕ four-hundred-and-nine-ℕ
is-prime-four-hundred-and-nine-ℕ =
  boolean-reflection
    ( is-decidable-is-prime-ℕ four-hundred-and-nine-ℕ)
    ( refl)
-}

--------------------------------------------------------------------------------

{- Exercises -}

--------------------------------------------------------------------------------

{- Exercise 8.1 -}

{- The Goldbach conjecture asserts that every even number above 2 is the sum
   of two primes. -}

Goldbach-conjecture : UU lzero
Goldbach-conjecture =
  ( n : ℕ) → (le-ℕ two-ℕ n) → (is-even-ℕ n) →
    Σ ℕ (λ p → (is-prime-ℕ p) × (Σ ℕ (λ q → (is-prime-ℕ q) × Id (add-ℕ p q) n)))

is-twin-prime-ℕ : ℕ → UU lzero
is-twin-prime-ℕ n = (is-prime-ℕ n) × (is-prime-ℕ (succ-ℕ (succ-ℕ n)))

{- The twin prime conjecture asserts that there are infinitely many twin 
   primes. We assert that there are infinitely twin primes by asserting that 
   for every n : ℕ there is a twin prime that is larger than n. -}
   
Twin-prime-conjecture : UU lzero
Twin-prime-conjecture =
  (n : ℕ) → Σ ℕ (λ p → (is-twin-prime-ℕ p) × (leq-ℕ n p))

iterate-collatz : ℕ → ℕ → ℕ
iterate-collatz zero-ℕ n = n
iterate-collatz (succ-ℕ k) n =
  collatz (iterate-collatz k n)

Collatz-conjecture : UU lzero
Collatz-conjecture =
  (n : ℕ) →
  is-nonzero-ℕ n → Σ ℕ (λ k → Id (iterate-collatz k n) one-ℕ)

--------------------------------------------------------------------------------

{- Exercise 8.2 -}

-- Exercise 8.2 (a)

prime-ℕ : ℕ → ℕ
prime-ℕ zero-ℕ = two-ℕ
prime-ℕ (succ-ℕ n) = pr1 (infinitude-of-primes-ℕ (prime-ℕ n))

-- Exercise 8.2 (b)

prime-counting-ℕ : ℕ → ℕ
prime-counting-ℕ zero-ℕ = zero-ℕ
prime-counting-ℕ (succ-ℕ n) with is-decidable-is-prime-ℕ (succ-ℕ n)
... | inl x = succ-ℕ (prime-counting-ℕ n)
... | inr x = prime-counting-ℕ n

--------------------------------------------------------------------------------

{- Exercise 8.3 -}

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

--------------------------------------------------------------------------------

{- Exercise 8.4 -}

-- We define observational equality of coproducts.

Eq-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  coprod A B → coprod A B → UU (l1 ⊔ l2)
Eq-coprod {l1} {l2} A B (inl x) (inl y) = raise (l1 ⊔ l2) (Id x y)
Eq-coprod {l1} {l2} A B (inl x) (inr y) = raise-empty (l1 ⊔ l2)
Eq-coprod {l1} {l2} A B (inr x) (inl y) = raise-empty (l1 ⊔ l2)
Eq-coprod {l1} {l2} A B (inr x) (inr y) = raise (l1 ⊔ l2) (Id x y)

-- Exercise 8.4 (a)

reflexive-Eq-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  (t : coprod A B) → Eq-coprod A B t t
reflexive-Eq-coprod {l1} {l2} A B (inl x) = map-raise refl
reflexive-Eq-coprod {l1} {l2} A B (inr x) = map-raise refl

Eq-coprod-eq :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  (s t : coprod A B) → Id s t → Eq-coprod A B s t
Eq-coprod-eq A B s .s refl = reflexive-Eq-coprod A B s

eq-Eq-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (s t : coprod A B) →
  Eq-coprod A B s t → Id s t
eq-Eq-coprod A B (inl x) (inl x') = ap inl ∘ inv-map-raise
eq-Eq-coprod A B (inl x) (inr y') = ex-falso ∘ inv-map-raise
eq-Eq-coprod A B (inr y) (inl x') = ex-falso ∘ inv-map-raise
eq-Eq-coprod A B (inr y) (inr y') = ap inr ∘ inv-map-raise

-- Exercise 8.4 (b)

has-decidable-equality-coprod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-equality A → has-decidable-equality B →
  has-decidable-equality (coprod A B)
has-decidable-equality-coprod {l1} {l2} {A} {B} d e (inl x) (inl x') =
  is-decidable-iff
    ( eq-Eq-coprod A B (inl x) (inl x') ∘ map-raise)
    ( inv-map-raise ∘ Eq-coprod-eq A B (inl x) (inl x'))
    ( d x x')
has-decidable-equality-coprod {l1} {l2} {A} {B} d e (inl x) (inr y') =
  inr (inv-map-raise ∘ (Eq-coprod-eq A B (inl x) (inr y')))
has-decidable-equality-coprod {l1} {l2} {A} {B} d e (inr y) (inl x') =
  inr (inv-map-raise ∘ (Eq-coprod-eq A B (inr y) (inl x')))
has-decidable-equality-coprod {l1} {l2} {A} {B} d e (inr y) (inr y') =
  is-decidable-iff
    ( eq-Eq-coprod A B (inr y) (inr y') ∘ map-raise)
    ( inv-map-raise ∘ Eq-coprod-eq A B (inr y) (inr y'))
    ( e y y')

has-decidable-equality-left-summand :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-equality (coprod A B) → has-decidable-equality A
has-decidable-equality-left-summand {l1} {l2} {A} {B} d x y =
  is-decidable-iff
    ( inv-map-raise ∘ Eq-coprod-eq A B (inl x) (inl y))
    ( eq-Eq-coprod A B (inl x) (inl y) ∘ map-raise)
    ( d (inl x) (inl y))

has-decidable-equality-right-summand :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-equality (coprod A B) → has-decidable-equality B
has-decidable-equality-right-summand {l1} {l2} {A} {B} d x y =
  is-decidable-iff
    ( inv-map-raise ∘ Eq-coprod-eq A B (inr x) (inr y))
    ( eq-Eq-coprod A B (inr x) (inr y) ∘ map-raise)
    ( d (inr x) (inr y))

--------------------------------------------------------------------------------

{- Exercise 8.5 -}

-- Exercies 8.5 (a)

-- Exercise 8.5 (c)

Eq-list : {l1 : Level} {A : UU l1} → list A → list A → UU l1
Eq-list {l1} nil nil = raise-unit l1
Eq-list {l1} nil (cons x l') = raise-empty l1
Eq-list {l1} (cons x l) nil = raise-empty l1
Eq-list {l1} (cons x l) (cons x' l') = (Id x x') × Eq-list l l'

reflexive-Eq-list : {l1 : Level} {A : UU l1} (l : list A) → Eq-list l l
reflexive-Eq-list nil = raise-star
reflexive-Eq-list (cons x l) = pair refl (reflexive-Eq-list l)

Eq-list-eq :
  {l1 : Level} {A : UU l1} (l l' : list A) → Id l l' → Eq-list l l'
Eq-list-eq l .l refl = reflexive-Eq-list l

eq-Eq-list :
  {l1 : Level} {A : UU l1} (l l' : list A) → Eq-list l l' → Id l l'
eq-Eq-list nil nil (map-raise star) = refl
eq-Eq-list nil (cons x l') (map-raise f) = ex-falso f
eq-Eq-list (cons x l) nil (map-raise f) = ex-falso f
eq-Eq-list (cons x l) (cons .x l') (pair refl e) =
  ap (cons x) (eq-Eq-list l l' e)

has-decidable-equality-list :
  {l1 : Level} {A : UU l1} →
  has-decidable-equality A → has-decidable-equality (list A)
has-decidable-equality-list d nil nil = inl refl
has-decidable-equality-list d nil (cons x l) =
  inr (inv-map-raise ∘ Eq-list-eq nil (cons x l))
has-decidable-equality-list d (cons x l) nil =
  inr (inv-map-raise ∘ Eq-list-eq (cons x l) nil)
has-decidable-equality-list d (cons x l) (cons x' l') =
  is-decidable-iff
    ( eq-Eq-list (cons x l) (cons x' l'))
    ( Eq-list-eq (cons x l) (cons x' l'))
    ( is-decidable-prod
      ( d x x')
      ( is-decidable-iff
        ( Eq-list-eq l l')
        ( eq-Eq-list l l')
        ( has-decidable-equality-list d l l')))

is-decidable-left-factor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable (A × B) → B → is-decidable A
is-decidable-left-factor (inl (pair x y)) b = inl x
is-decidable-left-factor (inr f) b = inr (λ a → f (pair a b))

is-decidable-right-factor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable (A × B) → A → is-decidable B
is-decidable-right-factor (inl (pair x y)) a = inl y
is-decidable-right-factor (inr f) a = inr (λ b → f (pair a b))

has-decidable-equality-has-decidable-equality-list :
  {l1 : Level} {A : UU l1} →
  has-decidable-equality (list A) → has-decidable-equality A
has-decidable-equality-has-decidable-equality-list d x y =
  is-decidable-left-factor
    ( is-decidable-iff
      ( Eq-list-eq (cons x nil) (cons y nil))
      ( eq-Eq-list (cons x nil) (cons y nil))
      ( d (cons x nil) (cons y nil)))
    ( raise-star)

--------------------------------------------------------------------------------
