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

is-decidable-is-zero-ℕ : (n : ℕ) → is-decidable (is-zero-ℕ n)
is-decidable-is-zero-ℕ n = has-decidable-equality-ℕ n zero-ℕ

is-decidable-is-zero-ℕ' : (n : ℕ) → is-decidable (is-zero-ℕ' n)
is-decidable-is-zero-ℕ' n = has-decidable-equality-ℕ zero-ℕ n

is-decidable-is-one-ℕ : (n : ℕ) → is-decidable (is-one-ℕ n)
is-decidable-is-one-ℕ n = has-decidable-equality-ℕ n one-ℕ

is-decidable-is-one-ℕ' : (n : ℕ) → is-decidable (is-one-ℕ' n)
is-decidable-is-one-ℕ' n = has-decidable-equality-ℕ one-ℕ n

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
    ( inv ∘ (is-zero-div-zero-ℕ x))
    ( is-decidable-is-zero-ℕ' x)
is-decidable-div-ℕ (succ-ℕ d) x =
  is-decidable-iff
    ( div-succ-eq-zero-ℕ d x)
    ( eq-zero-div-succ-ℕ d x)
    ( has-decidable-equality-Fin (succ-ℕ d) (mod-succ-ℕ d x) zero-Fin)

--------------------------------------------------------------------------------

{- Section 8.2 Case analysis and definitions by with-abstraction -}

{- Definition 8.2.2 -}

collatz-function : ℕ → ℕ
collatz-function n with is-decidable-div-ℕ two-ℕ n
... | inl (pair y p) = y
... | inr f = succ-ℕ (mul-ℕ three-ℕ n)

{- Remark 8.2.4 -}

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

{- Proposition 8.2.5 -}

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

{- Proposition 8.2.6 -}

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

{- Corollary 8.2.7 -}

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
  (x : Σ ℕ P) → P zero-ℕ → Id (pr1 (well-ordering-principle-ℕ P d x)) zero-ℕ
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

leq-div-ℕ : (d x : ℕ) → div-ℕ d (succ-ℕ x) → leq-ℕ d (succ-ℕ x)
leq-div-ℕ d x (pair (succ-ℕ k) p) =
  concatenate-leq-eq-ℕ d (leq-mul-ℕ' k d) p

leq-sum-is-common-divisor-ℕ' :
  (a b d : ℕ) →
  is-successor-ℕ (add-ℕ a b) → is-common-divisor-ℕ a b d → leq-ℕ d (add-ℕ a b)
leq-sum-is-common-divisor-ℕ' a zero-ℕ d (pair k p) H =
  concatenate-leq-eq-ℕ d
    ( leq-div-ℕ d k (tr (div-ℕ d) p (pr1 H)))
    ( inv p)
leq-sum-is-common-divisor-ℕ' a (succ-ℕ b) d (pair k p) H =
  leq-div-ℕ d (add-ℕ a b) (div-add-ℕ d a (succ-ℕ b) (pr1 H) (pr2 H))

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
  inv
    ( eq-leq-zero-ℕ
      ( gcd-ℕ a b)
      ( concatenate-leq-eq-ℕ
        ( gcd-ℕ a b)
        ( is-lower-bound-gcd-ℕ a b
          ( add-ℕ a b)
          ( sum-is-multiple-of-gcd-ℕ a b))
        ( p)))

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

is-prime : ℕ → UU lzero
is-prime n =
  ¬ (Id n one-ℕ) × ((x : ℕ) → (div-ℕ x n) → coprod (Id x one-ℕ) (Id x n))

is-prime-two-ℕ' :
  (x : ℕ) → div-ℕ x two-ℕ → coprod (Id x one-ℕ) (Id x two-ℕ)
is-prime-two-ℕ' zero-ℕ H =
  ex-falso (Eq-ℕ-eq (is-zero-div-zero-ℕ two-ℕ H))
is-prime-two-ℕ' (succ-ℕ zero-ℕ) H = inl refl
is-prime-two-ℕ' (succ-ℕ (succ-ℕ zero-ℕ)) H = inr refl
is-prime-two-ℕ' (succ-ℕ (succ-ℕ (succ-ℕ x))) H =
  ex-falso (leq-div-ℕ (succ-ℕ (succ-ℕ (succ-ℕ x))) one-ℕ H)

is-prime-two-ℕ : is-prime two-ℕ
is-prime-two-ℕ = pair Eq-ℕ-eq is-prime-two-ℕ'

{- Proposition 8.5.2 -}

is-decidable-is-prime : (n : ℕ) → is-decidable (is-prime n)
is-decidable-is-prime zero-ℕ =
  inr
    ( λ d →
      Peano-8 one-ℕ
        ( inv
          ( coprod-elim-right
            ( Id two-ℕ one-ℕ)
            ( Id two-ℕ zero-ℕ)
            ( Eq-ℕ-eq)
            ( pr2 d two-ℕ (div-zero-ℕ two-ℕ)))))
is-decidable-is-prime (succ-ℕ n) = 
  is-decidable-prod
    ( is-decidable-neg (has-decidable-equality-ℕ (succ-ℕ n) one-ℕ))
    ( is-decidable-bounded-Π-ℕ
      ( λ x → div-ℕ x (succ-ℕ n))
      ( λ x → coprod (Id x one-ℕ) (Id x (succ-ℕ n)))
      ( λ x → is-decidable-div-ℕ x (succ-ℕ n))
      ( λ x → is-decidable-coprod
                ( has-decidable-equality-ℕ x one-ℕ)
                ( has-decidable-equality-ℕ x (succ-ℕ n)))
      ( succ-ℕ n)
      ( λ x → leq-div-ℕ x n))

{- Definition 8.5.3 -}

is-relatively-prime-ℕ : ℕ → ℕ → UU lzero
is-relatively-prime-ℕ a b = is-one-ℕ (gcd-ℕ a b)

is-gcd-succ-one-ℕ : (n : ℕ) → is-gcd-ℕ n (succ-ℕ n) one-ℕ
is-gcd-succ-one-ℕ n x =
  pair
    ( λ H → div-right-summand-ℕ x n one-ℕ (pr1 H) (pr2 H))
    ( λ H → pair
              ( transitive-div-ℕ x one-ℕ n H (div-one-ℕ n))
              ( transitive-div-ℕ x one-ℕ (succ-ℕ n) H (div-one-ℕ (succ-ℕ n))))

succ-is-relatively-prime-ℕ : (n : ℕ) → is-relatively-prime-ℕ n (succ-ℕ n)
succ-is-relatively-prime-ℕ n =
  uniqueness-is-gcd-ℕ n (succ-ℕ n) (gcd-ℕ n (succ-ℕ n)) one-ℕ
    ( is-gcd-gcd-ℕ n (succ-ℕ n))
    ( is-gcd-succ-one-ℕ n)

is-relatively-prime-div-ℕ :
  (d x y : ℕ) → div-ℕ d x →
  is-relatively-prime-ℕ x y → is-relatively-prime-ℕ d y
is-relatively-prime-div-ℕ d x y H K =
  is-one-div-one-ℕ
    ( gcd-ℕ d y)
    ( tr (div-ℕ (gcd-ℕ d y)) K
      ( div-gcd-is-common-divisor-ℕ x y (gcd-ℕ d y)
        ( pair
          ( transitive-div-ℕ (gcd-ℕ d y) d x
            ( pr1 (is-common-divisor-gcd-ℕ d y))
            ( H))
          ( pr2 (is-common-divisor-gcd-ℕ d y)))))

{-
infinitude-of-primes :
  (n : ℕ) → Σ ℕ (λ x → (is-prime x) × (leq-ℕ n x))
infinitude-of-primes n = {!!}
-}
