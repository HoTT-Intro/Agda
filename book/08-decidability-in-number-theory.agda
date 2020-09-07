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

{- Definition 8.2.1 -}

is-decidable-fam :
  {l1 l2 : Level} {A : UU l1} (P : A → UU l2) → UU (l1 ⊔ l2)
is-decidable-fam {A = A} P = (x : A) → is-decidable (P x)

{- Definition 8.2.2 -}

is-lower-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) → UU l
is-lower-bound-ℕ P n =
  (m : ℕ) → P m → (leq-ℕ n m)

{- Theorem 8.2.3 (The well-ordering principle of ℕ) -}

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

--------------------------------------------------------------------------------

{- Section 8.3 The greatest common divisor -}

{- Definition 8.3.1 -}

is-common-divisor-ℕ : (a b x : ℕ) → UU lzero
is-common-divisor-ℕ a b x = (div-ℕ x a) × (div-ℕ x b)

is-gcd-ℕ : (a b d : ℕ) → UU lzero
is-gcd-ℕ a b d =
  (x : ℕ) →
    ( (is-common-divisor-ℕ a b x) → (div-ℕ x d)) ×
    ( (div-ℕ x d) → (is-common-divisor-ℕ a b x))

{- Proposition 8.3.2 -}

is-common-divisor-is-gcd-ℕ :
  (a b d : ℕ) → is-gcd-ℕ a b d → is-common-divisor-ℕ a b d
is-common-divisor-is-gcd-ℕ a b d H = pr2 (H d) (refl-div-ℕ d)

uniqueness-is-gcd-ℕ :
  (a b d d' : ℕ) → is-gcd-ℕ a b d → is-gcd-ℕ a b d' → Id d d'
uniqueness-is-gcd-ℕ a b d d' H H' =
  anti-symmetric-div-ℕ d d'
    ( pr1 (H' d) (is-common-divisor-is-gcd-ℕ a b d H))
    ( pr1 (H d') (is-common-divisor-is-gcd-ℕ a b d' H'))

{- Definition 8.3.3 -}

is-multiple-of-gcd-ℕ : (a b n : ℕ) → UU lzero
is-multiple-of-gcd-ℕ a b zero-ℕ = (Id a zero-ℕ) × (Id b zero-ℕ)
is-multiple-of-gcd-ℕ a b (succ-ℕ n) =
  (x : ℕ) → is-common-divisor-ℕ a b x → div-ℕ x (succ-ℕ n)

{- Lemma 8.3.4 -}

is-decidable-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (A → B)
is-decidable-function-type dec-A (inl b) = inl (λ x → b)
is-decidable-function-type (inl a) (inr nb) = inr (λ f → nb (f a))
is-decidable-function-type (inr na) (inr nb) = inl (ex-falso ∘ na)

{- Lemma 8.3.5 -}

-- There's a really cool application of with-abstraction here, on the recursive
-- call of the function itself!

is-decidable-Π-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) →
  (m : ℕ) → ((x : ℕ) → (leq-ℕ m x) → P x) → is-decidable ((x : ℕ) → P x)
is-decidable-Π-ℕ P d zero-ℕ H = inl (λ x → H x (leq-zero-ℕ x))
is-decidable-Π-ℕ P d (succ-ℕ m) H with d zero-ℕ
... | inr np = inr (λ f → np (f zero-ℕ))
... | inl p with
  is-decidable-Π-ℕ
    ( λ x → P (succ-ℕ x))
    ( λ x → d (succ-ℕ x))
    ( m)
    ( λ x l → H (succ-ℕ x) l)
... | inl g = inl (ind-ℕ p (λ x y → g x))
... | inr ng = inr (λ f → ng (λ x → f (succ-ℕ x)))

{- Corollary 8.3.6 -}

is-decidable-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (A × B)
is-decidable-prod (inl a) (inl b) = inl (pair a b)
is-decidable-prod (inl a) (inr nb) = inr (λ x → nb (pr2 x))
is-decidable-prod (inr na) (inl b) = inr (λ x → na (pr1 x))
is-decidable-prod (inr na) (inr nb) = inr (λ x → na (pr1 x))

leq-div-ℕ : (d x : ℕ) → div-ℕ d (succ-ℕ x) → leq-ℕ d (succ-ℕ x)
leq-div-ℕ d x (pair (succ-ℕ k) p) =
  concatenate-leq-eq-ℕ d (leq-mul-ℕ' k d) p

leq-sum-is-common-divisor-ℕ :
  (a b d : ℕ) → (Σ ℕ (λ k → Id (add-ℕ a b) (succ-ℕ k))) →
  is-common-divisor-ℕ a b d → leq-ℕ d (add-ℕ a b)
leq-sum-is-common-divisor-ℕ a zero-ℕ d (pair k p) H =
  concatenate-leq-eq-ℕ d
    ( leq-div-ℕ d k (tr (div-ℕ d) p (pr1 H)))
    ( inv p)
leq-sum-is-common-divisor-ℕ a (succ-ℕ b) d (pair k p) H =
  leq-div-ℕ d (add-ℕ a b) (div-add-ℕ d a (succ-ℕ b) (pr1 H) (pr2 H))

is-successor-is-nonzero-ℕ :
  (x : ℕ) → ¬ (Id x zero-ℕ) → Σ ℕ (λ y → Id x (succ-ℕ y))
is-successor-is-nonzero-ℕ zero-ℕ H = ex-falso (H refl)
is-successor-is-nonzero-ℕ (succ-ℕ x) H = pair x refl

is-decidable-is-multiple-of-gcd-ℕ :
  (a b : ℕ) → is-decidable-fam (is-multiple-of-gcd-ℕ a b)
is-decidable-is-multiple-of-gcd-ℕ a b zero-ℕ =
  is-decidable-prod
    ( has-decidable-equality-ℕ a zero-ℕ)
    ( has-decidable-equality-ℕ b zero-ℕ)
is-decidable-is-multiple-of-gcd-ℕ a b (succ-ℕ n) with
  is-decidable-prod
    ( has-decidable-equality-ℕ a zero-ℕ)
    ( has-decidable-equality-ℕ b zero-ℕ)
... | inl e =
  inr
    ( λ f →
      Peano-8 n
        ( inv
          ( eq-zero-div-zero-ℕ
            ( succ-ℕ n)
            ( f zero-ℕ
              ( pair
                ( div-eq-ℕ zero-ℕ a (inv (pr1 e)))
                ( div-eq-ℕ zero-ℕ b (inv (pr2 e))))))))
... | inr f =
  is-decidable-Π-ℕ
    ( λ x → (is-common-divisor-ℕ a b x) → (div-ℕ x (succ-ℕ n)))
    ( λ x →
      is-decidable-function-type
        ( is-decidable-prod (is-decidable-div-ℕ x a) (is-decidable-div-ℕ x b))
        ( is-decidable-div-ℕ x (succ-ℕ n)))
    ( succ-ℕ (add-ℕ a b))
    ( λ x l H →
      ex-falso
        ( contradiction-leq-ℕ x
          ( add-ℕ a b)
          ( leq-sum-is-common-divisor-ℕ a b x
            ( is-successor-is-nonzero-ℕ
              ( add-ℕ a b)
              ( functor-neg (is-zero-summand-is-zero-sum-ℕ a b) f))
            ( H))
          ( l)))
  

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
