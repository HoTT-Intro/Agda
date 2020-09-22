{-# OPTIONS --without-K --exact-split #-}

module book.17-number-theory where

import book.17-set-quotients
open book.17-set-quotients public

-- Exercise 6.7

{- The Pigeon hole principle. -}

{- First we write a function that counts the number of elements in a decidable
   subset of a finite set. -}

count-Fin-succ-ℕ :
  {l : Level} (n : ℕ) (P : Fin (succ-ℕ n) → classical-Prop l) →
  ℕ → is-decidable (pr1 (pr1 (P (inr star)))) → ℕ
count-Fin-succ-ℕ n P m (inl x) = succ-ℕ m
count-Fin-succ-ℕ n P m (inr x) = m

count-Fin :
  {l : Level} (n : ℕ) (P : Fin n → classical-Prop l) → ℕ
count-Fin zero-ℕ P = zero-ℕ
count-Fin (succ-ℕ n) P =
  count-Fin-succ-ℕ n P
    ( count-Fin n (P ∘ inl))
    ( pr2 (P (inr star)))

{- Next we prove the pigeonhole principle. -}

max-Fin :
  (n : ℕ) → Fin (succ-ℕ n)
max-Fin n = inr star

contraction-Fin-one-ℕ :
  (t : Fin one-ℕ) → Id (inr star) t
contraction-Fin-one-ℕ (inr star) = refl

is-contr-Fin-one-ℕ :
  is-contr (Fin one-ℕ)
is-contr-Fin-one-ℕ = pair (inr star) contraction-Fin-one-ℕ

skip :
  (n : ℕ) → Fin (succ-ℕ n) → Fin n → Fin (succ-ℕ n)
skip (succ-ℕ n) (inl i) (inl j) = inl (skip n i j)
skip (succ-ℕ n) (inl i) (inr star) = inr star
skip (succ-ℕ n) (inr star) j = inl j

repeat :
  (n : ℕ) → Fin n → Fin (succ-ℕ n) → Fin n
repeat (succ-ℕ n) (inl i) (inl j) = inl (repeat n i j)
repeat (succ-ℕ n) (inl j) (inr star) = inr star
repeat (succ-ℕ n) (inr star) (inl j) = j
repeat (succ-ℕ n) (inr star) (inr star) = inr star

repeat-repeat :
  (n : ℕ) (i j : Fin n) →
    ((repeat n i) ∘ (repeat (succ-ℕ n) (skip n (inl i) j))) ~
    ((repeat n j) ∘ (repeat (succ-ℕ n) (skip n (inl j) i)))
repeat-repeat zero-ℕ () j k
repeat-repeat (succ-ℕ n) (inl i) (inl j) (inl k) =
  ap inl (repeat-repeat n i j k)
repeat-repeat (succ-ℕ n) (inl i) (inl j) (inr star) = refl
repeat-repeat (succ-ℕ n) (inl i) (inr star) (inr star) = refl
repeat-repeat (succ-ℕ n) (inr star) (inl j) (inr star) = refl
repeat-repeat (succ-ℕ n) (inr star) (inr star) (inl k) = refl
repeat-repeat (succ-ℕ n) (inr star) (inr star) (inr star) = refl
repeat-repeat (succ-ℕ zero-ℕ) (inl ()) (inr star) (inl k)
repeat-repeat (succ-ℕ (succ-ℕ n)) (inl i) (inr star) (inl k) = refl
repeat-repeat (succ-ℕ zero-ℕ) (inr star) (inl ()) (inl k) 
repeat-repeat (succ-ℕ (succ-ℕ n)) (inr star) (inl j) (inl k) = refl

{-
skip-repeat :
  (n : ℕ) (i : Fin n) → ((skip n (inl i)) ∘ (repeat n i)) ~ id
skip-repeat (succ-ℕ n) (inl x) (inl y) = ap inl (skip-repeat n x y)
skip-repeat (succ-ℕ n) (inl x) (inr star) = refl
skip-repeat (succ-ℕ n) (inr star) (inl (inl x)) = ap inl {!ap (skip n) ?!}
skip-repeat (succ-ℕ n) (inr star) (inl (inr star)) = {!!}
skip-repeat (succ-ℕ n) (inr star) (inr star) = {!!}
-}

map-lift-Fin :
  (m n : ℕ) (f : Fin (succ-ℕ m) → Fin (succ-ℕ n))
  (i : Fin (succ-ℕ n)) (H : fib f i → empty) →
  Fin m → Fin n
map-lift-Fin m n f (inl i) H = (repeat n i) ∘ (f ∘ inl)
map-lift-Fin m (succ-ℕ n) f (inr star) H =
  ( repeat (succ-ℕ n) (max-Fin n)) ∘
  ( f ∘ inl)
map-lift-Fin zero-ℕ zero-ℕ f (inr star) H = ind-empty
map-lift-Fin (succ-ℕ m) zero-ℕ f (inr star) H =
  ex-falso
    ( H (pair (inr star) (inv (contraction-Fin-one-ℕ (f (inr star))))))

{-
is-lift-lift-Fin :
  (m n : ℕ) (f : Fin (succ-ℕ m) → Fin (succ-ℕ n))
  (i : Fin (succ-ℕ n)) (H : fib f i → empty) →
  (f ∘ inl) ~ ((skip n i) ∘ (map-lift-Fin m n f i H))
is-lift-lift-Fin m n f (inl i) H x = {!!}
is-lift-lift-Fin m n f (inr i) H x = {!!}
-}

-- The greatest common divisor

{- First we show that mul-ℕ n is an embedding whenever n > 0. In order to do
   this, we have to show that add-ℕ n is injective. -}

{-  FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX
is-injective-add-ℕ' :
  (n : ℕ) → is-injective is-set-ℕ is-set-ℕ (add-ℕ n)
is-injective-add-ℕ' n k l p = is-injective-add-ℕ' n k l
  (((commutative-add-ℕ n k) ∙ ?) ∙ (commutative-add-ℕ l n))

is-emb-add-ℕ :
  (n : ℕ) → is-emb (add-ℕ n)
is-emb-add-ℕ n =
  is-emb-is-injective is-set-ℕ is-set-ℕ (add-ℕ n) (is-injective-add-ℕ n)

equiv-fib-add-fib-add-ℕ' :
  (m n : ℕ) → fib (add-ℕ' m) n ≃ fib (add-ℕ m) n
equiv-fib-add-fib-add-ℕ' m n =
  equiv-tot (λ k → equiv-concat (commutative-add-ℕ m k) n)

leq-fib-add-ℕ' :
  (m n : ℕ) → fib (add-ℕ' m) n → (leq-ℕ m n)
leq-fib-add-ℕ' zero-ℕ n (pair k p) = leq-zero-ℕ n
leq-fib-add-ℕ' (succ-ℕ m) (succ-ℕ n) (pair k p) =
  leq-fib-add-ℕ' m n (pair k (is-injective-succ-ℕ (add-ℕ k m) n p))

leq-fib-add-ℕ :
  (m n : ℕ) → fib (add-ℕ m) n → (leq-ℕ m n)
leq-fib-add-ℕ m .m (pair zero-ℕ refl) = reflexive-leq-ℕ m
leq-fib-add-ℕ m .(add-ℕ m (succ-ℕ k)) (pair (succ-ℕ k) refl) =
  transitive-leq-ℕ m (add-ℕ m k) (succ-ℕ (add-ℕ m k))
    ( leq-fib-add-ℕ m (add-ℕ m k) (pair k refl))
    ( succ-leq-ℕ (add-ℕ m k))
-}

{-
fib-add-leq-ℕ :
  (m n : ℕ) → (leq-ℕ m n) → fib (add-ℕ m) n
fib-add-leq-ℕ zero-ℕ zero-ℕ star = pair zero-ℕ refl
fib-add-leq-ℕ zero-ℕ (succ-ℕ n) star = {!!}
fib-add-leq-ℕ (succ-ℕ m) (succ-ℕ n) p = {!!}

{-
fib-add-leq-ℕ zero-ℕ zero-ℕ H = pair zero-ℕ refl
fib-add-leq-ℕ zero-ℕ (succ-ℕ n) H = pair (succ-ℕ n) refl
fib-add-leq-ℕ (succ-ℕ m) (succ-ℕ n) H =
  pair
    ( pr1 (fib-add-leq-ℕ m n H))
    ( ap succ-ℕ (pr2 (fib-add-leq-ℕ m n H)))
-}

is-equiv-leq-fib-add-ℕ :
  (m n : ℕ) → is-equiv (leq-fib-add-ℕ m n)
is-equiv-leq-fib-add-ℕ m n =
  is-equiv-is-prop
    ( is-prop-map-is-emb _ (is-emb-add-ℕ m) n)
    ( is-prop-leq-ℕ m n)
    ( fib-add-leq-ℕ m n)

is-equiv-fib-add-leq-ℕ :
  (m n : ℕ) → is-equiv (fib-add-leq-ℕ m n)
is-equiv-fib-add-leq-ℕ m n =
  is-equiv-is-prop
    ( is-prop-leq-ℕ m n)
    ( is-prop-map-is-emb _ (is-emb-add-ℕ m) n)
    ( leq-fib-add-ℕ m n)
-}

is-emb-mul-ℕ :
  (n : ℕ) → is-emb (mul-ℕ' (succ-ℕ n))
is-emb-mul-ℕ n =
  is-emb-is-injective is-set-ℕ is-set-ℕ
    ( mul-ℕ' (succ-ℕ n))
    ( is-injective-right-mul-ℕ n)

{- FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX
is-emb-mul-ℕ' :
  (n : ℕ) → (le-ℕ zero-ℕ n) → is-emb (λ m → mul-ℕ m n)
is-emb-mul-ℕ' n t =
  is-emb-htpy'
    ( mul-ℕ n)
    ( λ m → mul-ℕ m n)
    ( commutative-mul-ℕ n)
    ( is-emb-mul-ℕ n)
-}

{- We conclude that the division relation is a property. -}

{-  FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX
is-prop-div-ℕ :
  (m n : ℕ) → (le-ℕ zero-ℕ m) → is-prop (div-ℕ m n)
is-prop-div-ℕ (succ-ℕ m) n star =
  is-prop-map-is-emb
    ( λ z → mul-ℕ z (succ-ℕ m))
    ( is-emb-mul-ℕ' (succ-ℕ m) star)
    n
-}

{- We now construct the division with remainder. -}

le-mul-ℕ :
  (d n k : ℕ) → UU lzero
le-mul-ℕ d n k = le-ℕ n (mul-ℕ k d)

is-decidable-le-mul-ℕ :
  (d n k : ℕ) → is-decidable (le-mul-ℕ d n k)
is-decidable-le-mul-ℕ d n k =
  is-decidable-le-ℕ n (mul-ℕ k d)

order-preserving-succ-ℕ :
  (n n' : ℕ) → (leq-ℕ n n') → (leq-ℕ (succ-ℕ n) (succ-ℕ n'))
order-preserving-succ-ℕ n n' H = H

{-
order-preserving-add-ℕ :
  (m n m' n' : ℕ) →
  (leq-ℕ m m') → (leq-ℕ n n') → (leq-ℕ (add-ℕ m n) (add-ℕ m' n'))
order-preserving-add-ℕ = {!!}
-}

{-
order-preserving-add-ℕ zero-ℕ zero-ℕ m' n' Hm Hn = star
order-preserving-add-ℕ zero-ℕ (succ-ℕ n) zero-ℕ (succ-ℕ n') Hm Hn = Hn
order-preserving-add-ℕ zero-ℕ (succ-ℕ n) (succ-ℕ m') (succ-ℕ n') Hm Hn =
  leq-eq-right-ℕ n
    ( inv (right-successor-law-add-ℕ m' n'))
    ( order-preserving-add-ℕ zero-ℕ n (succ-ℕ m') n' Hm Hn)
order-preserving-add-ℕ (succ-ℕ m) n (succ-ℕ m') n' Hm Hn =
  order-preserving-add-ℕ m n m' n' Hm Hn
-}

le-eq-right-ℕ :
  (m : ℕ) {n n' : ℕ} → Id n n' → le-ℕ m n' → le-ℕ m n
le-eq-right-ℕ m refl = id

{-
le-add-ℕ :
  (m n : ℕ) → (leq-ℕ one-ℕ n) → le-ℕ m (add-ℕ m n)
le-add-ℕ = {!!}

{-
le-add-ℕ zero-ℕ (succ-ℕ n) star = star
le-add-ℕ (succ-ℕ m) (succ-ℕ n) star = le-add-ℕ m (succ-ℕ n) star
-}

le-mul-self-ℕ :
  (d n : ℕ) → (leq-ℕ one-ℕ d) → (leq-ℕ one-ℕ n) → le-mul-ℕ d n n
le-mul-self-ℕ (succ-ℕ d) (succ-ℕ n) star star =
  le-eq-right-ℕ
    ( succ-ℕ n)
    ( right-successor-law-mul-ℕ (succ-ℕ n) d)
    ( le-add-ℕ (succ-ℕ n) (mul-ℕ (succ-ℕ n) d) {!leq-eq-right-ℕ !})
-}

{-
leq-multiple-ℕ :
  (n m : ℕ) → (leq-ℕ one-ℕ m) → leq-ℕ n (mul-ℕ n m)
leq-multiple-ℕ n (succ-ℕ m) H =
  leq-eq-right-ℕ n
    ( inv (right-successor-law-mul-ℕ n m))
    ( leq-fib-add-ℕ n (add-ℕ n (mul-ℕ n m)) (pair (mul-ℕ n m) refl))

least-factor-least-larger-multiple-ℕ :
  (d n : ℕ) → (leq-ℕ one-ℕ d) →
  minimal-element-ℕ (λ k → leq-ℕ n (mul-ℕ k d))
least-factor-least-larger-multiple-ℕ d n H =
  well-ordering-principle-ℕ
    ( λ k → leq-ℕ n (mul-ℕ k d))
    ( λ k → is-decidable-leq-ℕ n (mul-ℕ k d))
    ( pair n (leq-multiple-ℕ n d H))

factor-least-larger-multiple-ℕ :
  (d n : ℕ) → (leq-ℕ one-ℕ d) → ℕ
factor-least-larger-multiple-ℕ d n H =
  pr1 (least-factor-least-larger-multiple-ℕ d n H)

least-larger-multiple-ℕ :
  (d n : ℕ) → (leq-ℕ one-ℕ d) → ℕ
least-larger-multiple-ℕ d n H =
  mul-ℕ (factor-least-larger-multiple-ℕ d n H) d

leq-least-larger-multiple-ℕ :
  (d n : ℕ) (H : leq-ℕ one-ℕ d) →
  leq-ℕ n (least-larger-multiple-ℕ d n H)
leq-least-larger-multiple-ℕ d n H =
  pr1 (pr2 (least-factor-least-larger-multiple-ℕ d n H))

is-minimal-least-larger-multiple-ℕ :
  (d n : ℕ) (H : leq-ℕ one-ℕ d) (k : ℕ) (K : leq-ℕ n (mul-ℕ k d)) →
  leq-ℕ (factor-least-larger-multiple-ℕ d n H) k
is-minimal-least-larger-multiple-ℕ d n H =
  pr2 (pr2 (least-factor-least-larger-multiple-ℕ d n H))
-}

{-
is-decidable-div-is-decidable-eq-least-larger-multiple-ℕ :
  (d n : ℕ) (H : leq-ℕ one-ℕ d) →
  is-decidable (Id (least-larger-multiple-ℕ d n H) n) → is-decidable (div-ℕ d n)
is-decidable-div-is-decidable-eq-least-larger-multiple-ℕ d n H (inl p) =
  inl (pair (factor-least-larger-multiple-ℕ d n H) p)
is-decidable-div-is-decidable-eq-least-larger-multiple-ℕ d n H (inr f) =
  inr (λ x → {!!})

is-decidable-div-ℕ' :
  (d n : ℕ) → (leq-ℕ one-ℕ d) → is-decidable (div-ℕ d n)
is-decidable-div-ℕ' d n H = {!!}

is-decidable-div-ℕ :
  (d n : ℕ) → is-decidable (div-ℕ d n)
is-decidable-div-ℕ zero-ℕ zero-ℕ = inl (pair zero-ℕ refl)
is-decidable-div-ℕ zero-ℕ (succ-ℕ n) =
  inr ( λ p →
    Eq-ℕ-eq {-zero-ℕ (succ-ℕ n)-} ((inv (right-zero-law-mul-ℕ (pr1 p))) ∙ (pr2 p)))
is-decidable-div-ℕ (succ-ℕ d) n =
  is-decidable-div-ℕ' (succ-ℕ d) n (leq-zero-ℕ d)
-}

-- Operations on decidable bounded subsets of ℕ

iterated-operation-ℕ :
  (strict-upper-bound : ℕ) (operation : ℕ → ℕ → ℕ) (base-value : ℕ) → ℕ
iterated-operation-ℕ zero-ℕ μ e = e
iterated-operation-ℕ (succ-ℕ b) μ e = μ (iterated-operation-ℕ b μ e) b

iterated-sum-ℕ :
  (summand : ℕ → ℕ) (b : ℕ) → ℕ
iterated-sum-ℕ f zero-ℕ = zero-ℕ
iterated-sum-ℕ f (succ-ℕ b) = add-ℕ (iterated-sum-ℕ f b) (f (succ-ℕ b))

ranged-sum-ℕ :
  (summand : ℕ → ℕ) (l u : ℕ) → ℕ
ranged-sum-ℕ f zero-ℕ u = iterated-sum-ℕ f u
ranged-sum-ℕ f (succ-ℕ l) zero-ℕ = zero-ℕ
ranged-sum-ℕ f (succ-ℕ l) (succ-ℕ u) =
  ranged-sum-ℕ (f ∘ succ-ℕ) l u

succ-iterated-operation-fam-ℕ :
  { l : Level}
  ( P : ℕ → UU l) (is-decidable-P : (n : ℕ) → is-decidable (P n)) →
  ( predecessor-strict-upper-bound : ℕ) (operation : ℕ → ℕ → ℕ) →
  is-decidable (P predecessor-strict-upper-bound) → ℕ → ℕ
succ-iterated-operation-fam-ℕ
  P is-decidable-P b μ (inl p) m = μ m b
succ-iterated-operation-fam-ℕ
  P is-decidable-P b μ (inr f) m = m

iterated-operation-fam-ℕ :
  { l : Level} (P : ℕ → UU l) (is-decidable-P : (n : ℕ) → is-decidable (P n)) →
  ( strict-upper-bound : ℕ) (operation : ℕ → ℕ → ℕ) (base-value : ℕ) → ℕ
iterated-operation-fam-ℕ P d zero-ℕ μ e = e
iterated-operation-fam-ℕ P d (succ-ℕ b) μ e =
  succ-iterated-operation-fam-ℕ P d b μ (d b)
    ( iterated-operation-fam-ℕ P d b μ e)

Sum-fam-ℕ :
  { l : Level} (P : ℕ → UU l) (is-decidable-P : (n : ℕ) → is-decidable (P n)) →
  ( upper-bound : ℕ) ( summand : ℕ → ℕ) → ℕ
Sum-fam-ℕ P d b f = iterated-operation-fam-ℕ P d (succ-ℕ b) (λ x y → add-ℕ x (f y)) zero-ℕ

{-
iterated-operation-fam-ℕ
  P is-decidable-P zero-ℕ is-bounded-P μ base-value =
  base-value
iterated-operation-fam-ℕ
  P is-decidable-P (succ-ℕ b) is-bounded-P μ base-value =
  succ-iterated-operation-ℕ P is-decidable-P b is-bounded-P μ
    ( is-decidable-P b)
    ( iterated-operation-ℕ
      ( introduce-bound-on-fam-ℕ b P)
      ( is-decidable-introduce-bound-on-fam-ℕ b P is-decidable-P)
      ( b)
      ( is-bounded-introduce-bound-on-fam-ℕ b P)
      ( μ)
      ( base-value))

product-decidable-bounded-fam-ℕ :
  { l : Level} (P : ℕ → UU l) →
  ( is-decidable-P : (n : ℕ) → is-decidable (P n))
  ( b : ℕ) ( is-bounded-P : is-bounded-fam-ℕ b P) → ℕ
product-decidable-bounded-fam-ℕ P is-decidable-P b is-bounded-P =
  iterated-operation-ℕ P is-decidable-P b is-bounded-P mul-ℕ one-ℕ

twenty-four-ℕ : ℕ
twenty-four-ℕ =
  product-decidable-bounded-fam-ℕ
    ( λ x → le-ℕ x five-ℕ)
    ( λ x → is-decidable-le-ℕ x five-ℕ)
    ( five-ℕ)
    ( λ x → id)
-}

{-
test-zero-twenty-four-ℕ : Id twenty-four-ℕ zero-ℕ
test-zero-twenty-four-ℕ = refl

test-twenty-four-ℕ : Id twenty-four-ℕ (factorial four-ℕ)
test-twenty-four-ℕ = refl
-}

-- Exercises

-- Exercise 10.?

abstract
  has-decidable-equality-𝟚 : has-decidable-equality bool
  has-decidable-equality-𝟚 true true = inl refl
  has-decidable-equality-𝟚 true false = inr (Eq-𝟚-eq true false)
  has-decidable-equality-𝟚 false true = inr (Eq-𝟚-eq false true)
  has-decidable-equality-𝟚 false false = inl refl

-- Exercise 10.?

abstract
  has-decidable-equality-prod' : {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    (x x' : A) (y y' : B) → is-decidable (Id x x') → is-decidable (Id y y') →
    is-decidable (Id (pair x y) (pair x' y'))
  has-decidable-equality-prod' x x' y y' (inl p) (inl q) =
    inl (eq-pair-triv (pair p q))
  has-decidable-equality-prod' x x' y y' (inl p) (inr g) =
    inr (λ h → g (ap pr2 h))
  has-decidable-equality-prod' x x' y y' (inr f) (inl q) =
    inr (λ h → f (ap pr1 h))
  has-decidable-equality-prod' x x' y y' (inr f) (inr g) =
    inr (λ h → f (ap pr1 h))

abstract
  has-decidable-equality-prod : {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    has-decidable-equality A → has-decidable-equality B →
    has-decidable-equality (A × B)
  has-decidable-equality-prod dec-A dec-B (pair x y) (pair x' y') =
    has-decidable-equality-prod' x x' y y' (dec-A x x') (dec-B y y')


{-

bounds-fam-ℕ :
  {l : Level} (P : ℕ → UU l) → UU l
bounds-fam-ℕ P = Σ ℕ (λ n → is-bounded-fam-ℕ n P)

is-minimal-ℕ :
  {l : Level} (P : ℕ → UU l) → Σ ℕ P → UU l
is-minimal-ℕ P (pair n p) = (t : Σ ℕ P) → leq-ℕ n (pr1 t)

fam-succ-ℕ :
  {l : Level} → (ℕ → UU l) → (ℕ → UU l)
fam-succ-ℕ P n = P (succ-ℕ n)

is-decidable-fam-succ-ℕ :
  {l : Level} (P : ℕ → UU l) →
  ((n : ℕ) → is-decidable (P n)) → ((n : ℕ) → is-decidable (P (succ-ℕ n)))
is-decidable-fam-succ-ℕ P d n = d (succ-ℕ n)

min-is-bounded-not-zero-ℕ :
  {l : Level} (P : ℕ → UU l) → ((n : ℕ) → is-decidable (P n)) →
  Σ ℕ (λ n → is-bounded-fam-ℕ n P) →
  ¬ (P zero-ℕ) →
  Σ (Σ ℕ (fam-succ-ℕ P)) (is-minimal-ℕ (fam-succ-ℕ P)) →
  Σ (Σ ℕ P) (is-minimal-ℕ P)
min-is-bounded-not-zero-ℕ P d b np0 t = {!!}

min-is-bounded-ℕ :
  {l : Level} (P : ℕ → UU l) → ((n : ℕ) → is-decidable (P n)) →
  Σ ℕ (λ n → is-bounded-fam-ℕ n P) →
  Σ ℕ P → Σ (Σ ℕ P) (is-minimal-ℕ P)
min-is-bounded-ℕ P d (pair zero-ℕ b) t =
  pair
    ( pair
      ( zero-ℕ)
      ( tr P (eq-zero-leq-zero-ℕ (pr1 t) (b (pr1 t) (pr2 t))) (pr2 t)))
    ( λ p → leq-zero-ℕ (pr1 p))
min-is-bounded-ℕ P d (pair (succ-ℕ n) b) t =
  ind-coprod
    ( λ (t : is-decidable (P zero-ℕ)) → Σ (Σ ℕ P) (is-minimal-ℕ P))
    ( λ p0 → pair (pair zero-ℕ p0) (λ p → leq-zero-ℕ (pr1 p)))
    ( λ y → min-is-bounded-not-zero-ℕ P d (pair (succ-ℕ n) b) y
      ( min-is-bounded-ℕ
        ( fam-succ-ℕ P)
        ( is-decidable-fam-succ-ℕ P d)
        {!!}
        {!!}))
    ( d zero-ℕ)

{- We show that every non-empty decidable subset of ℕ has a least element. -}

least-ℕ :
  {l : Level} (P : ℕ → UU l) → Σ ℕ P → UU l
least-ℕ P (pair n p) = (m : ℕ) → P m → leq-ℕ n m

least-element-non-empty-decidable-subset-ℕ :
  {l : Level} (P : ℕ → UU l) (d : (n : ℕ) → is-decidable (P n)) →
  Σ ℕ P → Σ (Σ ℕ P) (least-ℕ P)
least-element-non-empty-decidable-subset-ℕ P d (pair zero-ℕ p) =
  pair (pair zero-ℕ p) {!!}
least-element-non-empty-decidable-subset-ℕ P d (pair (succ-ℕ n) p) = {!!}
-}

{-
zero-Fin :
  (n : ℕ) → Fin (succ-ℕ n)
zero-Fin zero-ℕ = inr star
zero-Fin (succ-ℕ n) = inl (zero-Fin n)

succ-Fin :
  (n : ℕ) → Fin n → Fin n
succ-Fin (succ-ℕ n) (inr star) = zero-Fin n
succ-Fin (succ-ℕ (succ-ℕ n)) (inl (inl x)) = inl (succ-Fin (succ-ℕ n) (inl x))
succ-Fin (succ-ℕ (succ-ℕ n)) (inl (inr star)) = inr star

iterated-succ-Fin :
  (k : ℕ) → (n : ℕ) → Fin n → Fin n
iterated-succ-Fin zero-ℕ n = id
iterated-succ-Fin (succ-ℕ k) n = (succ-Fin n) ∘ (iterated-succ-Fin k n)

quotient-ℕ-Fin :
  (n : ℕ) → Fin (succ-ℕ n)
quotient-ℕ-Fin n = iterated-succ-Fin n (succ-ℕ n) (zero-Fin n)

pred-Fin :
  (n : ℕ) → Fin n → Fin n
pred-Fin (succ-ℕ zero-ℕ) (inr star) = inr star
pred-Fin (succ-ℕ (succ-ℕ n)) (inl x) = {!!}
pred-Fin (succ-ℕ (succ-ℕ n)) (inr star) = inl (inr star)

add-Fin :
  (n : ℕ) → Fin n → Fin n → Fin n
add-Fin (succ-ℕ n) (inl x) j = {!!}
add-Fin (succ-ℕ n) (inr x) j = {!!}


idempotent-succ-Fin :
  (n : ℕ) (i : Fin n) → Id (iterated-succ-Fin n n i) i
idempotent-succ-Fin (succ-ℕ zero-ℕ) (inr star) = refl
idempotent-succ-Fin (succ-ℕ (succ-ℕ n)) (inl x) = {!!}
idempotent-succ-Fin (succ-ℕ (succ-ℕ n)) (inr x) = {!!}

-}

in-nat-ℤ : ℕ → ℤ
in-nat-ℤ zero-ℕ = zero-ℤ
in-nat-ℤ (succ-ℕ n) = in-pos n

div-ℤ :
  (k l : ℤ) → UU lzero
div-ℤ k l = Σ ℤ (λ x → Id (mul-ℤ x k) l)

-- From before

{- The Goldbach conjecture asserts that every even number above 2 is the sum
   of two primes. -}

Goldbach-conjecture : UU lzero
Goldbach-conjecture =
  ( n : ℕ) → (two-ℕ < n) → (is-even-ℕ n) →
    Σ ℕ (λ p → (is-prime p) × (Σ ℕ (λ q → (is-prime q) × Id (add-ℕ p q) n)))

is-twin-prime : ℕ → UU lzero
is-twin-prime n = (is-prime n) × (is-prime (succ-ℕ (succ-ℕ n)))

{- The twin prime conjecture asserts that there are infinitely many twin 
   primes. We assert that there are infinitely twin primes by asserting that 
   for every n : ℕ there is a twin prime that is larger than n. -}
   
Twin-prime-conjecture : UU lzero
Twin-prime-conjecture = (n : ℕ) → Σ ℕ (λ p → (is-twin-prime p) × (leq-ℕ n p))

-- Exercise

unit-classical-Prop : classical-Prop lzero
unit-classical-Prop =
  pair unit-Prop (inl star)

raise-unit-classical-Prop :
  (l : Level) → classical-Prop l
raise-unit-classical-Prop l =
  pair
    ( pair
      ( raise l unit)
      ( is-prop-is-equiv' unit
        ( map-raise)
        ( is-equiv-map-raise l unit)
        ( is-prop-unit)))
    ( inl (map-raise star))

bool-classical-Prop :
  (l : Level) → classical-Prop l → bool
bool-classical-Prop l (pair P (inl x)) = true
bool-classical-Prop l (pair P (inr x)) = false

{-
classical-Prop-bool :
  (l : Level) → bool → classical-Prop l
classical-Prop-bool l true = raise-unit-classical-Prop l
classical-Prop-bool l false = {!!}
-}
