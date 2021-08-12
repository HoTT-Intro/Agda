{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module extra.cofibonacci where

open import extra.pigeonhole-principle public

{-------------------------------------------------------------------------------

  The Cofibonacci Sequence
  ------------------------

  In this file we construct the cofibonacci sequence [1], which is the unique
  function G : ℕ → ℕ satisfying the property that
  
  div-ℕ (G m) n ↔ div-ℕ m (Fibonacci-ℕ n).

  It is closely related to the sequence of Pisano periods [2], which is the
  sequence P : ℕ → ℕ, where P n is the period of the Fibonacci sequence modulo
  n. We will construct the Pisano periods along the way.

  [1] https://oeis.org/A001177
  [2] https://oeis.org/A001175

-------------------------------------------------------------------------------}

-- We show that Fibonacci-ℕ is a functor on ℕ ordered by divisibility

Fibonacci-add-ℕ :
  (m n : ℕ) →
  Id ( Fibonacci-ℕ (add-ℕ m (succ-ℕ n)))
     ( add-ℕ ( mul-ℕ (Fibonacci-ℕ (succ-ℕ m)) (Fibonacci-ℕ (succ-ℕ n)))
             ( mul-ℕ (Fibonacci-ℕ m) (Fibonacci-ℕ n)))
Fibonacci-add-ℕ m zero-ℕ =
  inv ( ( ap ( λ t → add-ℕ t (mul-ℕ (Fibonacci-ℕ m) zero-ℕ))
             ( right-unit-law-mul-ℕ (Fibonacci-ℕ (succ-ℕ m)))) ∙
        ( ap ( add-ℕ (Fibonacci-ℕ (succ-ℕ m)))
             ( right-zero-law-mul-ℕ (Fibonacci-ℕ m))))
Fibonacci-add-ℕ m (succ-ℕ n) =
  ( ap Fibonacci-ℕ (inv (left-successor-law-add-ℕ m (succ-ℕ n)))) ∙
  ( ( Fibonacci-add-ℕ (succ-ℕ m) n) ∙
    ( ( ap ( add-ℕ' (mul-ℕ (Fibonacci-ℕ (succ-ℕ m)) (Fibonacci-ℕ n)))
           ( right-distributive-mul-add-ℕ
             ( Fibonacci-ℕ (succ-ℕ m))
             ( Fibonacci-ℕ m)
             ( Fibonacci-ℕ (succ-ℕ n)))) ∙
      ( ( associative-add-ℕ
          ( mul-ℕ (Fibonacci-ℕ (succ-ℕ m)) (Fibonacci-ℕ (succ-ℕ n)))
          ( mul-ℕ (Fibonacci-ℕ m) (Fibonacci-ℕ (succ-ℕ n)))
          ( mul-ℕ (Fibonacci-ℕ (succ-ℕ m)) (Fibonacci-ℕ n))) ∙
        ( ( ap ( add-ℕ
                 ( mul-ℕ (Fibonacci-ℕ (succ-ℕ m)) (Fibonacci-ℕ (succ-ℕ n))))
               ( commutative-add-ℕ
                 ( mul-ℕ (Fibonacci-ℕ m) (Fibonacci-ℕ (succ-ℕ n)))
                 ( mul-ℕ (Fibonacci-ℕ (succ-ℕ m)) (Fibonacci-ℕ n)))) ∙
          ( ( inv
              ( associative-add-ℕ
                ( mul-ℕ (Fibonacci-ℕ (succ-ℕ m)) (Fibonacci-ℕ (succ-ℕ n)))
                ( mul-ℕ (Fibonacci-ℕ (succ-ℕ m)) (Fibonacci-ℕ n))
                ( mul-ℕ (Fibonacci-ℕ m) (Fibonacci-ℕ (succ-ℕ n))))) ∙
            ( ap ( add-ℕ' (mul-ℕ (Fibonacci-ℕ m) (Fibonacci-ℕ (succ-ℕ n))))
                 ( inv
                   ( left-distributive-mul-add-ℕ
                     ( Fibonacci-ℕ (succ-ℕ m))
                     ( Fibonacci-ℕ (succ-ℕ n))
                     ( Fibonacci-ℕ n)))))))))

{-
   We prove that if an two of the following three properties hold, then so does
   the third:

   1. d | Fibonacci-ℕ m
   2. d | Fibonacci-ℕ n
   3. d | Fibonacci-ℕ (add-ℕ m n).
-}

div-Fibonacci-add-ℕ :
  (d m n : ℕ) → div-ℕ d (Fibonacci-ℕ m) → div-ℕ d (Fibonacci-ℕ n) →
  div-ℕ d (Fibonacci-ℕ (add-ℕ m n))
div-Fibonacci-add-ℕ d m zero-ℕ H1 H2 = H1
div-Fibonacci-add-ℕ d m (succ-ℕ n) H1 H2 =
  tr ( div-ℕ d)
     ( inv (Fibonacci-add-ℕ m n))
     ( div-add-ℕ d
       ( mul-ℕ (Fibonacci-ℕ (succ-ℕ m)) (Fibonacci-ℕ (succ-ℕ n)))
       ( mul-ℕ (Fibonacci-ℕ m) (Fibonacci-ℕ n))
       ( div-mul-ℕ (Fibonacci-ℕ (succ-ℕ m)) d (Fibonacci-ℕ (succ-ℕ n)) H2)
       ( tr ( div-ℕ d)
            ( commutative-mul-ℕ (Fibonacci-ℕ n) (Fibonacci-ℕ m))
            ( div-mul-ℕ (Fibonacci-ℕ n) d (Fibonacci-ℕ m) H1)))

div-Fibonacci-left-summand-ℕ :
  (d m n : ℕ) → div-ℕ d (Fibonacci-ℕ n) → div-ℕ d (Fibonacci-ℕ (add-ℕ m n)) →
  div-ℕ d (Fibonacci-ℕ m)
div-Fibonacci-left-summand-ℕ d m n H1 H2 =
  {!!}

div-Fibonacci-div-ℕ :
  (d m n : ℕ) → div-ℕ m n → div-ℕ d (Fibonacci-ℕ m) → div-ℕ d (Fibonacci-ℕ n)
div-Fibonacci-div-ℕ d m .zero-ℕ (pair zero-ℕ refl) H = div-zero-ℕ d
div-Fibonacci-div-ℕ d zero-ℕ .(mul-ℕ k zero-ℕ) (pair (succ-ℕ k) refl) H =
  tr ( div-ℕ d)
     ( ap Fibonacci-ℕ (inv (right-zero-law-mul-ℕ (succ-ℕ k))))
     ( div-zero-ℕ d)
div-Fibonacci-div-ℕ d (succ-ℕ m) .(succ-ℕ (add-ℕ (mul-ℕ k (succ-ℕ m)) m))
  ( pair (succ-ℕ k) refl) H =
   div-Fibonacci-add-ℕ d
     ( mul-ℕ k (succ-ℕ m))
     ( succ-ℕ m)
     ( div-Fibonacci-div-ℕ d
       ( succ-ℕ m)
       ( mul-ℕ k (succ-ℕ m))
       ( pair k refl)
       ( H))
     ( H)

-- Fibonacci-ℕ is an order preserving map on ℕ ordered by divisibility.

preserves-div-Fibonacci-ℕ :
  (m n : ℕ) → div-ℕ m n → div-ℕ (Fibonacci-ℕ m) (Fibonacci-ℕ n)
preserves-div-Fibonacci-ℕ m n H =
  div-Fibonacci-div-ℕ (Fibonacci-ℕ m) m n H (refl-div-ℕ (Fibonacci-ℕ m))

--------------------------------------------------------------------------------

-- The Pisano sequence

generating-map-fibonacci-pair-Fin :
  (k : ℕ) → Fin (succ-ℕ k) × Fin (succ-ℕ k) → Fin (succ-ℕ k) × Fin (succ-ℕ k)
generating-map-fibonacci-pair-Fin k p =
  pair (pr2 p) (add-Fin (pr2 p) (pr1 p))

inv-generating-map-fibonacci-pair-Fin :
  (k : ℕ) → Fin (succ-ℕ k) × Fin (succ-ℕ k) → Fin (succ-ℕ k) × Fin (succ-ℕ k)
inv-generating-map-fibonacci-pair-Fin k (pair x y) =
  pair (add-Fin y (neg-Fin x)) x

issec-inv-generating-map-fibonacci-pair-Fin :
  (k : ℕ) (p : Fin (succ-ℕ k) × Fin (succ-ℕ k)) →
  Id ( generating-map-fibonacci-pair-Fin k
       ( inv-generating-map-fibonacci-pair-Fin k p))
     ( p)
issec-inv-generating-map-fibonacci-pair-Fin k (pair x y) =
  ap-binary pair refl
    ( ( commutative-add-Fin x (add-Fin y (neg-Fin x))) ∙
      ( ( associative-add-Fin y (neg-Fin x) x) ∙
        ( ( ap (add-Fin y) (left-inverse-law-add-Fin x)) ∙
          ( right-unit-law-add-Fin y))))

isretr-inv-generating-map-fibonacci-pair-Fin :
  (k : ℕ ) (p : Fin (succ-ℕ k) × Fin (succ-ℕ k)) →
  Id ( inv-generating-map-fibonacci-pair-Fin k
       ( generating-map-fibonacci-pair-Fin k p))
     ( p)
isretr-inv-generating-map-fibonacci-pair-Fin k (pair x y) =
  ap-binary pair
    ( commutative-add-Fin (add-Fin y x) (neg-Fin y) ∙
      ( ( inv (associative-add-Fin (neg-Fin y) y x)) ∙
        ( ( ap (λ t → add-Fin t x) (left-inverse-law-add-Fin y)) ∙
          ( left-unit-law-add-Fin x))))
    ( refl)

is-equiv-generating-map-fibonacci-pair-Fin :
  (k : ℕ) → is-equiv (generating-map-fibonacci-pair-Fin k)
is-equiv-generating-map-fibonacci-pair-Fin k =
  is-equiv-has-inverse
    ( inv-generating-map-fibonacci-pair-Fin k)
    ( issec-inv-generating-map-fibonacci-pair-Fin k)
    ( isretr-inv-generating-map-fibonacci-pair-Fin k)

fibonacci-pair-Fin :
  (k : ℕ) → ℕ → Fin (succ-ℕ k) × Fin (succ-ℕ k)
fibonacci-pair-Fin k zero-ℕ = pair zero-Fin one-Fin
fibonacci-pair-Fin k (succ-ℕ n) =
  generating-map-fibonacci-pair-Fin k (fibonacci-pair-Fin k n)

compute-fibonacci-pair-Fin :
  (k : ℕ) (n : ℕ) →
  Id ( fibonacci-pair-Fin k n)
     ( pair ( mod-succ-ℕ k (Fibonacci-ℕ n))
            ( mod-succ-ℕ k (Fibonacci-ℕ (succ-ℕ n))))
compute-fibonacci-pair-Fin k zero-ℕ = refl
compute-fibonacci-pair-Fin k (succ-ℕ zero-ℕ) =
  ap-binary pair refl (right-unit-law-add-Fin one-Fin)
compute-fibonacci-pair-Fin k (succ-ℕ (succ-ℕ n)) =
  ap-binary pair
    ( ap pr2 (compute-fibonacci-pair-Fin k (succ-ℕ n)))
    ( ( ap-binary add-Fin
        ( ap pr2 (compute-fibonacci-pair-Fin k (succ-ℕ n)))
        ( ap pr1 (compute-fibonacci-pair-Fin k (succ-ℕ n)))) ∙
      ( inv
        ( mod-succ-add-ℕ k
          ( Fibonacci-ℕ (succ-ℕ (succ-ℕ n)))
          ( Fibonacci-ℕ (succ-ℕ n)))))

has-ordered-repetition-fibonacci-pair-Fin :
  (k : ℕ) → has-ordered-repetition-ℕ (fibonacci-pair-Fin k)
has-ordered-repetition-fibonacci-pair-Fin k =
  has-ordered-repetition-nat-to-count
    ( count-prod (count-Fin (succ-ℕ k)) (count-Fin (succ-ℕ k)))
    ( fibonacci-pair-Fin k)

minimal-ordered-repetition-fibonacci-pair-Fin :
  (k : ℕ) →
  minimal-element-ℕ (is-ordered-repetition-ℕ (fibonacci-pair-Fin k))
minimal-ordered-repetition-fibonacci-pair-Fin k =
  well-ordering-principle-ℕ
    ( is-ordered-repetition-ℕ (fibonacci-pair-Fin k))
    ( is-decidable-is-ordered-repetition-ℕ-count
        ( count-prod (count-Fin (succ-ℕ k)) (count-Fin (succ-ℕ k)))
        ( fibonacci-pair-Fin k))
    ( has-ordered-repetition-fibonacci-pair-Fin k)

pisano-period : ℕ → ℕ
pisano-period k = pr1 (minimal-ordered-repetition-fibonacci-pair-Fin k)

is-ordered-repetition-pisano-period :
  (k : ℕ) →
  is-ordered-repetition-ℕ (fibonacci-pair-Fin k) (pisano-period k)
is-ordered-repetition-pisano-period k =
  pr1 (pr2 (minimal-ordered-repetition-fibonacci-pair-Fin k))

is-lower-bound-pisano-period :
  (k : ℕ) →
  is-lower-bound-ℕ
    ( is-ordered-repetition-ℕ (fibonacci-pair-Fin k))
    ( pisano-period k)
is-lower-bound-pisano-period k =
  pr2 (pr2 (minimal-ordered-repetition-fibonacci-pair-Fin k))

cases-is-repetition-of-zero-pisano-period :
  (k x y : ℕ) → Id (pr1 (is-ordered-repetition-pisano-period k)) x →
  Id (pisano-period k) y → is-zero-ℕ x
cases-is-repetition-of-zero-pisano-period k zero-ℕ y p q = refl
cases-is-repetition-of-zero-pisano-period k (succ-ℕ x) zero-ℕ p q =
   ex-falso
     ( concatenate-eq-le-eq-ℕ
       ( inv p)
       ( pr1 (pr2 (is-ordered-repetition-pisano-period k)))
       ( q))
cases-is-repetition-of-zero-pisano-period k (succ-ℕ x) (succ-ℕ y) p q =
  ex-falso
    ( contradiction-leq-ℕ y y (refl-leq-ℕ y)
      ( concatenate-eq-leq-ℕ y (inv q) (is-lower-bound-pisano-period k y R)))
  where
  R : is-ordered-repetition-ℕ (fibonacci-pair-Fin k) y
  R = triple x
        ( concatenate-eq-le-eq-ℕ
          ( inv p)
          ( pr1 (pr2 (is-ordered-repetition-pisano-period k)))
          ( q))
        ( is-injective-is-equiv
          ( is-equiv-generating-map-fibonacci-pair-Fin k)
          ( ( ap (fibonacci-pair-Fin k) (inv p)) ∙
            ( ( pr2 (pr2 (is-ordered-repetition-pisano-period k))) ∙
              ( ap (fibonacci-pair-Fin k) q))))

is-repetition-of-zero-pisano-period :
  (k : ℕ) → is-zero-ℕ (pr1 (is-ordered-repetition-pisano-period k))
is-repetition-of-zero-pisano-period k =
  cases-is-repetition-of-zero-pisano-period k
    ( pr1 (is-ordered-repetition-pisano-period k))
    ( pisano-period k)
    ( refl)
    ( refl)

compute-fibonacci-pair-Fin-pisano-period :
  (k : ℕ) →
  Id (fibonacci-pair-Fin k (pisano-period k)) (fibonacci-pair-Fin k zero-ℕ)
compute-fibonacci-pair-Fin-pisano-period k =
  ( inv (pr2 (pr2 (is-ordered-repetition-pisano-period k)))) ∙
  ( ap (fibonacci-pair-Fin k) (is-repetition-of-zero-pisano-period k)) 

le-zero-pisano-period :
  (k : ℕ) → le-ℕ zero-ℕ (pisano-period k)
le-zero-pisano-period k =
  concatenate-eq-le-ℕ
    { x = zero-ℕ}
    { y = pr1 (is-ordered-repetition-pisano-period k)}
    { z = pisano-period k}
    ( inv (is-repetition-of-zero-pisano-period k))
    ( pr1 (pr2 (is-ordered-repetition-pisano-period k)))

is-nonzero-pisano-period :
  (k : ℕ) → is-nonzero-ℕ (pisano-period k)
is-nonzero-pisano-period k p =
  ex-falso (concatenate-le-eq-ℕ (le-zero-pisano-period k) p)

div-fibonacci-pisano-period :
  (k : ℕ) → div-ℕ (succ-ℕ k) (Fibonacci-ℕ (pisano-period k))
div-fibonacci-pisano-period k =
  div-ℕ-is-zero-Fin k
    ( Fibonacci-ℕ (pisano-period k))
    ( ( ap pr1 (inv (compute-fibonacci-pair-Fin k (pisano-period k)))) ∙
      ( inv
        ( ap pr1
          { x = fibonacci-pair-Fin k zero-ℕ}
          { y = fibonacci-pair-Fin k (pisano-period k)}
          ( ( ap ( fibonacci-pair-Fin k)
                 ( inv (is-repetition-of-zero-pisano-period k))) ∙
            ( pr2 (pr2 (is-ordered-repetition-pisano-period k)))))))

--------------------------------------------------------------------------------

-- The cofibonacci sequence

is-multiple-of-cofibonacci : (m x : ℕ) → UU lzero
is-multiple-of-cofibonacci m x =
  is-nonzero-ℕ m → is-nonzero-ℕ x × div-ℕ m (Fibonacci-ℕ x)

is-decidable-is-multiple-of-cofibonacci :
  (m x : ℕ) → is-decidable (is-multiple-of-cofibonacci m x)
is-decidable-is-multiple-of-cofibonacci m x =
  is-decidable-function-type
    ( is-decidable-is-nonzero-ℕ m)
    ( is-decidable-prod
      ( is-decidable-is-nonzero-ℕ x)
      ( is-decidable-div-ℕ m (Fibonacci-ℕ x)))

cofibonacci-multiple :
  (m : ℕ) → Σ ℕ (is-multiple-of-cofibonacci m)
cofibonacci-multiple zero-ℕ = pair zero-ℕ (λ f → (ex-falso (f refl)))
cofibonacci-multiple (succ-ℕ m) =
  pair ( pisano-period m)
       ( λ f →
         pair (is-nonzero-pisano-period m) (div-fibonacci-pisano-period m))

least-multiple-of-cofibonacci :
  (m : ℕ) → minimal-element-ℕ (is-multiple-of-cofibonacci m)
least-multiple-of-cofibonacci m =
  well-ordering-principle-ℕ
    ( is-multiple-of-cofibonacci m)
    ( is-decidable-is-multiple-of-cofibonacci m)
    ( cofibonacci-multiple m)

cofibonacci : ℕ → ℕ
cofibonacci m = pr1 (least-multiple-of-cofibonacci m)

is-multiple-of-cofibonacci-cofibonacci :
  (m : ℕ) → is-multiple-of-cofibonacci m (cofibonacci m)
is-multiple-of-cofibonacci-cofibonacci m =
  pr1 (pr2 (least-multiple-of-cofibonacci m))

is-lower-bound-cofibonacci :
  (m x : ℕ) → is-multiple-of-cofibonacci m x → cofibonacci m ≤-ℕ x
is-lower-bound-cofibonacci m =
  pr2 (pr2 (least-multiple-of-cofibonacci m))

is-zero-cofibonacci-zero-ℕ : is-zero-ℕ (cofibonacci zero-ℕ)
is-zero-cofibonacci-zero-ℕ =
  is-zero-leq-zero-ℕ
    ( cofibonacci zero-ℕ)
    ( is-lower-bound-cofibonacci zero-ℕ zero-ℕ
      ( λ f → ex-falso (f refl)))

forward-is-left-adjoint-cofibonacci :
  (m n : ℕ) → div-ℕ (cofibonacci m) n → div-ℕ m (Fibonacci-ℕ n)
forward-is-left-adjoint-cofibonacci zero-ℕ n H =
  tr ( div-ℕ zero-ℕ)
     ( ap ( Fibonacci-ℕ)
          ( inv
            ( is-zero-div-zero-ℕ n
              ( tr (λ t → div-ℕ t n) is-zero-cofibonacci-zero-ℕ H))))
     ( refl-div-ℕ zero-ℕ)
forward-is-left-adjoint-cofibonacci (succ-ℕ m) zero-ℕ H = div-zero-ℕ (succ-ℕ m)
forward-is-left-adjoint-cofibonacci (succ-ℕ m) (succ-ℕ n) H =
  div-Fibonacci-div-ℕ
    ( succ-ℕ m)
    ( cofibonacci (succ-ℕ m))
    ( succ-ℕ n)
    ( H)
    ( pr2
      ( is-multiple-of-cofibonacci-cofibonacci
        ( succ-ℕ m)
        ( is-nonzero-succ-ℕ m)))

converse-is-left-adjoint-cofibonacci :
  (m n : ℕ) → div-ℕ m (Fibonacci-ℕ n) → div-ℕ (cofibonacci m) n
converse-is-left-adjoint-cofibonacci m n H = {!!}

is-left-adjoint-cofibonacci :
  (m n : ℕ) → div-ℕ (cofibonacci m) n ↔ div-ℕ m (Fibonacci-ℕ n)
is-left-adjoint-cofibonacci zero-ℕ n = {!!}
is-left-adjoint-cofibonacci (succ-ℕ m) n = {!!}
