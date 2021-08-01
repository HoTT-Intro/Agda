{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module extra.cofibonacci where

import book
open book public

{-------------------------------------------------------------------------------

  In this file we construct the cofibonacci sequence, which is the unique
  function G : ℕ → ℕ satisfying the property that
  
  div-ℕ (G m) n ↔ div-ℕ m (Fibonacci-ℕ n).

-------------------------------------------------------------------------------}

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
      ( refl-leq-ℕ (succ-ℕ (succ-ℕ k)))
      ( r))
... | inr g = {!!}

--------------------------------------------------------------------------------

-- We prove some basic properties of the Fibonacci sequence

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

-- We show that for every m : ℕ there is an x : ℕ such that m | F x

generating-map-Fibonacci-pair-mod-succ-ℕ :
  (k : ℕ) → Fin (succ-ℕ k) × Fin (succ-ℕ k) → Fin (succ-ℕ k) × Fin (succ-ℕ k)
generating-map-Fibonacci-pair-mod-succ-ℕ k p =
  pair (pr2 p) (add-Fin (pr2 p) (pr1 p))

inv-generating-map-Fibonacci-pair-mod-succ-ℕ :
  (k : ℕ) → Fin (succ-ℕ k) × Fin (succ-ℕ k) → Fin (succ-ℕ k) × Fin (succ-ℕ k)
inv-generating-map-Fibonacci-pair-mod-succ-ℕ k (pair x y) =
  pair (add-Fin y (neg-Fin x)) x

issec-inv-generating-map-Fibonacci-pair-mod-succ-ℕ :
  (k : ℕ) (p : Fin (succ-ℕ k) × Fin (succ-ℕ k)) →
  Id ( generating-map-Fibonacci-pair-mod-succ-ℕ k
       ( inv-generating-map-Fibonacci-pair-mod-succ-ℕ k p))
     ( p)
issec-inv-generating-map-Fibonacci-pair-mod-succ-ℕ k (pair x y) =
  ap-binary pair refl
    ( ( commutative-add-Fin x (add-Fin y (neg-Fin x))) ∙
      ( ( associative-add-Fin y (neg-Fin x) x) ∙
        ( ( ap (add-Fin y) (left-inverse-law-add-Fin x)) ∙
          ( right-unit-law-add-Fin y))))

isretr-inv-generating-map-Fibonacci-pair-mod-succ-ℕ :
  (k : ℕ ) (p : Fin (succ-ℕ k) × Fin (succ-ℕ k)) →
  Id ( inv-generating-map-Fibonacci-pair-mod-succ-ℕ k
       ( generating-map-Fibonacci-pair-mod-succ-ℕ k p))
     ( p)
isretr-inv-generating-map-Fibonacci-pair-mod-succ-ℕ k (pair x y) =
  ap-binary pair
    ( commutative-add-Fin (add-Fin y x) (neg-Fin y) ∙
      ( ( inv (associative-add-Fin (neg-Fin y) y x)) ∙
        ( ( ap (λ t → add-Fin t x) (left-inverse-law-add-Fin y)) ∙
          ( left-unit-law-add-Fin x))))
    ( refl)

Fibonacci-pair-mod-succ-ℕ :
  (k : ℕ) → ℕ → Fin (succ-ℕ k) × Fin (succ-ℕ k)
Fibonacci-pair-mod-succ-ℕ k zero-ℕ = pair zero-Fin one-Fin
Fibonacci-pair-mod-succ-ℕ k (succ-ℕ n) =
  generating-map-Fibonacci-pair-mod-succ-ℕ k (Fibonacci-pair-mod-succ-ℕ k n)

compute-Fibonacci-pair-mod-succ-ℕ :
  (k : ℕ) (n : ℕ) →
  Id ( Fibonacci-pair-mod-succ-ℕ k n)
     ( pair ( mod-succ-ℕ k (Fibonacci-ℕ n))
            ( mod-succ-ℕ k (Fibonacci-ℕ (succ-ℕ n))))
compute-Fibonacci-pair-mod-succ-ℕ k zero-ℕ = refl
compute-Fibonacci-pair-mod-succ-ℕ k (succ-ℕ zero-ℕ) =
  ap-binary pair refl (right-unit-law-add-Fin one-Fin)
compute-Fibonacci-pair-mod-succ-ℕ k (succ-ℕ (succ-ℕ n)) =
  ap-binary pair
    ( ap pr2 (compute-Fibonacci-pair-mod-succ-ℕ k (succ-ℕ n)))
    ( ( ap-binary add-Fin
        ( ap pr2 (compute-Fibonacci-pair-mod-succ-ℕ k (succ-ℕ n)))
        ( ap pr1 (compute-Fibonacci-pair-mod-succ-ℕ k (succ-ℕ n)))) ∙
      ( inv
        ( mod-succ-add-ℕ k
          ( Fibonacci-ℕ (succ-ℕ (succ-ℕ n)))
          ( Fibonacci-ℕ (succ-ℕ n)))))

-- Now we proceed with the construction of the cofibonacci sequence

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

fibonacci-multiple :
  (m : ℕ) → Σ ℕ (is-multiple-of-cofibonacci m)
fibonacci-multiple m = {!minimal-element-ℕ!}

least-multiple-of-cofibonacci :
  (m : ℕ) → minimal-element-ℕ (is-multiple-of-cofibonacci m)
least-multiple-of-cofibonacci m =
  well-ordering-principle-ℕ
    ( is-multiple-of-cofibonacci m)
    ( is-decidable-is-multiple-of-cofibonacci m)
    ( fibonacci-multiple m)

cofibonacci : ℕ → ℕ
cofibonacci m = pr1 (least-multiple-of-cofibonacci m)

is-multiple-of-cofibonacci-cofibonacci :
  (m : ℕ) → is-multiple-of-cofibonacci m (cofibonacci m)
is-multiple-of-cofibonacci-cofibonacci m =
  pr1 (pr2 (least-multiple-of-cofibonacci m))

is-least-multiple-of-cofibonacci-cofibonacci :
  (m x : ℕ) → is-multiple-of-cofibonacci m x → cofibonacci m ≤-ℕ x
is-least-multiple-of-cofibonacci-cofibonacci m =
  pr2 (pr2 (least-multiple-of-cofibonacci m))

is-zero-cofibonacci-zero-ℕ : is-zero-ℕ (cofibonacci zero-ℕ)
is-zero-cofibonacci-zero-ℕ =
  is-zero-leq-zero-ℕ
    ( cofibonacci zero-ℕ)
    ( is-least-multiple-of-cofibonacci-cofibonacci zero-ℕ zero-ℕ
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
forward-is-left-adjoint-cofibonacci (succ-ℕ m) (succ-ℕ n) H = {!!}
{-
  div-Fibonacci-div-ℕ m (cofibonacci m) n H
    {!is-multiple-!}
-}

is-left-adjoint-cofibonacci :
  (m n : ℕ) → div-ℕ (cofibonacci m) n ↔ div-ℕ m (Fibonacci-ℕ n)
is-left-adjoint-cofibonacci m n = {!!}
