{-# OPTIONS --without-K --exact-split --safe #-}

module book.07-finite-types where

import book.06-universes
open book.06-universes public

--------------------------------------------------------------------------------

{- Section 7.1 The congruence relations -}

{- Definition 7.1.1 -}

-- We introduce the divisibility relation. --

div-ℕ : ℕ → ℕ → UU lzero
div-ℕ m n = Σ ℕ (λ k → Id (mul-ℕ k m) n)

is-even-ℕ : ℕ → UU lzero
is-even-ℕ n = div-ℕ two-ℕ n

is-odd-ℕ : ℕ → UU lzero
is-odd-ℕ n = ¬ (is-even-ℕ n)

{- Remark 7.1.2 -}

div-one-ℕ :
  (x : ℕ) → div-ℕ one-ℕ x
div-one-ℕ x = pair x (right-unit-law-mul-ℕ x)

div-is-one-ℕ :
  (k x : ℕ) → is-one-ℕ k → div-ℕ k x
div-is-one-ℕ .one-ℕ x refl = div-one-ℕ x

div-zero-ℕ :
  (k : ℕ) → div-ℕ k zero-ℕ
div-zero-ℕ k = pair zero-ℕ (left-zero-law-mul-ℕ k)

div-is-zero-ℕ :
  (k x : ℕ) → is-zero-ℕ x → div-ℕ k x
div-is-zero-ℕ k .zero-ℕ refl = div-zero-ℕ k

{- Proposition 7.1.3 -}

{- In the following three constructions we show that if any two of the three
   numbers x, y, and x + y, is divisible by d, then so is the third. -}

div-add-ℕ :
  (d x y : ℕ) → div-ℕ d x → div-ℕ d y → div-ℕ d (add-ℕ x y)
div-add-ℕ d x y (pair n p) (pair m q) =
  pair
    ( add-ℕ n m)
    ( ( right-distributive-mul-add-ℕ n m d) ∙
      ( ap-add-ℕ p q))

div-left-summand-ℕ :
  (d x y : ℕ) → div-ℕ d y → div-ℕ d (add-ℕ x y) → div-ℕ d x
div-left-summand-ℕ zero-ℕ x y (pair m q) (pair n p) =
  pair zero-ℕ
    ( ( inv (right-zero-law-mul-ℕ n)) ∙
      ( p ∙ (ap (add-ℕ x) ((inv q) ∙ (right-zero-law-mul-ℕ m)))))
div-left-summand-ℕ (succ-ℕ d) x y (pair m q) (pair n p) =
  pair
    ( dist-ℕ m n)
    ( is-injective-add-ℕ' (mul-ℕ m (succ-ℕ d))
      ( ( inv
          ( ( right-distributive-mul-add-ℕ m (dist-ℕ m n) (succ-ℕ d)) ∙
            ( commutative-add-ℕ
              ( mul-ℕ m (succ-ℕ d))
              ( mul-ℕ (dist-ℕ m n) (succ-ℕ d))))) ∙ 
        ( ( ap
            ( mul-ℕ' (succ-ℕ d))
            ( leq-dist-ℕ m n
              ( leq-leq-mul-ℕ' m n d
                ( concatenate-eq-leq-eq-ℕ q
                  ( leq-add-ℕ' y x)
                  ( inv p))))) ∙
          ( p ∙ (ap (add-ℕ x) (inv q))))))

div-right-summand-ℕ :
  (d x y : ℕ) → div-ℕ d x → div-ℕ d (add-ℕ x y) → div-ℕ d y
div-right-summand-ℕ d x y H1 H2 =
  div-left-summand-ℕ d y x H1 (tr (div-ℕ d) (commutative-add-ℕ x y) H2)

{- Definition 7.1.4 -}

{- We define the congruence relation on ℕ and we do some bureaucracy that will
   help us in calculations involving the congruence relations. -}

cong-ℕ :
  ℕ → ℕ → ℕ → UU lzero
cong-ℕ k x y = div-ℕ k (dist-ℕ x y)

_≡_mod_ : ℕ → ℕ → ℕ → UU lzero
x ≡ y mod k = cong-ℕ k x y

concatenate-eq-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 x4 : ℕ} →
  Id x1 x2 → cong-ℕ k x2 x3 → Id x3 x4 → cong-ℕ k x1 x4
concatenate-eq-cong-eq-ℕ k refl H refl = H

concatenate-eq-cong-ℕ :
  (k : ℕ) {x1 x2 x3 : ℕ} →
  Id x1 x2 → cong-ℕ k x2 x3 → cong-ℕ k x1 x3
concatenate-eq-cong-ℕ k refl H = H

concatenate-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 : ℕ} →
  cong-ℕ k x1 x2 → Id x2 x3 → cong-ℕ k x1 x3
concatenate-cong-eq-ℕ k H refl = H

-- We show that cong-ℕ one-ℕ is the indiscrete equivalence relation --

is-indiscrete-cong-one-ℕ :
  (x y : ℕ) → cong-ℕ one-ℕ x y
is-indiscrete-cong-one-ℕ x y = div-one-ℕ (dist-ℕ x y)

-- We show that the congruence relation modulo 0 is discrete

is-discrete-cong-zero-ℕ :
  (x y : ℕ) → cong-ℕ zero-ℕ x y → Id x y
is-discrete-cong-zero-ℕ x y (pair k p) =
  eq-dist-ℕ x y ((inv p) ∙ (right-zero-law-mul-ℕ k))

{- Example 7.1.5 -}

cong-zero-ℕ :
  (k : ℕ) → cong-ℕ k k zero-ℕ
cong-zero-ℕ k =
  pair one-ℕ ((left-unit-law-mul-ℕ k) ∙ (inv (right-unit-law-dist-ℕ k)))

{- Proposition 7.1.6 -}

-- We show that cong-ℕ is an equivalence relation.

reflexive-cong-ℕ :
  (k x : ℕ) → cong-ℕ k x x
reflexive-cong-ℕ k x =
  pair zero-ℕ ((left-zero-law-mul-ℕ (succ-ℕ k)) ∙ (inv (dist-eq-ℕ x x refl)))

cong-identification-ℕ :
  (k : ℕ) {x y : ℕ} → Id x y → cong-ℕ k x y
cong-identification-ℕ k {x} refl = reflexive-cong-ℕ k x

symmetric-cong-ℕ :
  (k x y : ℕ) → cong-ℕ k x y → cong-ℕ k y x
symmetric-cong-ℕ k x y (pair d p) =
  pair d (p ∙ (symmetric-dist-ℕ x y))

cong-zero-ℕ' :
  (k : ℕ) → cong-ℕ k zero-ℕ k
cong-zero-ℕ' k =
  symmetric-cong-ℕ k k zero-ℕ (cong-zero-ℕ k)

{- Before we show that cong-ℕ is transitive, we give some lemmas that will help 
   us showing that cong is an equivalence relation. They are basically 
   bureaucracy, manipulating already known facts. -}

-- Three elements can be ordered in 6 possible ways

cases-order-three-elements-ℕ :
  (x y z : ℕ) → UU lzero
cases-order-three-elements-ℕ x y z =
  coprod
    ( coprod ((leq-ℕ x y) × (leq-ℕ y z)) ((leq-ℕ x z) × (leq-ℕ z y)))
    ( coprod
      ( coprod ((leq-ℕ y z) × (leq-ℕ z x)) ((leq-ℕ y x) × (leq-ℕ x z)))
      ( coprod ((leq-ℕ z x) × (leq-ℕ x y)) ((leq-ℕ z y) × (leq-ℕ y x))))

order-three-elements-ℕ :
  (x y z : ℕ) → cases-order-three-elements-ℕ x y z
order-three-elements-ℕ zero-ℕ zero-ℕ zero-ℕ = inl (inl (pair star star))
order-three-elements-ℕ zero-ℕ zero-ℕ (succ-ℕ z) = inl (inl (pair star star))
order-three-elements-ℕ zero-ℕ (succ-ℕ y) zero-ℕ = inl (inr (pair star star))
order-three-elements-ℕ zero-ℕ (succ-ℕ y) (succ-ℕ z) =
  inl (functor-coprod (pair star) (pair star) (decide-leq-ℕ y z))
order-three-elements-ℕ (succ-ℕ x) zero-ℕ zero-ℕ =
  inr (inl (inl (pair star star)))
order-three-elements-ℕ (succ-ℕ x) zero-ℕ (succ-ℕ z) =
  inr (inl (functor-coprod (pair star) (pair star) (decide-leq-ℕ z x)))
order-three-elements-ℕ (succ-ℕ x) (succ-ℕ y) zero-ℕ =
  inr (inr (functor-coprod (pair star) (pair star) (decide-leq-ℕ x y)))
order-three-elements-ℕ (succ-ℕ x) (succ-ℕ y) (succ-ℕ z) =
  order-three-elements-ℕ x y z

{- We show that the distances of any three elements always add up, when they
   are added up in the right way :) -} 

cases-dist-ℕ :
  (x y z : ℕ) → UU lzero
cases-dist-ℕ x y z = 
  coprod
    ( Id (add-ℕ (dist-ℕ x y) (dist-ℕ y z)) (dist-ℕ x z))
    ( coprod
      ( Id (add-ℕ (dist-ℕ y z) (dist-ℕ x z)) (dist-ℕ x y))
      ( Id (add-ℕ (dist-ℕ x z) (dist-ℕ x y)) (dist-ℕ y z)))

is-total-dist-ℕ :
  (x y z : ℕ) → cases-dist-ℕ x y z
is-total-dist-ℕ x y z with order-three-elements-ℕ x y z
is-total-dist-ℕ x y z | inl (inl (pair H1 H2)) =
  inl (triangle-equality-dist-ℕ x y z H1 H2)
is-total-dist-ℕ x y z | inl (inr (pair H1 H2)) = 
  inr
    ( inl
      ( ( commutative-add-ℕ (dist-ℕ y z) (dist-ℕ x z)) ∙
        ( ( ap (add-ℕ (dist-ℕ x z)) (symmetric-dist-ℕ y z)) ∙
          ( triangle-equality-dist-ℕ x z y H1 H2))))
is-total-dist-ℕ x y z | inr (inl (inl (pair H1 H2))) =
  inr
    ( inl
      ( ( ap (add-ℕ (dist-ℕ y z)) (symmetric-dist-ℕ x z)) ∙
        ( ( triangle-equality-dist-ℕ y z x H1 H2) ∙
          ( symmetric-dist-ℕ y x))))
is-total-dist-ℕ x y z | inr (inl (inr (pair H1 H2))) =
  inr
    ( inr
      ( ( ap (add-ℕ (dist-ℕ x z)) (symmetric-dist-ℕ x y)) ∙
        ( ( commutative-add-ℕ (dist-ℕ x z) (dist-ℕ y x)) ∙
          ( triangle-equality-dist-ℕ y x z H1 H2)))) 
is-total-dist-ℕ x y z | inr (inr (inl (pair H1 H2))) =
  inr
    ( inr
      ( ( ap (add-ℕ' (dist-ℕ x y)) (symmetric-dist-ℕ x z)) ∙
        ( ( triangle-equality-dist-ℕ z x y H1 H2) ∙
          ( symmetric-dist-ℕ z y))))
is-total-dist-ℕ x y z | inr (inr (inr (pair H1 H2))) =
  inl
    ( ( ap-add-ℕ (symmetric-dist-ℕ x y) (symmetric-dist-ℕ y z)) ∙
      ( ( commutative-add-ℕ (dist-ℕ y x) (dist-ℕ z y)) ∙
        ( ( triangle-equality-dist-ℕ z y x H1 H2) ∙
          ( symmetric-dist-ℕ z x))))

-- Finally, we show that cong-ℕ is transitive.

transitive-cong-ℕ :
  (k x y z : ℕ) →
  cong-ℕ k x y → cong-ℕ k y z → cong-ℕ k x z
transitive-cong-ℕ k x y z d e with is-total-dist-ℕ x y z
transitive-cong-ℕ k x y z d e | inl α =
  tr (div-ℕ k) α (div-add-ℕ k (dist-ℕ x y) (dist-ℕ y z) d e)
transitive-cong-ℕ k x y z d e | inr (inl α) =
  div-right-summand-ℕ k (dist-ℕ y z) (dist-ℕ x z) e (tr (div-ℕ k) (inv α) d)
transitive-cong-ℕ k x y z d e | inr (inr α) =
  div-left-summand-ℕ k (dist-ℕ x z) (dist-ℕ x y) d (tr (div-ℕ k) (inv α) e)

concatenate-cong-eq-cong-ℕ :
  {k x1 x2 x3 x4 : ℕ} →
  cong-ℕ k x1 x2 → Id x2 x3 → cong-ℕ k x3 x4 → cong-ℕ k x1 x4
concatenate-cong-eq-cong-ℕ {k} {x} {y} {.y} {z} H refl K =
  transitive-cong-ℕ k x y z H K
  
concatenate-eq-cong-eq-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 x4 x5 x6 : ℕ} →
  Id x1 x2 → cong-ℕ k x2 x3 → Id x3 x4 →
  cong-ℕ k x4 x5 → Id x5 x6 → cong-ℕ k x1 x6
concatenate-eq-cong-eq-cong-eq-ℕ k {x} {.x} {y} {.y} {z} {.z} refl H refl K refl =
  transitive-cong-ℕ k x y z H K

--------------------------------------------------------------------------------

{- Section 7.2 The finite types -}

{- Definition 7.2.1 -}

-- We introduce the finite types as a family indexed by ℕ.

Fin : ℕ → UU lzero
Fin zero-ℕ = empty
Fin (succ-ℕ k) = coprod (Fin k) unit

inl-Fin :
  (k : ℕ) → Fin k → Fin (succ-ℕ k)
inl-Fin k = inl

neg-one-Fin : {k : ℕ} → Fin (succ-ℕ k)
neg-one-Fin {k} = inr star

is-neg-one-Fin : {k : ℕ} → Fin k → UU lzero
is-neg-one-Fin {succ-ℕ k} x = Id x neg-one-Fin

{- Definition 7.2.4 -}

-- We define the inclusion of Fin k into ℕ.

nat-Fin : {k : ℕ} → Fin k → ℕ
nat-Fin {succ-ℕ k} (inl x) = nat-Fin x
nat-Fin {succ-ℕ k} (inr x) = k

{- Lemma 7.2.5 -}

-- We show that nat-Fin is bounded

strict-upper-bound-nat-Fin : {k : ℕ} (x : Fin k) → le-ℕ (nat-Fin x) k
strict-upper-bound-nat-Fin {succ-ℕ k} (inl x) =
  transitive-le-ℕ
    ( nat-Fin x)
    ( k)
    ( succ-ℕ k)
    ( strict-upper-bound-nat-Fin x)
    ( succ-le-ℕ k)
strict-upper-bound-nat-Fin {succ-ℕ k} (inr star) =
  succ-le-ℕ k

-- We also give a non-strict upper bound for convenience

upper-bound-nat-Fin : {k : ℕ} (x : Fin (succ-ℕ k)) → leq-ℕ (nat-Fin x) k
upper-bound-nat-Fin {zero-ℕ} (inr star) = star
upper-bound-nat-Fin {succ-ℕ k} (inl x) =
  preserves-leq-succ-ℕ (nat-Fin x) k (upper-bound-nat-Fin x)
upper-bound-nat-Fin {succ-ℕ k} (inr star) = reflexive-leq-ℕ (succ-ℕ k)

{- Proposition 7.2.6 -}

-- We show that nat-Fin is an injective function

neq-le-ℕ : {x y : ℕ} → le-ℕ x y → ¬ (Id x y)
neq-le-ℕ {zero-ℕ} {succ-ℕ y} H = Peano-8 y ∘ inv
neq-le-ℕ {succ-ℕ x} {succ-ℕ y} H p = neq-le-ℕ H (is-injective-succ-ℕ p)

is-injective-nat-Fin : {k : ℕ} → is-injective (nat-Fin {k})
is-injective-nat-Fin {succ-ℕ k} {inl x} {inl y} p =
  ap inl (is-injective-nat-Fin p)
is-injective-nat-Fin {succ-ℕ k} {inl x} {inr star} p =
  ex-falso (neq-le-ℕ (strict-upper-bound-nat-Fin x) p)
is-injective-nat-Fin {succ-ℕ k} {inr star} {inl y} p =
  ex-falso (neq-le-ℕ (strict-upper-bound-nat-Fin y) (inv p))
is-injective-nat-Fin {succ-ℕ k} {inr star} {inr star} p =
  refl

--------------------------------------------------------------------------------

{- Definition 7.3.1 -}

-- We define the zero element of Fin k.

zero-Fin : {k : ℕ} → Fin (succ-ℕ k)
zero-Fin {zero-ℕ} = inr star
zero-Fin {succ-ℕ k} = inl zero-Fin

is-zero-Fin : {k : ℕ} → Fin k → UU lzero
is-zero-Fin {succ-ℕ k} x = Id x zero-Fin

is-zero-Fin' : {k : ℕ} → Fin k → UU lzero
is-zero-Fin' {succ-ℕ k} x = Id zero-Fin x

is-nonzero-Fin : {k : ℕ} → Fin k → UU lzero
is-nonzero-Fin {succ-ℕ k} x = ¬ (is-zero-Fin x)

-- We define a function skip-zero-Fin in order to define succ-Fin.

skip-zero-Fin : {k : ℕ} → Fin k → Fin (succ-ℕ k)
skip-zero-Fin {succ-ℕ k} (inl x) = inl (skip-zero-Fin x)
skip-zero-Fin {succ-ℕ k} (inr star) = inr star

-- We define the successor function on Fin k.

succ-Fin : {k : ℕ} → Fin k → Fin k
succ-Fin {succ-ℕ k} (inl x) = skip-zero-Fin x
succ-Fin {succ-ℕ k} (inr star) = zero-Fin

{- Definition 7.3.2 -}

-- We define the modulo function

mod-succ-ℕ : (k : ℕ) → ℕ → Fin (succ-ℕ k)
mod-succ-ℕ k zero-ℕ = zero-Fin
mod-succ-ℕ k (succ-ℕ n) = succ-Fin (mod-succ-ℕ k n)

mod-two-ℕ : ℕ → Fin two-ℕ
mod-two-ℕ = mod-succ-ℕ one-ℕ

mod-three-ℕ : ℕ → Fin three-ℕ
mod-three-ℕ = mod-succ-ℕ two-ℕ

{- Lemma 7.3.3 -}

-- We prove three things to help calculating with nat-Fin.

nat-zero-Fin :
  {k : ℕ} → is-zero-ℕ (nat-Fin (zero-Fin {k}))
nat-zero-Fin {zero-ℕ} = refl 
nat-zero-Fin {succ-ℕ k} = nat-zero-Fin {k}

nat-skip-zero-Fin :
  {k : ℕ} (x : Fin k) → Id (nat-Fin (skip-zero-Fin x)) (succ-ℕ (nat-Fin x))
nat-skip-zero-Fin {succ-ℕ k} (inl x) = nat-skip-zero-Fin x
nat-skip-zero-Fin {succ-ℕ k} (inr star) = refl

nat-succ-Fin :
  {k : ℕ} (x : Fin k) → Id (nat-Fin (succ-Fin (inl x))) (succ-ℕ (nat-Fin x))
nat-succ-Fin {k} x = nat-skip-zero-Fin x

cong-nat-succ-Fin :
  (k : ℕ) (x : Fin k) → cong-ℕ k (nat-Fin (succ-Fin x)) (succ-ℕ (nat-Fin x))
cong-nat-succ-Fin (succ-ℕ k) (inl x) =
  cong-identification-ℕ
    ( succ-ℕ k)
    { nat-Fin (succ-Fin (inl x))}
    { succ-ℕ (nat-Fin x)}
    ( nat-succ-Fin x)
cong-nat-succ-Fin (succ-ℕ k) (inr star) =
  concatenate-eq-cong-ℕ
    ( succ-ℕ k)
    { nat-Fin {succ-ℕ k} zero-Fin}
    { zero-ℕ}
    { succ-ℕ k}
    ( nat-zero-Fin {k})
    ( cong-zero-ℕ' (succ-ℕ k))

{- Proposition 7.3.4 -}

-- We show that (nat-Fin (mod-succ-ℕ n x)) is congruent to x modulo n+1. --

cong-nat-mod-succ-ℕ :
  (k x : ℕ) → cong-ℕ (succ-ℕ k) (nat-Fin (mod-succ-ℕ k x)) x
cong-nat-mod-succ-ℕ k zero-ℕ =
  cong-identification-ℕ (succ-ℕ k) (nat-zero-Fin {k})
cong-nat-mod-succ-ℕ k (succ-ℕ x) =
  transitive-cong-ℕ
    ( succ-ℕ k)
    ( nat-Fin (mod-succ-ℕ k (succ-ℕ x)))
    ( succ-ℕ (nat-Fin (mod-succ-ℕ k x)))
    ( succ-ℕ x)
    ( cong-nat-succ-Fin (succ-ℕ k) (mod-succ-ℕ k x) )
    ( cong-nat-mod-succ-ℕ k x)

{- Proposition 7.3.5 -}

is-zero-div-ℕ :
  (d x : ℕ) → le-ℕ x d → div-ℕ d x → is-zero-ℕ x
is-zero-div-ℕ d zero-ℕ H D = refl
is-zero-div-ℕ d (succ-ℕ x) H (pair (succ-ℕ k) p) =
  ex-falso
    ( contradiction-le-ℕ
      ( succ-ℕ x) d H
      ( concatenate-leq-eq-ℕ d
        ( leq-add-ℕ' d (mul-ℕ k d)) p))

eq-cong-le-dist-ℕ :
  (k x y : ℕ) → le-ℕ (dist-ℕ x y) k → cong-ℕ k x y → Id x y
eq-cong-le-dist-ℕ k x y H K =
  eq-dist-ℕ x y (is-zero-div-ℕ k (dist-ℕ x y) H K)

strict-upper-bound-dist-ℕ :
  (b x y : ℕ) → le-ℕ x b → le-ℕ y b → le-ℕ (dist-ℕ x y) b
strict-upper-bound-dist-ℕ (succ-ℕ b) zero-ℕ y H K = K
strict-upper-bound-dist-ℕ (succ-ℕ b) (succ-ℕ x) zero-ℕ H K = H
strict-upper-bound-dist-ℕ (succ-ℕ b) (succ-ℕ x) (succ-ℕ y) H K =
  preserves-le-succ-ℕ (dist-ℕ x y) b (strict-upper-bound-dist-ℕ b x y H K)

eq-cong-le-ℕ :
  (k x y : ℕ) → le-ℕ x k → le-ℕ y k → cong-ℕ k x y → Id x y
eq-cong-le-ℕ k x y H K =
  eq-cong-le-dist-ℕ k x y (strict-upper-bound-dist-ℕ k x y H K)

{- Theorem 7.3.6 -}

{- We show that if mod-succ-ℕ k x = mod-succ-ℕ k y, then x and y must be
   congruent modulo succ-ℕ n. This is the forward direction of the theorm. -}

cong-eq-ℕ :
  (k x y : ℕ) → Id (mod-succ-ℕ k x) (mod-succ-ℕ k y) → cong-ℕ (succ-ℕ k) x y
cong-eq-ℕ k x y p =
  concatenate-cong-eq-cong-ℕ {succ-ℕ k} {x}
    ( symmetric-cong-ℕ (succ-ℕ k) (nat-Fin (mod-succ-ℕ k x)) x
      ( cong-nat-mod-succ-ℕ k x))
    ( ap nat-Fin p)
    ( cong-nat-mod-succ-ℕ k y)

eq-cong-nat-Fin :
  (k : ℕ) (x y : Fin k) → cong-ℕ k (nat-Fin x) (nat-Fin y) → Id x y
eq-cong-nat-Fin (succ-ℕ k) x y H =
  is-injective-nat-Fin
    ( eq-cong-le-ℕ (succ-ℕ k) (nat-Fin x) (nat-Fin y)
      ( strict-upper-bound-nat-Fin x)
      ( strict-upper-bound-nat-Fin y)
      ( H))

eq-cong-ℕ :
  (k x y : ℕ) → cong-ℕ (succ-ℕ k) x y → Id (mod-succ-ℕ k x) (mod-succ-ℕ k y)
eq-cong-ℕ k x y H =
  eq-cong-nat-Fin
    ( succ-ℕ k)
    ( mod-succ-ℕ k x)
    ( mod-succ-ℕ k y)
    ( transitive-cong-ℕ
      ( succ-ℕ k)
      ( nat-Fin (mod-succ-ℕ k x))
      ( x)
      ( nat-Fin (mod-succ-ℕ k y))
      ( cong-nat-mod-succ-ℕ k x)
      ( transitive-cong-ℕ (succ-ℕ k) x y (nat-Fin (mod-succ-ℕ k y)) H
        ( symmetric-cong-ℕ (succ-ℕ k) (nat-Fin (mod-succ-ℕ k y)) y
          ( cong-nat-mod-succ-ℕ k y))))

-- We record some immediate corollaries

eq-zero-div-succ-ℕ :
  (k x : ℕ) → div-ℕ (succ-ℕ k) x → is-zero-Fin (mod-succ-ℕ k x)
eq-zero-div-succ-ℕ k x d =
  eq-cong-ℕ k x zero-ℕ
    ( tr (div-ℕ (succ-ℕ k)) (inv (right-unit-law-dist-ℕ x)) d)

div-succ-eq-zero-ℕ :
  (k x : ℕ) → is-zero-Fin (mod-succ-ℕ k x) → div-ℕ (succ-ℕ k) x
div-succ-eq-zero-ℕ k x p =
  tr (div-ℕ (succ-ℕ k)) (right-unit-law-dist-ℕ x) (cong-eq-ℕ k x zero-ℕ p)

{- Theorem 7.3.7 -}

issec-nat-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mod-succ-ℕ k (nat-Fin x)) x
issec-nat-Fin {k} x =
  is-injective-nat-Fin
    ( eq-cong-le-ℕ
      ( succ-ℕ k)
      ( nat-Fin (mod-succ-ℕ k (nat-Fin x)))
      ( nat-Fin x)
      ( strict-upper-bound-nat-Fin (mod-succ-ℕ k (nat-Fin x)))
      ( strict-upper-bound-nat-Fin x)
      ( cong-nat-mod-succ-ℕ k (nat-Fin x)))

--------------------------------------------------------------------------------

{- Section 7.4 The cyclic group structure on the finite types -}

{- Definition 7.4.1 -}

-- Addition on finite sets --

add-Fin : {k : ℕ} → Fin k → Fin k → Fin k
add-Fin {succ-ℕ k} x y = mod-succ-ℕ k (add-ℕ (nat-Fin x) (nat-Fin y))

add-Fin' : {k : ℕ} → Fin k → Fin k → Fin k
add-Fin' x y = add-Fin y x

-- We define an action on paths of add-Fin on the two arguments at once.

ap-add-Fin :
  {k : ℕ} {x y x' y' : Fin k} →
  Id x x' → Id y y' → Id (add-Fin x y) (add-Fin x' y')
ap-add-Fin refl refl = refl

-- The negative of an element of Fin k --

neg-Fin :
  {k : ℕ} → Fin k → Fin k
neg-Fin {succ-ℕ k} x =
  mod-succ-ℕ k (dist-ℕ (nat-Fin x) (succ-ℕ k))

{- Remark 7.4.2 -}

cong-nat-zero-Fin :
  {k : ℕ} → cong-ℕ (succ-ℕ k) (nat-Fin (zero-Fin {k})) zero-ℕ
cong-nat-zero-Fin {k} = cong-nat-mod-succ-ℕ k zero-ℕ

cong-add-Fin :
  {k : ℕ} (x y : Fin k) →
  cong-ℕ k (nat-Fin (add-Fin x y)) (add-ℕ (nat-Fin x) (nat-Fin y))
cong-add-Fin {succ-ℕ k} x y =
  cong-nat-mod-succ-ℕ k (add-ℕ (nat-Fin x) (nat-Fin y))

cong-neg-Fin :
  {k : ℕ} (x : Fin k) →
  cong-ℕ k (nat-Fin (neg-Fin x)) (dist-ℕ (nat-Fin x) k)
cong-neg-Fin {succ-ℕ k} x = 
  cong-nat-mod-succ-ℕ k (dist-ℕ (nat-Fin x) (succ-ℕ k))

{- Proposition 7.4.3 -}

-- We show that congruence is translation invariant --

translation-invariant-cong-ℕ :
  (k x y z : ℕ) → cong-ℕ k x y → cong-ℕ k (add-ℕ z x) (add-ℕ z y)
translation-invariant-cong-ℕ k x y z (pair d p) =
  pair d (p ∙ inv (translation-invariant-dist-ℕ z x y))

translation-invariant-cong-ℕ' :
  (k x y z : ℕ) → cong-ℕ k x y → cong-ℕ k (add-ℕ x z) (add-ℕ y z)
translation-invariant-cong-ℕ' k x y z H =
  concatenate-eq-cong-eq-ℕ k
    ( commutative-add-ℕ x z)
    ( translation-invariant-cong-ℕ k x y z H)
    ( commutative-add-ℕ z y)

step-invariant-cong-ℕ :
  (k x y : ℕ) → cong-ℕ k x y → cong-ℕ k (succ-ℕ x) (succ-ℕ y)
step-invariant-cong-ℕ k x y = translation-invariant-cong-ℕ' k x y one-ℕ

-- We show that addition respects the congruence relation --

congruence-add-ℕ :
  (k : ℕ) {x y x' y' : ℕ} →
  cong-ℕ k x x' → cong-ℕ k y y' → cong-ℕ k (add-ℕ x y) (add-ℕ x' y')
congruence-add-ℕ k {x} {y} {x'} {y'} H K =
  transitive-cong-ℕ k (add-ℕ x y) (add-ℕ x y') (add-ℕ x' y')
    ( translation-invariant-cong-ℕ k y y' x K)
    ( translation-invariant-cong-ℕ' k x x' y' H)

{- Theorem 7.4.4 -}

-- We show that addition is commutative --

commutative-add-Fin : {k : ℕ} (x y : Fin k) → Id (add-Fin x y) (add-Fin y x)
commutative-add-Fin {succ-ℕ k} x y =
  ap (mod-succ-ℕ k) (commutative-add-ℕ (nat-Fin x) (nat-Fin y))

-- We show that addition is associative --

associative-add-Fin :
  {k : ℕ} (x y z : Fin k) →
  Id (add-Fin (add-Fin x y) z) (add-Fin x (add-Fin y z))
associative-add-Fin {succ-ℕ k} x y z =
  eq-cong-ℕ k
    ( add-ℕ (nat-Fin (add-Fin x y)) (nat-Fin z))
    ( add-ℕ (nat-Fin x) (nat-Fin (add-Fin y z)))
    ( concatenate-cong-eq-cong-ℕ
      { x1 = add-ℕ (nat-Fin (add-Fin x y)) (nat-Fin z)}
      { x2 = add-ℕ (add-ℕ (nat-Fin x) (nat-Fin y)) (nat-Fin z)}
      { x3 = add-ℕ (nat-Fin x) (add-ℕ (nat-Fin y) (nat-Fin z))}
      { x4 = add-ℕ (nat-Fin x) (nat-Fin (add-Fin y z))}
      ( congruence-add-ℕ
        ( succ-ℕ k)
        { x = nat-Fin (add-Fin x y)}
        { y = nat-Fin z}
        { x' = add-ℕ (nat-Fin x) (nat-Fin y)}
        { y' = nat-Fin z}
        ( cong-add-Fin x y)
        ( reflexive-cong-ℕ (succ-ℕ k) (nat-Fin z)))
      ( associative-add-ℕ (nat-Fin x) (nat-Fin y) (nat-Fin z))
      ( congruence-add-ℕ
        ( succ-ℕ k)
        { x = nat-Fin x}
        { y = add-ℕ (nat-Fin y) (nat-Fin z)}
        { x' = nat-Fin x}
        { y' = nat-Fin (add-Fin y z)}
        ( reflexive-cong-ℕ (succ-ℕ k) (nat-Fin x))
        ( symmetric-cong-ℕ
          ( succ-ℕ k)
          ( nat-Fin (add-Fin y z))
          ( add-ℕ (nat-Fin y) (nat-Fin z))
          ( cong-add-Fin y z))))

-- We show that addition satisfies the right unit law --

right-unit-law-add-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (add-Fin x zero-Fin) x
right-unit-law-add-Fin {k} x =
  ( eq-cong-ℕ k
    ( add-ℕ (nat-Fin x) (nat-Fin {succ-ℕ k} zero-Fin))
    ( add-ℕ (nat-Fin x) zero-ℕ)
    ( congruence-add-ℕ
      ( succ-ℕ k)
      { x = nat-Fin {succ-ℕ k} x}
      { y = nat-Fin {succ-ℕ k} zero-Fin}
      { x' = nat-Fin x}
      { y' = zero-ℕ}
      ( reflexive-cong-ℕ (succ-ℕ k) (nat-Fin {succ-ℕ k} x))
      ( cong-nat-zero-Fin {k}))) ∙
  ( issec-nat-Fin x)

left-unit-law-add-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (add-Fin zero-Fin x) x
left-unit-law-add-Fin {k} x =
  ( commutative-add-Fin zero-Fin x) ∙
  ( right-unit-law-add-Fin x)

-- We show that addition satisfies the left inverse law --

left-inverse-law-add-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → is-zero-Fin (add-Fin (neg-Fin x) x)
left-inverse-law-add-Fin {k} x =
  eq-cong-ℕ k
    ( add-ℕ (nat-Fin (neg-Fin x)) (nat-Fin x))
    ( zero-ℕ)
    ( concatenate-cong-eq-cong-ℕ
      { succ-ℕ k}
      { x1 = add-ℕ (nat-Fin (neg-Fin x)) (nat-Fin x)}
      { x2 = add-ℕ (dist-ℕ (nat-Fin x) (succ-ℕ k)) (nat-Fin x)}
      { x3 = succ-ℕ k}
      { x4 = zero-ℕ}
      ( translation-invariant-cong-ℕ' (succ-ℕ k)
        ( nat-Fin (neg-Fin x))
        ( dist-ℕ (nat-Fin x) (succ-ℕ k))
        ( nat-Fin x)
        ( cong-neg-Fin x))
      ( is-difference-dist-ℕ' (nat-Fin x) (succ-ℕ k)
        ( upper-bound-nat-Fin (inl x)))
      ( cong-zero-ℕ' (succ-ℕ k)))

right-inverse-law-add-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → is-zero-Fin (add-Fin x (neg-Fin x))
right-inverse-law-add-Fin x =
  ( commutative-add-Fin x (neg-Fin x)) ∙ (left-inverse-law-add-Fin x)

{- Definition 7.4.5 -}

iterate : {l : Level} {X : UU l} → ℕ → (X → X) → (X → X)
iterate zero-ℕ f x = x
iterate (succ-ℕ k) f x = f (iterate k f x)

iterate-succ-ℕ :
  {l : Level} {X : UU l} (k : ℕ) (f : X → X) (x : X) →
  Id (iterate (succ-ℕ k) f x) (iterate k f (f x))
iterate-succ-ℕ zero-ℕ f x = refl
iterate-succ-ℕ (succ-ℕ k) f x = ap f (iterate-succ-ℕ k f x)

iterate-add-ℕ :
  {l : Level} {X : UU l} (k l : ℕ) (f : X → X) (x : X) →
  Id (iterate (add-ℕ k l) f x) (iterate k f (iterate l f x))
iterate-add-ℕ k zero-ℕ f x = refl
iterate-add-ℕ k (succ-ℕ l) f x =
  ap f (iterate-add-ℕ k l f x) ∙ iterate-succ-ℕ k f (iterate l f x)

iterate-iterate :
  {l : Level} {X : UU l} (k l : ℕ) (f : X → X) (x : X) →
  Id (iterate k f (iterate l f x)) (iterate l f (iterate k f x))
iterate-iterate k l f x =
  ( inv (iterate-add-ℕ k l f x)) ∙
  ( ( ap (λ t → iterate t f x) (commutative-add-ℕ k l)) ∙
    ( iterate-add-ℕ l k f x))

is-cyclic-map : {l : Level} {X : UU l} (f : X → X) → UU l
is-cyclic-map {l} {X} f = (x y : X) → Σ ℕ (λ k → Id (iterate k f x) y)

length-path-is-cyclic-map :
  {l : Level} {X : UU l} {f : X → X} → is-cyclic-map f → X → X → ℕ
length-path-is-cyclic-map H x y = pr1 (H x y)

eq-is-cyclic-map :
  {l : Level} {X : UU l} {f : X → X} (H : is-cyclic-map f) (x y : X) →
  Id (iterate (length-path-is-cyclic-map H x y) f x) y
eq-is-cyclic-map H x y = pr2 (H x y)

--------------------------------------------------------------------------------

{- Exercises -}

{- Exercise 7.1 -}

-- See Proposition 7.1.3

{- Exercise 7.2 -}

-- We show that the divisibility relation is a poset

refl-div-ℕ : (x : ℕ) → div-ℕ x x
refl-div-ℕ x = pair one-ℕ (left-unit-law-mul-ℕ x)

anti-symmetric-div-ℕ :
  (x y : ℕ) → div-ℕ x y → div-ℕ y x → Id x y
anti-symmetric-div-ℕ zero-ℕ zero-ℕ H K = refl
anti-symmetric-div-ℕ zero-ℕ (succ-ℕ y) (pair k p) K =
  inv (right-zero-law-mul-ℕ k) ∙ p
anti-symmetric-div-ℕ (succ-ℕ x) zero-ℕ H (pair l q) =
  inv q ∙ right-zero-law-mul-ℕ l
anti-symmetric-div-ℕ (succ-ℕ x) (succ-ℕ y) (pair k p) (pair l q) =
  ( inv (left-unit-law-mul-ℕ (succ-ℕ x))) ∙
  ( ( ap ( mul-ℕ' (succ-ℕ x))
         ( inv
           ( is-one-right-is-one-mul-ℕ l k
             ( is-one-is-left-unit-mul-ℕ (mul-ℕ l k) x
               ( ( associative-mul-ℕ l k (succ-ℕ x)) ∙
                 ( ap (mul-ℕ l) p ∙ q)))))) ∙
    ( p))

transitive-div-ℕ :
  (x y z : ℕ) → div-ℕ x y → div-ℕ y z → div-ℕ x z
transitive-div-ℕ x y z (pair k p) (pair l q) =
  pair ( mul-ℕ l k)
       ( associative-mul-ℕ l k x ∙ (ap (mul-ℕ l) p ∙ q))

div-mul-ℕ :
  (k x y : ℕ) → div-ℕ x y → div-ℕ x (mul-ℕ k y)
div-mul-ℕ k x y H =
  transitive-div-ℕ x y (mul-ℕ k y) H (pair k refl)

-- We conclude that 0 | x implies x = 0 and x | 1 implies x = 1.

is-zero-div-zero-ℕ : (x : ℕ) → div-ℕ zero-ℕ x → is-zero-ℕ x
is-zero-div-zero-ℕ x H = anti-symmetric-div-ℕ x zero-ℕ (div-zero-ℕ x) H

is-zero-is-zero-div-ℕ : (x y : ℕ) → div-ℕ x y → is-zero-ℕ x → is-zero-ℕ y
is-zero-is-zero-div-ℕ .zero-ℕ y d refl = is-zero-div-zero-ℕ y d

is-one-div-one-ℕ : (x : ℕ) → div-ℕ x one-ℕ → is-one-ℕ x
is-one-div-one-ℕ x H = anti-symmetric-div-ℕ x one-ℕ H (div-one-ℕ x)

is-one-div-ℕ : (x y : ℕ) → div-ℕ x y → div-ℕ x (succ-ℕ y) → is-one-ℕ x
is-one-div-ℕ x y H K = is-one-div-one-ℕ x (div-right-summand-ℕ x y one-ℕ H K)

div-eq-ℕ : (x y : ℕ) → Id x y → div-ℕ x y
div-eq-ℕ x .x refl = refl-div-ℕ x

{- Exercise 7.3 -}

div-factorial-is-nonzero-ℕ :
  (n x : ℕ) → leq-ℕ x n → is-nonzero-ℕ x → div-ℕ x (factorial-ℕ n)
div-factorial-is-nonzero-ℕ zero-ℕ zero-ℕ l H = ex-falso (H refl)
div-factorial-is-nonzero-ℕ (succ-ℕ n) x l H with
  decide-leq-succ-ℕ x n l
... | inl l' =
  transitive-div-ℕ x
    ( factorial-ℕ n)
    ( factorial-ℕ (succ-ℕ n))
    ( div-factorial-is-nonzero-ℕ n x l' H)
    ( pair (succ-ℕ n) (commutative-mul-ℕ (succ-ℕ n) (factorial-ℕ n)))
... | inr refl = pair (factorial-ℕ n) refl

{- Exercise 7.4 -}

-- We introduce the observational equality on finite sets.

Eq-Fin : (k : ℕ) → Fin k → Fin k → UU lzero
Eq-Fin (succ-ℕ k) (inl x) (inl y) = Eq-Fin k x y
Eq-Fin (succ-ℕ k) (inl x) (inr y) = empty
Eq-Fin (succ-ℕ k) (inr x) (inl y) = empty
Eq-Fin (succ-ℕ k) (inr x) (inr y) = unit

-- Exercise 7.4 (a)

refl-Eq-Fin : {k : ℕ} (x : Fin k) → Eq-Fin k x x
refl-Eq-Fin {succ-ℕ k} (inl x) = refl-Eq-Fin x
refl-Eq-Fin {succ-ℕ k} (inr x) = star

Eq-Fin-eq : {k : ℕ} {x y : Fin k} → Id x y → Eq-Fin k x y
Eq-Fin-eq {k} refl = refl-Eq-Fin {k} _

eq-Eq-Fin :
  {k : ℕ} {x y : Fin k} → Eq-Fin k x y → Id x y
eq-Eq-Fin {succ-ℕ k} {inl x} {inl y} e = ap inl (eq-Eq-Fin e)
eq-Eq-Fin {succ-ℕ k} {inr star} {inr star} star = refl

-- Exercise 7.4 (b)

is-injective-inl-Fin : {k : ℕ} → is-injective (inl-Fin k)
is-injective-inl-Fin p = eq-Eq-Fin (Eq-Fin-eq p)

-- Exercise 7.4 (c)

neq-zero-succ-Fin :
  {k : ℕ} {x : Fin k} → is-nonzero-Fin (succ-Fin (inl-Fin k x))
neq-zero-succ-Fin {succ-ℕ k} {inl x} p =
  neq-zero-succ-Fin (is-injective-inl-Fin p)
neq-zero-succ-Fin {succ-ℕ k} {inr star} p =
  Eq-Fin-eq {succ-ℕ (succ-ℕ k)} {inr star} {zero-Fin} p

-- Exercise 7.4 (d)

is-injective-skip-zero-Fin : {k : ℕ} → is-injective (skip-zero-Fin {k})
is-injective-skip-zero-Fin {succ-ℕ k} {inl x} {inl y} p =
  ap inl (is-injective-skip-zero-Fin (is-injective-inl-Fin p))
is-injective-skip-zero-Fin {succ-ℕ k} {inl x} {inr star} p =
  ex-falso (Eq-Fin-eq p)
is-injective-skip-zero-Fin {succ-ℕ k} {inr star} {inl y} p =
  ex-falso (Eq-Fin-eq p)
is-injective-skip-zero-Fin {succ-ℕ k} {inr star} {inr star} p = refl

is-injective-succ-Fin : {k : ℕ} → is-injective (succ-Fin {k})
is-injective-succ-Fin {succ-ℕ k} {inl x} {inl y} p =
  ap inl (is-injective-skip-zero-Fin {k} {x} {y} p)
is-injective-succ-Fin {succ-ℕ k} {inl x} {inr star} p =
  ex-falso (neq-zero-succ-Fin {succ-ℕ k} {inl x} (ap inl p))
is-injective-succ-Fin {succ-ℕ k} {inr star} {inl y} p =
  ex-falso (neq-zero-succ-Fin {succ-ℕ k} {inl y} (ap inl (inv p)))
is-injective-succ-Fin {succ-ℕ k} {inr star} {inr star} p = refl

{- Exercise 7.5 -}

-- We define the negative two element of Fin k.

neg-two-Fin :
  {k : ℕ} → Fin (succ-ℕ k)
neg-two-Fin {zero-ℕ} = inr star
neg-two-Fin {succ-ℕ k} = inl (inr star)

-- We define a function skip-neg-two-Fin in order to define pred-Fin.

skip-neg-two-Fin :
  {k : ℕ} → Fin k → Fin (succ-ℕ k)
skip-neg-two-Fin {succ-ℕ k} (inl x) = inl (inl x)
skip-neg-two-Fin {succ-ℕ k} (inr x) = neg-one-Fin {succ-ℕ k}

-- We define the predecessor function on Fin k.

pred-Fin : {k : ℕ} → Fin k → Fin k
pred-Fin {succ-ℕ k} (inl x) = skip-neg-two-Fin (pred-Fin x)
pred-Fin {succ-ℕ k} (inr x) = neg-two-Fin

-- We now turn to the exercise.

pred-zero-Fin :
  {k : ℕ} → is-neg-one-Fin (pred-Fin {succ-ℕ k} zero-Fin)
pred-zero-Fin {zero-ℕ} = refl
pred-zero-Fin {succ-ℕ k} = ap skip-neg-two-Fin (pred-zero-Fin {k})

succ-skip-neg-two-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) →
  Id (succ-Fin (skip-neg-two-Fin x)) (inl (succ-Fin x))
succ-skip-neg-two-Fin {zero-ℕ} (inr star) = refl
succ-skip-neg-two-Fin {succ-ℕ k} (inl x) = refl
succ-skip-neg-two-Fin {succ-ℕ k} (inr star) = refl

succ-pred-Fin :
  {k : ℕ} (x : Fin k) → Id (succ-Fin (pred-Fin x)) x
succ-pred-Fin {succ-ℕ zero-ℕ} (inr star) = refl
succ-pred-Fin {succ-ℕ (succ-ℕ k)} (inl x) =
  succ-skip-neg-two-Fin (pred-Fin x) ∙ ap inl (succ-pred-Fin x)
succ-pred-Fin {succ-ℕ (succ-ℕ k)} (inr star) = refl

pred-succ-Fin :
  {k : ℕ} (x : Fin k) → Id (pred-Fin (succ-Fin x)) x
pred-succ-Fin {succ-ℕ zero-ℕ} (inr star) = refl
pred-succ-Fin {succ-ℕ (succ-ℕ k)} (inl (inl x)) =
  ap skip-neg-two-Fin (pred-succ-Fin (inl x))
pred-succ-Fin {succ-ℕ (succ-ℕ k)} (inl (inr star)) = refl
pred-succ-Fin {succ-ℕ (succ-ℕ k)} (inr star) = pred-zero-Fin

{- Exercise 7.6 -}

fin-bounded-nat :
  {k : ℕ} → Σ ℕ (λ x → le-ℕ x k) → Fin k
fin-bounded-nat {succ-ℕ k} (pair x H) = mod-succ-ℕ k x

bounded-nat-Fin :
  {k : ℕ} → Fin k → Σ ℕ (λ x → le-ℕ x k)
bounded-nat-Fin {k} x = pair (nat-Fin x) (strict-upper-bound-nat-Fin x)

-- We still need to construct the identifications stated in the exercise

{- Exercise 7.7 -}

{- We define the multiplication on the types Fin k. -}

mul-Fin :
  {k : ℕ} → Fin k → Fin k → Fin k
mul-Fin {succ-ℕ k} x y = mod-succ-ℕ k (mul-ℕ (nat-Fin x) (nat-Fin y))

ap-mul-Fin :
  {k : ℕ} {x y x' y' : Fin k} →
  Id x x' → Id y y' → Id (mul-Fin x y) (mul-Fin x' y')
ap-mul-Fin refl refl = refl

-- Exercise 7.7 (a)

cong-mul-Fin :
  {k : ℕ} (x y : Fin k) →
  cong-ℕ k (nat-Fin (mul-Fin x y)) (mul-ℕ (nat-Fin x) (nat-Fin y))
cong-mul-Fin {succ-ℕ k} x y =
  cong-nat-mod-succ-ℕ k (mul-ℕ (nat-Fin x) (nat-Fin y))

-- Exercise 7.7 (b)

-- We show that congruence is invariant under scalar multiplication --

scalar-invariant-cong-ℕ :
  (k x y z : ℕ) → cong-ℕ k x y →  cong-ℕ k (mul-ℕ z x) (mul-ℕ z y)
scalar-invariant-cong-ℕ k x y z (pair d p) =
  pair
    ( mul-ℕ z d)
    ( ( associative-mul-ℕ z d k) ∙
      ( ( ap (mul-ℕ z) p) ∙
        ( inv (linear-dist-ℕ x y z))))

scalar-invariant-cong-ℕ' :
  (k x y z : ℕ) → cong-ℕ k x y → cong-ℕ k (mul-ℕ x z) (mul-ℕ y z)
scalar-invariant-cong-ℕ' k x y z H =
  concatenate-eq-cong-eq-ℕ k
    ( commutative-mul-ℕ x z)
    ( scalar-invariant-cong-ℕ k x y z H)
    ( commutative-mul-ℕ z y)

-- We show that multiplication respects the congruence relation --

congruence-mul-ℕ :
  (k : ℕ) {x y x' y' : ℕ} →
  cong-ℕ  k x x' → cong-ℕ k y y' → cong-ℕ k (mul-ℕ x y) (mul-ℕ x' y')
congruence-mul-ℕ k {x} {y} {x'} {y'} H K =
  transitive-cong-ℕ k (mul-ℕ x y) (mul-ℕ x y') (mul-ℕ x' y')
    ( scalar-invariant-cong-ℕ k y y' x K)
    ( scalar-invariant-cong-ℕ' k x x' y' H)

-- Exercise 7.7 (c)

associative-mul-Fin :
  {k : ℕ} (x y z : Fin k) →
  Id (mul-Fin (mul-Fin x y) z) (mul-Fin x (mul-Fin y z))
associative-mul-Fin {succ-ℕ k} x y z =
  eq-cong-ℕ k
    ( mul-ℕ (nat-Fin (mul-Fin x y)) (nat-Fin z))
    ( mul-ℕ (nat-Fin x) (nat-Fin (mul-Fin y z)))
    ( concatenate-cong-eq-cong-ℕ
      { x1 = mul-ℕ (nat-Fin (mul-Fin x y)) (nat-Fin z)}
      { x2 = mul-ℕ (mul-ℕ (nat-Fin x) (nat-Fin y)) (nat-Fin z)}
      { x3 = mul-ℕ (nat-Fin x) (mul-ℕ (nat-Fin y) (nat-Fin z))}
      { x4 = mul-ℕ (nat-Fin x) (nat-Fin (mul-Fin y z))}
      ( congruence-mul-ℕ
        ( succ-ℕ k)
        { x = nat-Fin (mul-Fin x y)}
        { y = nat-Fin z}
        ( cong-mul-Fin x y)
        ( reflexive-cong-ℕ (succ-ℕ k) (nat-Fin z)))
      ( associative-mul-ℕ (nat-Fin x) (nat-Fin y) (nat-Fin z))
      ( symmetric-cong-ℕ
        ( succ-ℕ k)
        ( mul-ℕ (nat-Fin x) (nat-Fin (mul-Fin y z)))
        ( mul-ℕ (nat-Fin x) (mul-ℕ (nat-Fin y) (nat-Fin z)))
        ( congruence-mul-ℕ
          ( succ-ℕ k)
          { x = nat-Fin x}
          { y = nat-Fin (mul-Fin y z)}
          ( reflexive-cong-ℕ (succ-ℕ k) (nat-Fin x))
          ( cong-mul-Fin y z))))

commutative-mul-Fin :
  {k : ℕ} (x y : Fin k) → Id (mul-Fin x y) (mul-Fin y x)
commutative-mul-Fin {succ-ℕ k} x y =
  eq-cong-ℕ k
    ( mul-ℕ (nat-Fin x) (nat-Fin y))
    ( mul-ℕ (nat-Fin y) (nat-Fin x))
    ( cong-identification-ℕ
      ( succ-ℕ k)
      ( commutative-mul-ℕ (nat-Fin x) (nat-Fin y)))

one-Fin : {k : ℕ} → Fin (succ-ℕ k)
one-Fin {k} = mod-succ-ℕ k one-ℕ

is-one-Fin : {k : ℕ} → Fin k → UU lzero
is-one-Fin {succ-ℕ k} x = Id x one-Fin

nat-one-Fin : {k : ℕ} → is-one-ℕ (nat-Fin (one-Fin {succ-ℕ k}))
nat-one-Fin {zero-ℕ} = refl
nat-one-Fin {succ-ℕ k} = nat-one-Fin {k}

left-unit-law-mul-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mul-Fin one-Fin x) x
left-unit-law-mul-Fin {zero-ℕ} (inr star) = refl
left-unit-law-mul-Fin {succ-ℕ k} x =
  ( eq-cong-ℕ (succ-ℕ k)
    ( mul-ℕ (nat-Fin (one-Fin {succ-ℕ k})) (nat-Fin x))
    ( nat-Fin x)
    ( cong-identification-ℕ
      ( succ-ℕ (succ-ℕ k))
      ( ( ap ( mul-ℕ' (nat-Fin x))
             ( nat-one-Fin {k})) ∙
        ( left-unit-law-mul-ℕ (nat-Fin x))))) ∙
  ( issec-nat-Fin x)

right-unit-law-mul-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mul-Fin x one-Fin) x
right-unit-law-mul-Fin x =
  ( commutative-mul-Fin x one-Fin) ∙
  ( left-unit-law-mul-Fin x)

left-distributive-mul-add-Fin :
  {k : ℕ} (x y z : Fin k) →
  Id (mul-Fin x (add-Fin y z)) (add-Fin (mul-Fin x y) (mul-Fin x z))
left-distributive-mul-add-Fin {succ-ℕ k} x y z =
  eq-cong-ℕ k
    ( mul-ℕ (nat-Fin x) (nat-Fin (add-Fin y z)))
    ( add-ℕ (nat-Fin (mul-Fin x y)) (nat-Fin (mul-Fin x z)))
    ( concatenate-cong-eq-cong-ℕ
      { k = succ-ℕ k}
      { x1 = mul-ℕ ( nat-Fin x) (nat-Fin (add-Fin y z))}
      { x2 = mul-ℕ ( nat-Fin x) (add-ℕ (nat-Fin y) (nat-Fin z))}
      { x3 = add-ℕ ( mul-ℕ (nat-Fin x) (nat-Fin y))
                   ( mul-ℕ (nat-Fin x) (nat-Fin z))}
      { x4 = add-ℕ (nat-Fin (mul-Fin x y)) (nat-Fin (mul-Fin x z))}
      ( congruence-mul-ℕ
        ( succ-ℕ k)
        { x = nat-Fin x}
        { y = nat-Fin (add-Fin y z)}
        { x' = nat-Fin x}
        { y' = add-ℕ (nat-Fin y) (nat-Fin z)}
        ( reflexive-cong-ℕ (succ-ℕ k) (nat-Fin x))
        ( cong-add-Fin y z))
      ( left-distributive-mul-add-ℕ (nat-Fin x) (nat-Fin y) (nat-Fin z))
      ( symmetric-cong-ℕ (succ-ℕ k)
        ( add-ℕ ( nat-Fin (mul-Fin x y))
                ( nat-Fin (mul-Fin x z)))
        ( add-ℕ ( mul-ℕ (nat-Fin x) (nat-Fin y))
                ( mul-ℕ (nat-Fin x) (nat-Fin z)))
        ( congruence-add-ℕ
          ( succ-ℕ k)
          { x = nat-Fin (mul-Fin x y)}
          { y = nat-Fin (mul-Fin x z)}
          { x' = mul-ℕ (nat-Fin x) (nat-Fin y)}
          { y' = mul-ℕ (nat-Fin x) (nat-Fin z)}
          ( cong-mul-Fin x y)
          ( cong-mul-Fin x z))))

right-distributive-mul-add-Fin :
  {k : ℕ} (x y z : Fin k) →
  Id (mul-Fin (add-Fin x y) z) (add-Fin (mul-Fin x z) (mul-Fin y z))
right-distributive-mul-add-Fin {k} x y z =
  ( commutative-mul-Fin (add-Fin x y) z) ∙
  ( ( left-distributive-mul-add-Fin z x y) ∙
    ( ap-add-Fin (commutative-mul-Fin z x) (commutative-mul-Fin z y)))

{- Exercise 7.8 -}

-- We first prove two lemmas

leq-nat-succ-Fin :
  (k : ℕ) (x : Fin k) → leq-ℕ (nat-Fin (succ-Fin x)) (succ-ℕ (nat-Fin x))
leq-nat-succ-Fin (succ-ℕ k) (inl x) =
  leq-eq-ℕ
    ( nat-Fin (skip-zero-Fin x))
    ( succ-ℕ (nat-Fin (inl x)))
    ( nat-skip-zero-Fin x)
leq-nat-succ-Fin (succ-ℕ k) (inr star) =
  concatenate-eq-leq-ℕ
    ( succ-ℕ (nat-Fin (inr star)))
    ( nat-zero-Fin {succ-ℕ k})
    ( leq-zero-ℕ (succ-ℕ (nat-Fin {succ-ℕ k} (inr star))))

leq-nat-mod-succ-ℕ :
  (k x : ℕ) → leq-ℕ (nat-Fin (mod-succ-ℕ k x)) x
leq-nat-mod-succ-ℕ k zero-ℕ =
  concatenate-eq-leq-ℕ zero-ℕ (nat-zero-Fin {k}) (reflexive-leq-ℕ zero-ℕ)
leq-nat-mod-succ-ℕ k (succ-ℕ x) =
  transitive-leq-ℕ
    ( nat-Fin (mod-succ-ℕ k (succ-ℕ x)))
    ( succ-ℕ (nat-Fin (mod-succ-ℕ k x)))
    ( succ-ℕ x)
    ( leq-nat-succ-Fin (succ-ℕ k) (mod-succ-ℕ k x))
    ( leq-nat-mod-succ-ℕ k x)

-- Now we solve the exercise

euclidean-division-succ-ℕ :
  (k x : ℕ) → Σ ℕ (λ r → (cong-ℕ (succ-ℕ k) x r) × (le-ℕ r (succ-ℕ k)))
euclidean-division-succ-ℕ k x =
  pair
    ( nat-Fin (mod-succ-ℕ k x))
    ( pair
      ( symmetric-cong-ℕ (succ-ℕ k) (nat-Fin (mod-succ-ℕ k x)) x
        ( cong-nat-mod-succ-ℕ k x))
      ( strict-upper-bound-nat-Fin (mod-succ-ℕ k x)))

remainder-euclidean-division-succ-ℕ : (k x : ℕ) → ℕ
remainder-euclidean-division-succ-ℕ k x =
  pr1 (euclidean-division-succ-ℕ k x)

strict-upper-bound-remainder-euclidean-division-succ-ℕ :
  (k x : ℕ) → le-ℕ (remainder-euclidean-division-succ-ℕ k x) (succ-ℕ k)
strict-upper-bound-remainder-euclidean-division-succ-ℕ k x =
  pr2 (pr2 (euclidean-division-succ-ℕ k x))

cong-euclidean-division-succ-ℕ :
  (k x : ℕ) → cong-ℕ (succ-ℕ k) x (remainder-euclidean-division-succ-ℕ k x)
cong-euclidean-division-succ-ℕ k x =
  pr1 (pr2 (euclidean-division-succ-ℕ k x))

quotient-euclidean-division-succ-ℕ : (k x : ℕ) → ℕ
quotient-euclidean-division-succ-ℕ k x =
  pr1 (cong-euclidean-division-succ-ℕ k x)

eq-quotient-euclidean-division-succ-ℕ :
  (k x : ℕ) →
  Id ( mul-ℕ (quotient-euclidean-division-succ-ℕ k x) (succ-ℕ k))
     ( dist-ℕ x (remainder-euclidean-division-succ-ℕ k x))
eq-quotient-euclidean-division-succ-ℕ k x =
  pr2 (cong-euclidean-division-succ-ℕ k x)

eq-euclidean-division-succ-ℕ :
  (k x : ℕ) →
  Id ( add-ℕ ( mul-ℕ (quotient-euclidean-division-succ-ℕ k x) (succ-ℕ k))
             ( remainder-euclidean-division-succ-ℕ k x))
     ( x)
eq-euclidean-division-succ-ℕ k x =
  ( ap ( add-ℕ' (remainder-euclidean-division-succ-ℕ k x))
       ( ( pr2 (cong-euclidean-division-succ-ℕ k x)) ∙
         ( symmetric-dist-ℕ x (remainder-euclidean-division-succ-ℕ k x)))) ∙
  ( is-difference-dist-ℕ' (remainder-euclidean-division-succ-ℕ k x) x
    ( leq-nat-mod-succ-ℕ k x))

euclidean-division-ℕ :
  (k x : ℕ) → is-nonzero-ℕ k → Σ ℕ (λ r → (cong-ℕ k x r) × (le-ℕ r k))
euclidean-division-ℕ k x is-nonzero-k with
  is-successor-is-nonzero-ℕ k is-nonzero-k
... | pair l refl = euclidean-division-succ-ℕ l x

remainder-euclidean-division-ℕ : (k x : ℕ) → is-nonzero-ℕ k → ℕ
remainder-euclidean-division-ℕ k x is-nonzero-k with
  is-successor-is-nonzero-ℕ k is-nonzero-k
... | pair l refl = remainder-euclidean-division-succ-ℕ l x

strict-upper-bound-remainder-euclidean-division-ℕ :
  (k x : ℕ) (is-nonzero-k : is-nonzero-ℕ k) →
  le-ℕ (remainder-euclidean-division-ℕ k x is-nonzero-k) k
strict-upper-bound-remainder-euclidean-division-ℕ k x is-nonzero-k with
  is-successor-is-nonzero-ℕ k is-nonzero-k
... | pair l refl = strict-upper-bound-remainder-euclidean-division-succ-ℕ l x

cong-euclidean-division-ℕ :
  (k x : ℕ) (is-nonzero-k : is-nonzero-ℕ k) →
  cong-ℕ k x (remainder-euclidean-division-ℕ k x is-nonzero-k)
cong-euclidean-division-ℕ k x is-nonzero-k with
  is-successor-is-nonzero-ℕ k is-nonzero-k
... | pair l refl = cong-euclidean-division-succ-ℕ l x

quotient-euclidean-division-ℕ : (k x : ℕ) → is-nonzero-ℕ k → ℕ
quotient-euclidean-division-ℕ k x is-nonzero-k with
  is-successor-is-nonzero-ℕ k is-nonzero-k
... | pair l refl = quotient-euclidean-division-succ-ℕ l x

eq-quotient-euclidean-division-ℕ :
  (k x : ℕ) (H : is-nonzero-ℕ k) →
  Id ( mul-ℕ (quotient-euclidean-division-ℕ k x H) k)
     ( dist-ℕ x (remainder-euclidean-division-ℕ k x H))
eq-quotient-euclidean-division-ℕ k x H with
  is-successor-is-nonzero-ℕ k H
... | pair l refl = eq-quotient-euclidean-division-succ-ℕ l x

eq-euclidean-division-ℕ :
  (k x : ℕ) (is-nonzero-k : is-nonzero-ℕ k) →
  Id ( add-ℕ ( mul-ℕ ( quotient-euclidean-division-ℕ k x is-nonzero-k) k)
             ( remainder-euclidean-division-ℕ k x is-nonzero-k))
     ( x)
eq-euclidean-division-ℕ k x is-nonzero-k with
  is-successor-is-nonzero-ℕ k is-nonzero-k
... | pair l refl = eq-euclidean-division-succ-ℕ l x






























--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

dist-ℤ : ℤ → ℤ → ℕ
dist-ℤ (inl x) (inl y) = dist-ℕ x y
dist-ℤ (inl x) (inr (inl star)) = succ-ℕ x
dist-ℤ (inl x) (inr (inr y)) = succ-ℕ (succ-ℕ (add-ℕ x y))
dist-ℤ (inr (inl star)) (inl y) = succ-ℕ y
dist-ℤ (inr (inr x)) (inl y) = succ-ℕ (succ-ℕ (add-ℕ x y))
dist-ℤ (inr (inl star)) (inr (inl star)) = zero-ℕ
dist-ℤ (inr (inl star)) (inr (inr y)) = succ-ℕ y
dist-ℤ (inr (inr x)) (inr (inl star)) = succ-ℕ x
dist-ℤ (inr (inr x)) (inr (inr y)) = dist-ℕ x y

dist-ℤ' : ℤ → ℤ → ℕ
dist-ℤ' x y = dist-ℤ y x

ap-dist-ℤ :
  {x y x' y' : ℤ} → Id x x' → Id y y' → Id (dist-ℤ x y) (dist-ℤ x' y')
ap-dist-ℤ refl refl = refl

eq-dist-ℤ :
  (x y : ℤ) → is-zero-ℕ (dist-ℤ x y) → Id x y
eq-dist-ℤ (inl x) (inl y) p = ap inl (eq-dist-ℕ x y p)
eq-dist-ℤ (inl x) (inr (inl star)) p = ex-falso (Peano-8 x p)
eq-dist-ℤ (inr (inl star)) (inl y) p = ex-falso (Peano-8 y p)
eq-dist-ℤ (inr (inl star)) (inr (inl star)) p = refl
eq-dist-ℤ (inr (inl star)) (inr (inr y)) p = ex-falso (Peano-8 y p)
eq-dist-ℤ (inr (inr x)) (inr (inl star)) p = ex-falso (Peano-8 x p)
eq-dist-ℤ (inr (inr x)) (inr (inr y)) p = ap (inr ∘ inr) (eq-dist-ℕ x y p)

dist-eq-ℤ' :
  (x : ℤ) → is-zero-ℕ (dist-ℤ x x)
dist-eq-ℤ' (inl x) = dist-eq-ℕ' x
dist-eq-ℤ' (inr (inl star)) = refl
dist-eq-ℤ' (inr (inr x)) = dist-eq-ℕ' x

dist-eq-ℤ :
  (x y : ℤ) → Id x y → is-zero-ℕ (dist-ℤ x y)
dist-eq-ℤ x .x refl = dist-eq-ℤ' x

{- The distance function on ℤ is symmetric. -}

symmetric-dist-ℤ :
  (x y : ℤ) → Id (dist-ℤ x y) (dist-ℤ y x)
symmetric-dist-ℤ (inl x) (inl y) = symmetric-dist-ℕ x y
symmetric-dist-ℤ (inl x) (inr (inl star)) = refl
symmetric-dist-ℤ (inl x) (inr (inr y)) =
  ap (succ-ℕ ∘ succ-ℕ) (commutative-add-ℕ x y)
symmetric-dist-ℤ (inr (inl star)) (inl y) = refl
symmetric-dist-ℤ (inr (inr x)) (inl y) =
  ap (succ-ℕ ∘ succ-ℕ) (commutative-add-ℕ x y)
symmetric-dist-ℤ (inr (inl star)) (inr (inl star)) = refl
symmetric-dist-ℤ (inr (inl star)) (inr (inr y)) = refl
symmetric-dist-ℤ (inr (inr x)) (inr (inl star)) = refl
symmetric-dist-ℤ (inr (inr x)) (inr (inr y)) = symmetric-dist-ℕ x y

-- We compute the distance from zero --

left-zero-law-dist-ℤ :
  (x : ℤ) → Id (dist-ℤ zero-ℤ x) (abs-ℤ x)
left-zero-law-dist-ℤ (inl x) = refl
left-zero-law-dist-ℤ (inr (inl star)) = refl
left-zero-law-dist-ℤ (inr (inr x)) = refl

right-zero-law-dist-ℤ :
  (x : ℤ) → Id (dist-ℤ x zero-ℤ) (abs-ℤ x)
right-zero-law-dist-ℤ (inl x) = refl
right-zero-law-dist-ℤ (inr (inl star)) = refl
right-zero-law-dist-ℤ (inr (inr x)) = refl

-- We prove the triangle inequality --

{-
triangle-inequality-dist-ℤ :
  (x y z : ℤ) → leq-ℕ (dist-ℤ x y) (add-ℕ (dist-ℤ x z) (dist-ℤ z y))
triangle-inequality-dist-ℤ (inl x) (inl y) (inl z) =
  triangle-inequality-dist-ℕ x y z
triangle-inequality-dist-ℤ (inl x) (inl y) (inr (inl star)) =
  triangle-inequality-dist-ℕ (succ-ℕ x) (succ-ℕ y) zero-ℕ
triangle-inequality-dist-ℤ (inl x) (inl y) (inr (inr z)) = {!!}
triangle-inequality-dist-ℤ (inl x) (inr y) (inl z) = {!!}
triangle-inequality-dist-ℤ (inl x) (inr y) (inr z) = {!!}
triangle-inequality-dist-ℤ (inr x) (inl y) (inl z) = {!!}
triangle-inequality-dist-ℤ (inr x) (inl y) (inr z) = {!!}
triangle-inequality-dist-ℤ (inr x) (inr y) (inl z) = {!!}
triangle-inequality-dist-ℤ (inr x) (inr y) (inr z) = {!!}
-}

{-

triangle-inequality-dist-ℕ :
  (m n k : ℕ) → leq-ℕ (dist-ℕ m n) (add-ℕ (dist-ℕ m k) (dist-ℕ k n))
triangle-inequality-dist-ℕ zero-ℕ zero-ℕ zero-ℕ = star
triangle-inequality-dist-ℕ zero-ℕ zero-ℕ (succ-ℕ k) = star
triangle-inequality-dist-ℕ zero-ℕ (succ-ℕ n) zero-ℕ =
  tr ( leq-ℕ (succ-ℕ n))
     ( inv (left-unit-law-add-ℕ (succ-ℕ n)))
     ( reflexive-leq-ℕ (succ-ℕ n))
triangle-inequality-dist-ℕ zero-ℕ (succ-ℕ n) (succ-ℕ k) =
  concatenate-eq-leq-eq-ℕ
    ( inv (ap succ-ℕ (left-unit-law-dist-ℕ n)))
    ( triangle-inequality-dist-ℕ zero-ℕ n k)
    ( ( ap (succ-ℕ ∘ (add-ℕ' (dist-ℕ k n))) (left-unit-law-dist-ℕ k)) ∙
      ( inv (left-successor-law-add-ℕ k (dist-ℕ k n))))
triangle-inequality-dist-ℕ (succ-ℕ m) zero-ℕ zero-ℕ = reflexive-leq-ℕ (succ-ℕ m)
triangle-inequality-dist-ℕ (succ-ℕ m) zero-ℕ (succ-ℕ k) =
  concatenate-eq-leq-eq-ℕ
    ( inv (ap succ-ℕ (right-unit-law-dist-ℕ m)))
    ( triangle-inequality-dist-ℕ m zero-ℕ k)
    ( ap (succ-ℕ ∘ (add-ℕ (dist-ℕ m k))) (right-unit-law-dist-ℕ k))
triangle-inequality-dist-ℕ (succ-ℕ m) (succ-ℕ n) zero-ℕ =
  concatenate-leq-eq-ℕ
    ( dist-ℕ m n)
    ( transitive-leq-ℕ
      ( dist-ℕ m n)
      ( succ-ℕ (add-ℕ (dist-ℕ m zero-ℕ) (dist-ℕ zero-ℕ n)))
      ( succ-ℕ (succ-ℕ (add-ℕ (dist-ℕ m zero-ℕ) (dist-ℕ zero-ℕ n)))) 
      ( transitive-leq-ℕ
        ( dist-ℕ m n)
        ( add-ℕ (dist-ℕ m zero-ℕ) (dist-ℕ zero-ℕ n))
        ( succ-ℕ (add-ℕ (dist-ℕ m zero-ℕ) (dist-ℕ zero-ℕ n)))
        ( triangle-inequality-dist-ℕ m n zero-ℕ)
        ( succ-leq-ℕ (add-ℕ (dist-ℕ m zero-ℕ) (dist-ℕ zero-ℕ n))))
      ( succ-leq-ℕ (succ-ℕ (add-ℕ (dist-ℕ m zero-ℕ) (dist-ℕ zero-ℕ n)))))
    ( ( ap (succ-ℕ ∘ succ-ℕ)
           ( ap-add-ℕ (right-unit-law-dist-ℕ m) (left-unit-law-dist-ℕ n))) ∙
      ( inv (left-successor-law-add-ℕ m (succ-ℕ n))))
triangle-inequality-dist-ℕ (succ-ℕ m) (succ-ℕ n) (succ-ℕ k) =
  triangle-inequality-dist-ℕ m n k

-- We show that dist-ℕ x y is a solution to a simple equation.

leq-dist-ℕ :
  (x y : ℕ) → leq-ℕ x y → Id (add-ℕ x (dist-ℕ x y)) y
leq-dist-ℕ zero-ℕ zero-ℕ H = refl
leq-dist-ℕ zero-ℕ (succ-ℕ y) star = left-unit-law-add-ℕ (succ-ℕ y)
leq-dist-ℕ (succ-ℕ x) (succ-ℕ y) H =
  ( left-successor-law-add-ℕ x (dist-ℕ x y)) ∙
  ( ap succ-ℕ (leq-dist-ℕ x y H))

rewrite-left-add-dist-ℕ :
  (x y z : ℕ) → Id (add-ℕ x y) z → Id x (dist-ℕ y z)
rewrite-left-add-dist-ℕ zero-ℕ zero-ℕ .zero-ℕ refl = refl
rewrite-left-add-dist-ℕ zero-ℕ (succ-ℕ y) .(succ-ℕ (add-ℕ zero-ℕ y)) refl =
  ( dist-eq-ℕ' y) ∙
  ( inv (ap (dist-ℕ (succ-ℕ y)) (left-unit-law-add-ℕ (succ-ℕ y))))
rewrite-left-add-dist-ℕ (succ-ℕ x) zero-ℕ .(succ-ℕ x) refl = refl
rewrite-left-add-dist-ℕ
  (succ-ℕ x) (succ-ℕ y) .(succ-ℕ (add-ℕ (succ-ℕ x) y)) refl =
  rewrite-left-add-dist-ℕ (succ-ℕ x) y (add-ℕ (succ-ℕ x) y) refl

rewrite-left-dist-add-ℕ :
  (x y z : ℕ) → leq-ℕ y z → Id x (dist-ℕ y z) → Id (add-ℕ x y) z
rewrite-left-dist-add-ℕ .(dist-ℕ y z) y z H refl =
  ( commutative-add-ℕ (dist-ℕ y z) y) ∙
  ( leq-dist-ℕ y z H)

rewrite-right-add-dist-ℕ :
  (x y z : ℕ) → Id (add-ℕ x y) z → Id y (dist-ℕ x z)
rewrite-right-add-dist-ℕ x y z p =
  rewrite-left-add-dist-ℕ y x z (commutative-add-ℕ y x ∙ p)

rewrite-right-dist-add-ℕ :
  (x y z : ℕ) → leq-ℕ x z → Id y (dist-ℕ x z) → Id (add-ℕ x y) z
rewrite-right-dist-add-ℕ x .(dist-ℕ x z) z H refl =
  leq-dist-ℕ x z H

-- We show that dist-ℕ is translation invariant

translation-invariant-dist-ℕ :
  (k m n : ℕ) → Id (dist-ℕ (add-ℕ k m) (add-ℕ k n)) (dist-ℕ m n)
translation-invariant-dist-ℕ zero-ℕ m n =
  ap-dist-ℕ (left-unit-law-add-ℕ m) (left-unit-law-add-ℕ n)
translation-invariant-dist-ℕ (succ-ℕ k)  m n =
  ( ap-dist-ℕ (left-successor-law-add-ℕ k m) (left-successor-law-add-ℕ k n)) ∙
  ( translation-invariant-dist-ℕ k m n)

-- We show that dist-ℕ is linear with respect to scalar multiplication

linear-dist-ℕ :
  (m n k : ℕ) → Id (dist-ℕ (mul-ℕ k m) (mul-ℕ k n)) (mul-ℕ k (dist-ℕ m n))
linear-dist-ℕ zero-ℕ zero-ℕ zero-ℕ = refl
linear-dist-ℕ zero-ℕ zero-ℕ (succ-ℕ k) = linear-dist-ℕ zero-ℕ zero-ℕ k
linear-dist-ℕ zero-ℕ (succ-ℕ n) zero-ℕ = refl
linear-dist-ℕ zero-ℕ (succ-ℕ n) (succ-ℕ k) =
  ap (dist-ℕ' (mul-ℕ (succ-ℕ k) (succ-ℕ n))) (right-zero-law-mul-ℕ (succ-ℕ k))
linear-dist-ℕ (succ-ℕ m) zero-ℕ zero-ℕ = refl
linear-dist-ℕ (succ-ℕ m) zero-ℕ (succ-ℕ k) =
  ap (dist-ℕ (mul-ℕ (succ-ℕ k) (succ-ℕ m))) (right-zero-law-mul-ℕ (succ-ℕ k))
linear-dist-ℕ (succ-ℕ m) (succ-ℕ n) zero-ℕ = refl
linear-dist-ℕ (succ-ℕ m) (succ-ℕ n) (succ-ℕ k) =
  ( ap-dist-ℕ
    ( right-successor-law-mul-ℕ (succ-ℕ k) m)
    ( right-successor-law-mul-ℕ (succ-ℕ k) n)) ∙
  ( ( translation-invariant-dist-ℕ
      ( succ-ℕ k)
      ( mul-ℕ (succ-ℕ k) m)
      ( mul-ℕ (succ-ℕ k) n)) ∙
    ( linear-dist-ℕ m n (succ-ℕ k)))
-}

swap-neg-two-neg-one-Fin :
  {k : ℕ} → Fin (succ-ℕ (succ-ℕ k)) → Fin (succ-ℕ (succ-ℕ k))
swap-neg-two-neg-one-Fin (inl (inl x)) = inl (inl x)
swap-neg-two-neg-one-Fin (inl (inr star)) = inr star
swap-neg-two-neg-one-Fin (inr star) = inl (inr star)

swap-Fin : {k : ℕ} (x y z : Fin k) → Fin k
swap-Fin {succ-ℕ zero-ℕ} x y z = z
swap-Fin {succ-ℕ (succ-ℕ k)} (inl x) (inl y) (inl z) = inl (swap-Fin x y z)
swap-Fin {succ-ℕ (succ-ℕ k)} (inl x) (inl y) (inr star) = inr star
swap-Fin {succ-ℕ (succ-ℕ k)} (inl x) (inr star) (inl z) =
  functor-coprod
    ( swap-Fin x (inr star))
    ( id)
    ( swap-neg-two-neg-one-Fin
      ( inl-Fin (succ-ℕ k)
        ( swap-Fin x (inr star) z)))
swap-Fin {succ-ℕ (succ-ℕ k)} (inl x) (inr star) (inr star) = inl x
swap-Fin {succ-ℕ (succ-ℕ k)} (inr star) (inl y) (inl z) =
  functor-coprod
    ( swap-Fin (inr star) y)
    ( id)
    ( swap-neg-two-neg-one-Fin
      ( inl-Fin (succ-ℕ k)
        ( swap-Fin (inr star) y z)))
swap-Fin {succ-ℕ (succ-ℕ k)} (inr star) (inl y) (inr star) = inl y
swap-Fin {succ-ℕ (succ-ℕ k)} (inr star) (inr star) (inl z) = inl z
swap-Fin {succ-ℕ (succ-ℕ k)} (inr star) (inr star) (inr star) = inr star

swap-neg-one-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (swap-Fin x neg-one-Fin neg-one-Fin) x
swap-neg-one-Fin {zero-ℕ} (inr star) = refl
swap-neg-one-Fin {succ-ℕ k} (inl x) = refl
swap-neg-one-Fin {succ-ℕ k} (inr star) = refl

is-neg-one-swap-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → is-neg-one-Fin (swap-Fin x neg-one-Fin x)
is-neg-one-swap-Fin {zero-ℕ} (inr star) = refl
is-neg-one-swap-Fin {succ-ℕ k} (inl x) =
  ap ( functor-coprod (swap-Fin x neg-one-Fin) id)
     ( ap ( swap-neg-two-neg-one-Fin ∘ inl-Fin (succ-ℕ k))
          ( is-neg-one-swap-Fin x))
is-neg-one-swap-Fin {succ-ℕ k} (inr star) = refl

{-
swap-swap-Fin : {k : ℕ} (x y z : Fin k) →
  Id (swap-Fin x y (swap-Fin x y z)) z
swap-swap-Fin {succ-ℕ zero-ℕ} x y z = refl
swap-swap-Fin {succ-ℕ (succ-ℕ k)} (inl x) (inl y) (inl z) =
  ap inl (swap-swap-Fin x y z)
swap-swap-Fin {succ-ℕ (succ-ℕ k)} (inl x) (inl y) (inr star) = refl
swap-swap-Fin {succ-ℕ (succ-ℕ k)} (inl x) (inr star) (inl z) = {!!}
swap-swap-Fin {succ-ℕ (succ-ℕ k)} (inl x) (inr star) (inr star) = {!!}
swap-swap-Fin {succ-ℕ (succ-ℕ k)} (inr star) (inl y) (inl z) = {!!}
swap-swap-Fin {succ-ℕ (succ-ℕ k)} (inr star) (inl y) (inr star) = {!!}
swap-swap-Fin {succ-ℕ (succ-ℕ k)} (inr star) (inr star) (inl z) = {!!}
swap-swap-Fin {succ-ℕ (succ-ℕ k)} (inr star) (inr star) (inr star) = {!!}
-}

--------------------------------------------------------------------------------

{- The type of k-ary natural numbers, for arbitrary k -}
data based-ℕ : ℕ → UU lzero where
  constant-based-ℕ : (k : ℕ) → Fin k → based-ℕ k
  unary-op-based-ℕ : (k : ℕ) → Fin k → based-ℕ k → based-ℕ k

{- Converting a k-ary natural number to a natural number -}
constant-ℕ : (k : ℕ) → Fin k → ℕ
constant-ℕ k x = nat-Fin x

unary-op-ℕ : (k : ℕ) → Fin k → ℕ → ℕ
unary-op-ℕ k x n = add-ℕ (mul-ℕ k (succ-ℕ n)) (nat-Fin x)

convert-based-ℕ : (k : ℕ) → based-ℕ k → ℕ
convert-based-ℕ k (constant-based-ℕ .k x) =
  constant-ℕ k x
convert-based-ℕ k (unary-op-based-ℕ .k x n) =
  unary-op-ℕ k x (convert-based-ℕ k n)

{- The type of 0-ary natural numbers is empty -}
is-empty-based-zero-ℕ : is-empty (based-ℕ zero-ℕ)
is-empty-based-zero-ℕ (constant-based-ℕ .zero-ℕ ())
is-empty-based-zero-ℕ (unary-op-based-ℕ .zero-ℕ () n)

{- We show that the function convert-based-ℕ is injective -}
cong-unary-op-ℕ :
  (k : ℕ) (x : Fin k) (n : ℕ) →
  cong-ℕ k (unary-op-ℕ k x n) (nat-Fin x)
cong-unary-op-ℕ (succ-ℕ k) x n =
  concatenate-cong-eq-ℕ
    ( succ-ℕ k)
    { unary-op-ℕ (succ-ℕ k) x n}
    ( translation-invariant-cong-ℕ'
      ( succ-ℕ k)
      ( mul-ℕ (succ-ℕ k) (succ-ℕ n))
      ( zero-ℕ)
      ( nat-Fin x)
      ( pair (succ-ℕ n) (commutative-mul-ℕ (succ-ℕ n) (succ-ℕ k))))
    ( left-unit-law-add-ℕ (nat-Fin x))

{- Any natural number of the form constant-ℕ k x is strictly less than any 
   natural number of the form unary-op-ℕ k y m -}
le-constant-unary-op-ℕ :
  (k : ℕ) (x y : Fin k) (m : ℕ) → le-ℕ (constant-ℕ k x) (unary-op-ℕ k y m)
le-constant-unary-op-ℕ k x y m =
  concatenate-le-leq-ℕ {nat-Fin x} {k} {unary-op-ℕ k y m}
    ( strict-upper-bound-nat-Fin x)
    ( transitive-leq-ℕ
      ( k)
      ( mul-ℕ k (succ-ℕ m))
      ( unary-op-ℕ k y m)
        ( leq-mul-ℕ m k)
        ( leq-add-ℕ (mul-ℕ k (succ-ℕ m)) (nat-Fin y)))

is-injective-convert-based-ℕ :
  (k : ℕ) → is-injective (convert-based-ℕ k)
is-injective-convert-based-ℕ
  ( succ-ℕ k)
  { constant-based-ℕ .(succ-ℕ k) x}
  { constant-based-ℕ .(succ-ℕ k) y} p =
  ap (constant-based-ℕ (succ-ℕ k)) (is-injective-nat-Fin p)
is-injective-convert-based-ℕ
  ( succ-ℕ k)
  { constant-based-ℕ .(succ-ℕ k) x}
  { unary-op-based-ℕ .(succ-ℕ k) y m} p =
  ex-falso
    ( neq-le-ℕ
      ( le-constant-unary-op-ℕ (succ-ℕ k) x y (convert-based-ℕ (succ-ℕ k) m))
      ( p))
is-injective-convert-based-ℕ
  ( succ-ℕ k)
  { unary-op-based-ℕ .(succ-ℕ k) x n}
  { constant-based-ℕ .(succ-ℕ k) y} p =
  ex-falso
    ( neq-le-ℕ
      ( le-constant-unary-op-ℕ (succ-ℕ k) y x (convert-based-ℕ (succ-ℕ k) n))
      ( inv p))
is-injective-convert-based-ℕ
  ( succ-ℕ k)
  { unary-op-based-ℕ .(succ-ℕ k) x n}
  { unary-op-based-ℕ .(succ-ℕ k) y m} p with
  -- the following term has type Id x y
  is-injective-nat-Fin {succ-ℕ k} {x} {y}
    ( eq-cong-le-ℕ
      ( succ-ℕ k)
      ( nat-Fin x)
      ( nat-Fin y)
      ( strict-upper-bound-nat-Fin x)
      ( strict-upper-bound-nat-Fin y)
      ( concatenate-cong-eq-cong-ℕ
        { succ-ℕ k}
        { nat-Fin x}
        { unary-op-ℕ (succ-ℕ k) x (convert-based-ℕ (succ-ℕ k) n)}
        { unary-op-ℕ (succ-ℕ k) y (convert-based-ℕ (succ-ℕ k) m)}
        { nat-Fin y}
        ( symmetric-cong-ℕ
          ( succ-ℕ k)
          ( unary-op-ℕ (succ-ℕ k) x (convert-based-ℕ (succ-ℕ k) n))
          ( nat-Fin x)
          ( cong-unary-op-ℕ (succ-ℕ k) x (convert-based-ℕ (succ-ℕ k) n)))
        ( p)
        ( cong-unary-op-ℕ (succ-ℕ k) y (convert-based-ℕ (succ-ℕ k) m))))
... | refl =
  ap ( unary-op-based-ℕ (succ-ℕ k) x)
     ( is-injective-convert-based-ℕ (succ-ℕ k)
       ( is-injective-succ-ℕ
         ( is-injective-left-mul-ℕ k
           ( is-injective-add-ℕ' (nat-Fin x) p))))
  
{- We show that the map convert-based-ℕ has an inverse. -}

-- The zero-element of the (k+1)-ary natural numbers
zero-based-ℕ : (k : ℕ) → based-ℕ (succ-ℕ k)
zero-based-ℕ k = constant-based-ℕ (succ-ℕ k) zero-Fin

-- The successor function on the k-ary natural numbers
succ-based-ℕ : (k : ℕ) → based-ℕ k → based-ℕ k
succ-based-ℕ (succ-ℕ k) (constant-based-ℕ .(succ-ℕ k) (inl x)) =
  constant-based-ℕ (succ-ℕ k) (succ-Fin (inl x))
succ-based-ℕ (succ-ℕ k) (constant-based-ℕ .(succ-ℕ k) (inr star)) =
  unary-op-based-ℕ (succ-ℕ k) zero-Fin (constant-based-ℕ (succ-ℕ k) zero-Fin)
succ-based-ℕ (succ-ℕ k) (unary-op-based-ℕ .(succ-ℕ k) (inl x) n) =
  unary-op-based-ℕ (succ-ℕ k) (succ-Fin (inl x)) n
succ-based-ℕ (succ-ℕ k) (unary-op-based-ℕ .(succ-ℕ k) (inr x) n) =
  unary-op-based-ℕ (succ-ℕ k) zero-Fin (succ-based-ℕ (succ-ℕ k) n)
  
-- The inverse map of convert-based-ℕ
inv-convert-based-ℕ : (k : ℕ) → ℕ → based-ℕ (succ-ℕ k)
inv-convert-based-ℕ k zero-ℕ =
  zero-based-ℕ k
inv-convert-based-ℕ k (succ-ℕ n) =
  succ-based-ℕ (succ-ℕ k) (inv-convert-based-ℕ k n)

convert-based-succ-based-ℕ :
  (k : ℕ) (x : based-ℕ k) →
  Id (convert-based-ℕ k (succ-based-ℕ k x)) (succ-ℕ (convert-based-ℕ k x))
convert-based-succ-based-ℕ (succ-ℕ k) (constant-based-ℕ .(succ-ℕ k) (inl x)) =
  nat-succ-Fin x
convert-based-succ-based-ℕ
  ( succ-ℕ k) (constant-based-ℕ .(succ-ℕ k) (inr star)) =
  ( ap (λ t → add-ℕ (mul-ℕ (succ-ℕ k) (succ-ℕ t)) t) (nat-zero-Fin {k})) ∙
  ( right-unit-law-mul-ℕ (succ-ℕ k))
convert-based-succ-based-ℕ (succ-ℕ k) (unary-op-based-ℕ .(succ-ℕ k) (inl x) n) =
  ap ( add-ℕ (mul-ℕ (succ-ℕ k) (succ-ℕ (convert-based-ℕ (succ-ℕ k) n))))
     ( nat-succ-Fin {k} x)
convert-based-succ-based-ℕ
  (succ-ℕ k) (unary-op-based-ℕ .(succ-ℕ k) (inr star) n) =
  ( ap ( add-ℕ
         ( mul-ℕ
           ( succ-ℕ k)
           ( succ-ℕ (convert-based-ℕ (succ-ℕ k) (succ-based-ℕ (succ-ℕ k) n)))))
       ( nat-zero-Fin {k})) ∙
  ( ( ap ( (mul-ℕ (succ-ℕ k)) ∘ succ-ℕ)
         ( convert-based-succ-based-ℕ (succ-ℕ k) n)) ∙
    ( ( right-successor-law-mul-ℕ
        ( succ-ℕ k)
        ( succ-ℕ (convert-based-ℕ (succ-ℕ k) n))) ∙
      ( commutative-add-ℕ
        ( succ-ℕ k)
        ( mul-ℕ (succ-ℕ k) (succ-ℕ (convert-based-ℕ (succ-ℕ k) n))))))
   
issec-inv-convert-based-ℕ :
  (k n : ℕ) → Id (convert-based-ℕ (succ-ℕ k) (inv-convert-based-ℕ k n)) n
issec-inv-convert-based-ℕ k zero-ℕ = nat-zero-Fin {k}
issec-inv-convert-based-ℕ k (succ-ℕ n) =
  ( convert-based-succ-based-ℕ (succ-ℕ k) (inv-convert-based-ℕ  k n)) ∙
  ( ap succ-ℕ (issec-inv-convert-based-ℕ k n))

isretr-inv-convert-based-ℕ :
  (k : ℕ) (x : based-ℕ (succ-ℕ k)) →
  Id (inv-convert-based-ℕ k (convert-based-ℕ (succ-ℕ k) x)) x
isretr-inv-convert-based-ℕ k x =
  is-injective-convert-based-ℕ
    ( succ-ℕ k)
    ( issec-inv-convert-based-ℕ k (convert-based-ℕ (succ-ℕ k) x))

{- Observational equality of the k-ary natural numbers -}
Eq-based-ℕ : (k : ℕ) → (x y : based-ℕ k) → UU lzero
Eq-based-ℕ
  ( succ-ℕ k)
  ( constant-based-ℕ .(succ-ℕ k) x)
  ( constant-based-ℕ .(succ-ℕ k) y) =
  Eq-Fin (succ-ℕ k) x y
Eq-based-ℕ
  ( succ-ℕ k)
  ( constant-based-ℕ .(succ-ℕ k) x)
  ( unary-op-based-ℕ .(succ-ℕ k) y m) =
  empty
Eq-based-ℕ
  ( succ-ℕ k)
  ( unary-op-based-ℕ .(succ-ℕ k) x n)
  ( constant-based-ℕ .(succ-ℕ k) y) =
  empty
Eq-based-ℕ
  ( succ-ℕ k)
  ( unary-op-based-ℕ .(succ-ℕ k) x n)
  ( unary-op-based-ℕ .(succ-ℕ k) y m) =
  ( Eq-Fin (succ-ℕ k) x y) × (Eq-based-ℕ (succ-ℕ k) n m)

refl-Eq-based-ℕ : (k : ℕ) (x : based-ℕ k) → Eq-based-ℕ k x x
refl-Eq-based-ℕ (succ-ℕ k) (constant-based-ℕ .(succ-ℕ k) x) = refl-Eq-Fin x
refl-Eq-based-ℕ (succ-ℕ k) (unary-op-based-ℕ .(succ-ℕ k) x n) =
  pair
    ( refl-Eq-Fin x)
    ( refl-Eq-based-ℕ (succ-ℕ k) n)

Eq-based-ℕ-eq :
  (k : ℕ) (x y : based-ℕ k) → Id x y → Eq-based-ℕ k x y
Eq-based-ℕ-eq k x .x refl = refl-Eq-based-ℕ k x

eq-Eq-based-ℕ :
  (k : ℕ) (x y : based-ℕ k) → Eq-based-ℕ k x y → Id x y
eq-Eq-based-ℕ
  ( succ-ℕ k)
  ( constant-based-ℕ .(succ-ℕ k) x)
  ( constant-based-ℕ .(succ-ℕ k) y) e =
  ap (constant-based-ℕ (succ-ℕ k)) (eq-Eq-Fin e)
eq-Eq-based-ℕ
  ( succ-ℕ k)
  ( unary-op-based-ℕ .(succ-ℕ k) x n)
  ( unary-op-based-ℕ .(succ-ℕ k) y m)
  ( pair e f) with eq-Eq-Fin {succ-ℕ k} {x} {y} e
... | refl =
  ap (unary-op-based-ℕ (succ-ℕ k) x) (eq-Eq-based-ℕ (succ-ℕ k) n m f)
