{-# OPTIONS --without-K --exact-split #-}

module extra.Eisenstein-integers where

open import book public

{-------------------------------------------------------------------------------

  The Eisenstein Integers

  The Eisenstein integers are the complex numbers of the form

    a + bω

  where ω = -½ + ½√3i, and where a and b are integers. Note that ω is a 
  solution to the equation ω² + ω + 1 = 0.

-------------------------------------------------------------------------------}

ℤ[ω] : UU lzero
ℤ[ω] = ℤ × ℤ

Eq-ℤ[ω] : ℤ[ω] → ℤ[ω] → UU lzero
Eq-ℤ[ω] x y = (Id (pr1 x) (pr1 y)) × (Id (pr2 x) (pr2 y))

refl-Eq-ℤ[ω] : (x : ℤ[ω]) → Eq-ℤ[ω] x x
refl-Eq-ℤ[ω] x = pair refl refl

Eq-eq-ℤ[ω] : {x y : ℤ[ω]} → Id x y → Eq-ℤ[ω] x y
Eq-eq-ℤ[ω] {x} refl = refl-Eq-ℤ[ω] x

eq-Eq-ℤ[ω]' : {x y : ℤ[ω]} → Eq-ℤ[ω] x y → Id x y
eq-Eq-ℤ[ω]' {pair a b} {pair .a .b} (pair refl refl) = refl

eq-Eq-ℤ[ω] : {x y : ℤ[ω]} → Id (pr1 x) (pr1 y) → Id (pr2 x) (pr2 y) → Id x y
eq-Eq-ℤ[ω] {pair a b} {pair .a .b} refl refl = refl

zero-ℤ[ω] : ℤ[ω]
zero-ℤ[ω] = pair zero-ℤ zero-ℤ

one-ℤ[ω] : ℤ[ω]
one-ℤ[ω] = pair one-ℤ zero-ℤ

eisenstein-int-ℤ : ℤ → ℤ[ω]
eisenstein-int-ℤ x = pair x zero-ℤ

ω-ℤ[ω] : ℤ[ω]
ω-ℤ[ω] = pair zero-ℤ one-ℤ

neg-ω-ℤ[ω] : ℤ[ω]
neg-ω-ℤ[ω] = pair zero-ℤ neg-one-ℤ

add-ℤ[ω] : ℤ[ω] → ℤ[ω] → ℤ[ω]
add-ℤ[ω] (pair a b) (pair a' b') = pair (add-ℤ a a') (add-ℤ b b')

neg-ℤ[ω] : ℤ[ω] → ℤ[ω]
neg-ℤ[ω] (pair a b) = pair (neg-ℤ a) (neg-ℤ b)

-- (a + bω)(c + dω) = (ac - bd) + (ad + cb - bd)ω

mul-ℤ[ω] : ℤ[ω] → ℤ[ω] → ℤ[ω]
mul-ℤ[ω] (pair a1 b1) (pair a2 b2) =
  pair
    ( add-ℤ (mul-ℤ a1 a2) (neg-ℤ (mul-ℤ b1 b2)))
    ( add-ℤ (add-ℤ (mul-ℤ a1 b2) (mul-ℤ a2 b1)) (neg-ℤ (mul-ℤ b1 b2)))

-- The conjugate of (a + bω) is (a + bω²), which is ((a - b) - bω).

conjugate-ℤ[ω] : ℤ[ω] → ℤ[ω]
conjugate-ℤ[ω] (pair a b) = pair (add-ℤ a (neg-ℤ b)) (neg-ℤ b)

-- We show that the Eisenstein integers form a ring with conjugation

conjugate-conjugate-ℤ[ω] :
  (x : ℤ[ω]) → Id (conjugate-ℤ[ω] (conjugate-ℤ[ω] x)) x
conjugate-conjugate-ℤ[ω] (pair a b) =
  eq-Eq-ℤ[ω] (isretr-add-neg-ℤ' (neg-ℤ b) a) (neg-neg-ℤ b)
