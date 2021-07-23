{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module extra.modular-arithetic-integers where

import book
open book public

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
ap-dist-ℤ p q = ap-binary dist-ℤ p q

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
