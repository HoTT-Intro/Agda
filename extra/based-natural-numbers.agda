{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module extra.based-natural-numbers where

import book
open book public

-- Some further observations about the k-ary natural numbers

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
