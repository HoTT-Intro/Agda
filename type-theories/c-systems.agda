{-# OPTIONS --without-K --exact-split --guardedness --allow-unsolved-metas #-}

module type-theories.c-systems where

open import type-theories.dependent-type-theories public
open dependent

object' : {l1 l2 : Level} → type-theory l1 l2 → ℕ → UU l1
object' A zero-ℕ = system.type (type-theory.sys A)
object' A (succ-ℕ n) =
  Σ ( system.type (type-theory.sys A))
    ( λ X → object' (slice-dtt A X) n)

{-
hom' :
  {l1 l2 : Level} (A : type-theory l1 l2) {m n : ℕ} →
  object' A m → object' A n → UU l2
hom' A {zero-ℕ} {zero-ℕ} X Y =
  system.element
    ( type-theory.sys (slice-dtt A X))
    ( section-system.type (weakening.type (type-theory.W A) X) Y)
hom' A {succ-ℕ m} {zero-ℕ} (pair X X') Y =
  hom'
    ( slice-dtt A X)
    { m}
    ( X')
    ( section-system.type (weakening.type (type-theory.W A) X) Y)
hom' A {zero-ℕ} {succ-ℕ n} X (pair Y Y') =
  Σ ( hom' A {zero-ℕ} {zero-ℕ} X Y)
    ( λ f → {!section-system.type (section-system.slice (weakening.type (type-theory.W A) X) Y)!})
hom' A {succ-ℕ m} {succ-ℕ n} X (pair Y Y') = {!!}
-}

module C-dependent-type-theory
  {l1 l2 : Level} (A : type-theory l1 l2)
  where

  object : UU l1
  object = Σ ℕ (object' A)

  hom : (X Y : object) → UU l2
  hom (pair zero-ℕ X) (pair zero-ℕ Y) =
    system.element
      ( type-theory.sys (slice-dtt A X))
      ( section-system.type (weakening.type (type-theory.W A) X) Y)
  hom (pair zero-ℕ X) (pair (succ-ℕ n) (pair Y Z)) =
    Σ ( system.element
        ( type-theory.sys (slice-dtt A X))
        ( section-system.type (weakening.type (type-theory.W A) X) Y))
      ( λ f →
        hom ( pair zero-ℕ X)
            ( pair n
              {! section-system.type (substitution.type (type-theory.S (slice-dtt A X)) ? ?) ?!}))
  hom (pair (succ-ℕ m) X) (pair zero-ℕ Y) = {!!}
  hom (pair (succ-ℕ m) X) (pair (succ-ℕ n) Y) = {!!}
