{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module type-theories.comprehension-type-theories where

open import type-theories.dependent-type-theories public
open dependent

open import type-theories.fibered-dependent-type-theories public

record comprehension
  {l1 l2 l3 l4 : Level} {A : type-theory l1 l2}
  {B : fibered.fibered-type-theory l3 l4 A} : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where
  coinductive
  field
    type : {!!}
    element : {!!}
    slice : {!!}
