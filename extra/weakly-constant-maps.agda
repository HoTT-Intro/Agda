{-# OPTIONS --without-K --exact-split #-}

module extra.weakly-constant-maps where

import book
open book public

is-higher-constant-map :
  {l1 l2 : Level} → ℕ → {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-higher-constant-map zero-ℕ {A} {B} f =
  Σ ( (x y : A) → Id (f x) (f y))
    ( λ H → (x y z : A) → Id (H x y ∙ H y z) (H x z))
is-higher-constant-map (succ-ℕ k) {A} {B} f =
  (x y : A) → is-higher-constant-map k (ap f {x} {y})

is-higher-constant-map-is-trunc :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} (f : A → B) →
  is-trunc (truncation-level-minus-one-ℕ k) A → is-higher-constant-map k f
is-higher-constant-map-is-trunc zero-ℕ f H =
  pair
    ( λ x y → ap f (eq-is-prop' H x y))
    ( λ x y z →
      ( inv (ap-concat f (eq-is-prop' H x y) (eq-is-prop' H y z))) ∙
      ( ap ( ap f)
           ( eq-is-prop'
             ( is-trunc-succ-is-trunc neg-one-𝕋 H x z)
             ( eq-is-prop' H x y ∙ eq-is-prop' H y z)
             ( eq-is-prop' H x z))))
is-higher-constant-map-is-trunc (succ-ℕ k) f H x y =
  is-higher-constant-map-is-trunc k (ap f) (H x y)
