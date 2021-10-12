{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module extra.quasi-decidable-propositions where

open import book public

is-quasi-decidable : UU-Prop lzero → UU (lsuc lzero)
is-quasi-decidable P =
  ( Q : UU-Prop lzero → UU-Prop lzero)
  ( q0 : type-Prop (Q empty-Prop))
  ( q1 : type-Prop (Q unit-Prop))
  ( qe : (f : ℕ → UU-Prop lzero) (g : (n : ℕ) → type-Prop (Q (f n))) →
    type-Prop (Q (exists-Prop f))) →
  type-Prop (Q P)

is-quasi-decidable-Level : (l : Level) → UU-Prop lzero → UU (lsuc l)
is-quasi-decidable-Level l P =
  ( Q : UU-Prop lzero → UU-Prop l)
  ( q0 : type-Prop (Q empty-Prop))
  ( q1 : type-Prop (Q unit-Prop))
  ( qe : (f : ℕ → UU-Prop lzero) (g : (n : ℕ) → type-Prop (Q (f n))) →
    type-Prop (Q (exists-Prop f))) →
  type-Prop (Q P)

is-quasi-decidable-is-quasi-decidable-Level :
  (l : Level) (P : UU-Prop lzero) →
  is-quasi-decidable-Level (lsuc l) P → is-quasi-decidable P
is-quasi-decidable-is-quasi-decidable-Level l P H Q q0 q1 qe =
  {!H (λ P → raise (prod-Prop (Q P) (is-small-Prop lzero (pr1 P)))!}
