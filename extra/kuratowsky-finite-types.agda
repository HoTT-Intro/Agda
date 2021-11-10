{-# OPTIONS --without-K --exact-split #-}

module extra.kuratowsky-finite-types where

open import book public

is-Kuratowsky-finite : {l1 : Level} → UU l1 → UU l1
is-Kuratowsky-finite X = ∃ (λ (k : ℕ) → Σ (Fin k → X) is-surjective)

upper-natural-of-a-type : {l1 : Level} {X : UU l1} → ℕ → UU l1
upper-natural-of-a-type {X = X} k = ∃ (λ (f : Fin k → X) → is-surjective f)
