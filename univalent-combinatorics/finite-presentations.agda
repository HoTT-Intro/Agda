{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-combinatorics.finite-presentations where

open import book.19-groups public

{-------------------------------------------------------------------------------

  Finitely presented types are types A equipped with a map f : Fin k → A such
  that the composite

    Fin k → A → type-trunc-Set A

  is an equivalence.

-------------------------------------------------------------------------------}

module _
  {l : Level} (k : ℕ) (A : UU l)
  where

  finite-presentation : UU l
  finite-presentation =
    Σ (Fin k → A) (λ f → is-equiv (unit-trunc-Set ∘ f))

  map-finite-presentation : finite-presentation → Fin k → A
  map-finite-presentation = pr1

  is-equiv-finite-presentation :
    (f : finite-presentation) →
    is-equiv (unit-trunc-Set ∘ map-finite-presentation f)
  is-equiv-finite-presentation = pr2


