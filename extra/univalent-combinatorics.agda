{-# OPTIONS --without-K --exact-split #-}

module extra.univalent-combinatorics where

open import book public

-- locally finite types

is-locally-finite-Prop : {l : Level} → UU l → UU-Prop l
is-locally-finite-Prop A =
  Π-Prop A (λ x → Π-Prop A (λ y → is-finite-Prop (Id x y)))

is-locally-finite : {l : Level} → UU l → UU l
is-locally-finite A = type-Prop (is-locally-finite-Prop A)

is-prop-is-locally-finite :
  {l : Level} (A : UU l) → is-prop (is-locally-finite A)
is-prop-is-locally-finite A = is-prop-type-Prop (is-locally-finite-Prop A)

-- homotopy finite types

is-htpy-finite-Prop : {l : Level} (k : ℕ) → UU l → UU-Prop l
is-htpy-finite-Prop zero-ℕ A = is-finite-Prop (type-trunc-Set A)
is-htpy-finite-Prop (succ-ℕ k) A =
  prod-Prop
    ( is-finite-Prop (type-trunc-Set A))
    ( Π-Prop A (λ x → Π-Prop A (λ y → is-htpy-finite-Prop k (Id x y))))

is-htpy-finite : {l : Level} (k : ℕ) → UU l → UU l
is-htpy-finite k A = type-Prop (is-htpy-finite-Prop k A)

is-prop-is-htpy-finite :
  {l : Level} (k : ℕ) (A : UU l) → is-prop (is-htpy-finite k A)
is-prop-is-htpy-finite k A = is-prop-type-Prop (is-htpy-finite-Prop k A)
