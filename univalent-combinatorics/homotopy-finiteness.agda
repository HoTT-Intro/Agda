{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module combinatorics.homotopy-finiteness where

open import book public

is-homotopy-finite-Prop : {l : Level} (k : ℕ) → UU l → UU-Prop l
is-homotopy-finite-Prop zero-ℕ X = is-finite-Prop (type-trunc-Set X)
is-homotopy-finite-Prop (succ-ℕ k) X =
  prod-Prop ( is-finite-Prop (type-trunc-Set X))
            ( Π-Prop X
              ( λ x → Π-Prop X (λ y → is-homotopy-finite-Prop k (Id x y))))

is-homotopy-finite : {l : Level} (k : ℕ) → UU l → UU l
is-homotopy-finite k X = type-Prop (is-homotopy-finite-Prop k X)

is-prop-is-homotopy-finite :
  {l : Level} (k : ℕ) (X : UU l) → is-prop (is-homotopy-finite k X)
is-prop-is-homotopy-finite k X =
  is-prop-type-Prop (is-homotopy-finite-Prop k X)

{-
is-homotopy-finite-equiv :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-homotopy-finite k B → is-homotopy-finite k A
is-homotopy-finite-equiv zero-ℕ e H = is-finite-equiv' {!!} {!!}
is-homotopy-finite-equiv (succ-ℕ k) e H = {!!}
-}

{-
is-homotopy-finite-Π-zero-ℕ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-finite A →
  ((x : A) → is-homotopy-finite zero-ℕ (B x)) →
  is-homotopy-finite zero-ℕ ((x : A) → B x)
is-homotopy-finite-Π-zero-ℕ HA HB = {!!}
-}
