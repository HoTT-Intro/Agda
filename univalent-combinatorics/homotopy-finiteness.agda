{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-combinatorics.homotopy-finiteness where

open import book.18-set-quotients public

is-strong-homotopy-finite-Prop : {l : Level} (k : ℕ) → UU l → UU-Prop l
is-strong-homotopy-finite-Prop zero-ℕ X = is-finite-Prop X
is-strong-homotopy-finite-Prop (succ-ℕ k) X =
  prod-Prop
    ( is-finite-Prop (type-trunc-Set X))
    ( Π-Prop X
      ( λ x → Π-Prop X (λ y → is-strong-homotopy-finite-Prop k (Id x y))))

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

is-homotopy-finite-equiv :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-homotopy-finite k B → is-homotopy-finite k A
is-homotopy-finite-equiv zero-ℕ e H =
  is-finite-equiv' (equiv-trunc-Set e) H
is-homotopy-finite-equiv (succ-ℕ k) e H =
  pair
    ( is-homotopy-finite-equiv zero-ℕ e (pr1 H))
    ( λ a b →
      is-homotopy-finite-equiv k
        ( equiv-ap e a b)
        ( pr2 H (map-equiv e a) (map-equiv e b)))

is-homotopy-finite-equiv' :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-homotopy-finite k A → is-homotopy-finite k B
is-homotopy-finite-equiv' k e = is-homotopy-finite-equiv k (inv-equiv e)

is-homotopy-finite-empty : (k : ℕ) → is-homotopy-finite k empty
is-homotopy-finite-empty zero-ℕ =
  is-finite-equiv equiv-unit-trunc-empty-Set is-finite-empty
is-homotopy-finite-empty (succ-ℕ k) =
  pair (is-homotopy-finite-empty zero-ℕ) ind-empty

is-homotopy-finite-coprod :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} →
  is-homotopy-finite k A → is-homotopy-finite k B →
  is-homotopy-finite k (coprod A B)
is-homotopy-finite-coprod zero-ℕ H K =
  is-finite-equiv'
    ( equiv-distributive-trunc-coprod-Set _ _)
    ( is-finite-coprod H K)
is-homotopy-finite-coprod (succ-ℕ k) H K =
  pair
    ( is-homotopy-finite-coprod zero-ℕ (pr1 H) (pr1 K))
    ( λ { (inl x) (inl y) →
          is-homotopy-finite-equiv k
            ( compute-eq-coprod-inl-inl x y)
            ( pr2 H x y) ;
          (inl x) (inr y) →
          is-homotopy-finite-equiv k
            ( compute-eq-coprod-inl-inr x y)
            ( is-homotopy-finite-empty k) ;
          (inr x) (inl y) →
          is-homotopy-finite-equiv k
            ( compute-eq-coprod-inr-inl x y)
            ( is-homotopy-finite-empty k) ;
          (inr x) (inr y) →
          is-homotopy-finite-equiv k
            ( compute-eq-coprod-inr-inr x y)
            ( pr2 K x y)})

is-homotopy-finite-Π-is-finite :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : A → UU l2} →
  is-finite A → ((a : A) → is-homotopy-finite k (B a)) →
  is-homotopy-finite k ((a : A) → B a)
is-homotopy-finite-Π-is-finite zero-ℕ {A} {B} H K =
  is-finite-equiv'
    ( equiv-distributive-trunc-Π-is-finite-Set B H)
    ( is-finite-Π H K)
is-homotopy-finite-Π-is-finite (succ-ℕ k) H K =
  pair
    ( is-homotopy-finite-Π-is-finite zero-ℕ H (λ a → pr1 (K a)))
    ( λ f g →
      is-homotopy-finite-equiv k
        ( equiv-funext)
        ( is-homotopy-finite-Π-is-finite k H (λ a → pr2 (K a) (f a) (g a))))

