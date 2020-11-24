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

-- locally finite types are closed under equivalences

is-locally-finite-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-locally-finite B → is-locally-finite A
is-locally-finite-equiv e f x y =
  is-finite-equiv' (equiv-ap e x y) (f (map-equiv e x) (map-equiv e y))

is-locally-finite-equiv' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-locally-finite A → is-locally-finite B
is-locally-finite-equiv' e = is-locally-finite-equiv (inv-equiv e)

-- types with decidable equality are locally finite

is-locally-finite-has-decidable-equality :
  {l1 : Level} {A : UU l1} → has-decidable-equality A → is-locally-finite A
is-locally-finite-has-decidable-equality d x y = is-finite-eq d

-- any proposition is locally finite

is-locally-finite-is-prop :
  {l1 : Level} {A : UU l1} → is-prop A → is-locally-finite A
is-locally-finite-is-prop H x y = is-finite-is-contr (H x y)

-- any contractible type is locally finite

is-locally-finite-is-contr :
  {l1 : Level} {A : UU l1} → is-contr A → is-locally-finite A
is-locally-finite-is-contr H =
  is-locally-finite-is-prop (is-prop-is-contr H)

is-locally-finite-unit : is-locally-finite unit
is-locally-finite-unit = is-locally-finite-is-contr is-contr-unit

-- any empty type is locally finite

is-locally-finite-is-empty :
  {l1 : Level} {A : UU l1} → is-empty A → is-locally-finite A
is-locally-finite-is-empty H = is-locally-finite-is-prop (λ x → ex-falso (H x))

is-locally-finite-empty : is-locally-finite empty
is-locally-finite-empty = is-locally-finite-is-empty id

--------------------------------------------------------------------------------

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

-- Dependent product of locally finite types

is-locally-finite-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-locally-finite A → is-locally-finite B → is-locally-finite (A × B)
is-locally-finite-prod f g x y =
  is-finite-equiv
    ( equiv-eq-pair x y)
    ( is-finite-prod (f (pr1 x) (pr1 y)) (g (pr2 x) (pr2 y)))

is-locally-finite-Π-Fin :
  {l1 : Level} {k : ℕ} {B : Fin k → UU l1} →
  ((x : Fin k) → is-locally-finite (B x)) →
  is-locally-finite ((x : Fin k) → B x)
is-locally-finite-Π-Fin {l1} {zero-ℕ} {B} f =
  is-locally-finite-is-contr (dependent-universal-property-empty B)
is-locally-finite-Π-Fin {l1} {succ-ℕ k} {B} f =
  is-locally-finite-equiv
    ( equiv-dependent-universal-property-coprod B)
    ( is-locally-finite-prod
      ( is-locally-finite-Π-Fin (λ x → f (inl x)))
      ( is-locally-finite-equiv
        ( equiv-ev-star (B ∘ inr))
        ( f (inr star))))

is-locally-finite-Π-count :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count A →
  ((x : A) → is-locally-finite (B x)) → is-locally-finite ((x : A) → B x)
is-locally-finite-Π-count {l1} {l2} {A} {B} (pair k e) g =
  is-locally-finite-equiv
    ( equiv-precomp-Π e B )
    ( is-locally-finite-Π-Fin (λ x → g (map-equiv e x)))

is-locally-finite-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-finite A →
  ((x : A) → is-locally-finite (B x)) → is-locally-finite ((x : A) → B x)
is-locally-finite-Π {l1} {l2} {A} {B} f g =
  apply-universal-property-trunc-Prop f
    ( is-locally-finite-Prop ((x : A) → B x))
    ( λ e → is-locally-finite-Π-count e g)
