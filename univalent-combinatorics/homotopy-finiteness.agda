{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-combinatorics.homotopy-finiteness where

open import book.18-set-quotients public

{-------------------------------------------------------------------------------

  Univalent combinatorics

-------------------------------------------------------------------------------}

-- Section 1. Homotopy finiteness

-- Definition 1.3

-- We introduce locally finite types

is-locally-finite-Prop :
  {l : Level} → UU l → UU-Prop l
is-locally-finite-Prop A =
  Π-Prop A (λ x → Π-Prop A (λ y → is-finite-Prop (Id x y)))

is-locally-finite : {l : Level} → UU l → UU l
is-locally-finite A = type-Prop (is-locally-finite-Prop A)

is-prop-is-locally-finite :
  {l : Level} (A : UU l) → is-prop (is-locally-finite A)
is-prop-is-locally-finite A = is-prop-type-Prop (is-locally-finite-Prop A)

-- We introduce strong homotopy finite types

is-strong-homotopy-finite-Prop : {l : Level} (k : ℕ) → UU l → UU-Prop l
is-strong-homotopy-finite-Prop zero-ℕ X = is-finite-Prop X
is-strong-homotopy-finite-Prop (succ-ℕ k) X =
  prod-Prop
    ( is-finite-Prop (type-trunc-Set X))
    ( Π-Prop X
      ( λ x → Π-Prop X (λ y → is-strong-homotopy-finite-Prop k (Id x y))))

is-strong-homotopy-finite : {l : Level} (k : ℕ) → UU l → UU l
is-strong-homotopy-finite k A =
  type-Prop (is-strong-homotopy-finite-Prop k A)

-- We introduce homotopy finite types

has-finite-connected-components-Prop : {l : Level} → UU l → UU-Prop l
has-finite-connected-components-Prop A =
  is-finite-Prop (type-trunc-Set A)

has-finite-connected-components : {l : Level} → UU l → UU l
has-finite-connected-components A =
  type-Prop (has-finite-connected-components-Prop A)

is-homotopy-finite-Prop : {l : Level} (k : ℕ) → UU l → UU-Prop l
is-homotopy-finite-Prop zero-ℕ X = has-finite-connected-components-Prop X
is-homotopy-finite-Prop (succ-ℕ k) X =
  prod-Prop ( is-homotopy-finite-Prop zero-ℕ X)
            ( Π-Prop X
              ( λ x → Π-Prop X (λ y → is-homotopy-finite-Prop k (Id x y))))

is-homotopy-finite : {l : Level} (k : ℕ) → UU l → UU l
is-homotopy-finite k X = type-Prop (is-homotopy-finite-Prop k X)

is-prop-is-homotopy-finite :
  {l : Level} (k : ℕ) (X : UU l) → is-prop (is-homotopy-finite k X)
is-prop-is-homotopy-finite k X =
  is-prop-type-Prop (is-homotopy-finite-Prop k X)

Homotopy-Finite : (l : Level) (k : ℕ) → UU (lsuc l)
Homotopy-Finite l k = Σ (UU l) (is-homotopy-finite k)

type-Homotopy-Finite :
  {l : Level} (k : ℕ) → Homotopy-Finite l k → UU l
type-Homotopy-Finite k = pr1

is-homotopy-finite-type-Homotopy-Finite :
  {l : Level} (k : ℕ) (A : Homotopy-Finite l k) →
  is-homotopy-finite k (type-Homotopy-Finite {l} k A)
is-homotopy-finite-type-Homotopy-Finite k = pr2

-- Basic properties of locally finite types

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

-- Basic properties of homotopy finiteness

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

empty-Homotopy-Finite : (k : ℕ) → Homotopy-Finite lzero k
empty-Homotopy-Finite k = pair empty (is-homotopy-finite-empty k)

is-homotopy-finite-is-empty :
  {l : Level} (k : ℕ) {A : UU l} → is-empty A → is-homotopy-finite k A
is-homotopy-finite-is-empty zero-ℕ f =
  is-finite-is-empty (is-empty-trunc-Set f)
is-homotopy-finite-is-empty (succ-ℕ k) f =
  pair
    ( is-homotopy-finite-is-empty zero-ℕ f)
    ( λ a → ex-falso (f a))

is-homotopy-finite-is-contr :
  {l : Level} (k : ℕ) {A : UU l} → is-contr A → is-homotopy-finite k A
is-homotopy-finite-is-contr zero-ℕ H =
  is-finite-is-contr (is-contr-trunc-Set H)
is-homotopy-finite-is-contr (succ-ℕ k) H =
  pair
    ( is-homotopy-finite-is-contr zero-ℕ H)
    ( λ x y →
      is-homotopy-finite-is-contr k ( is-prop-is-contr H x y))

is-homotopy-finite-unit :
  (k : ℕ) → is-homotopy-finite k unit
is-homotopy-finite-unit k = is-homotopy-finite-is-contr k is-contr-unit

unit-Homotopy-Finite : (k : ℕ) → Homotopy-Finite lzero k
unit-Homotopy-Finite k = pair unit (is-homotopy-finite-unit k)

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

coprod-Homotopy-Finite :
  {l1 l2 : Level} (k : ℕ) →
  Homotopy-Finite l1 k → Homotopy-Finite l2 k → Homotopy-Finite (l1 ⊔ l2) k
coprod-Homotopy-Finite k A B =
  pair
    ( coprod (type-Homotopy-Finite k A) (type-Homotopy-Finite k B))
    ( is-homotopy-finite-coprod k
      ( is-homotopy-finite-type-Homotopy-Finite k A)
      ( is-homotopy-finite-type-Homotopy-Finite k B))

Maybe-Homotopy-Finite :
  {l : Level} (k : ℕ) → Homotopy-Finite  l k → Homotopy-Finite l k
Maybe-Homotopy-Finite k A =
  coprod-Homotopy-Finite k A (unit-Homotopy-Finite k)

is-homotopy-finite-Maybe :
  {l : Level} (k : ℕ) {A : UU l} →
  is-homotopy-finite k A → is-homotopy-finite k (Maybe A)
is-homotopy-finite-Maybe k H =
  is-homotopy-finite-coprod k H (is-homotopy-finite-unit k)

is-homotopy-finite-Fin :
  (k n : ℕ) → is-homotopy-finite k (Fin n)
is-homotopy-finite-Fin k zero-ℕ =
  is-homotopy-finite-empty k
is-homotopy-finite-Fin k (succ-ℕ n) =
  is-homotopy-finite-Maybe k (is-homotopy-finite-Fin k n)

Fin-Homotopy-Finite : (k : ℕ) (n : ℕ) → Homotopy-Finite lzero k
Fin-Homotopy-Finite k n =
  pair (Fin n) (is-homotopy-finite-Fin k n)

is-homotopy-finite-count :
  {l : Level} (k : ℕ) {A : UU l} → count A → is-homotopy-finite k A
is-homotopy-finite-count k (pair n e) =
  is-homotopy-finite-equiv' k e (is-homotopy-finite-Fin k n)

is-homotopy-finite-is-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-finite A → is-homotopy-finite k A
is-homotopy-finite-is-finite k {A} H =
  apply-universal-property-trunc-Prop H
    ( is-homotopy-finite-Prop k A)
    ( is-homotopy-finite-count k)

homotopy-finite-𝔽 : (k : ℕ) → 𝔽 → Homotopy-Finite lzero k
homotopy-finite-𝔽 k A =
  pair (type-𝔽 A) (is-homotopy-finite-is-finite k (is-finite-type-𝔽 A))

has-finite-connected-components-is-path-connected :
  {l : Level} {A : UU l} →
  is-path-connected A → has-finite-connected-components A
has-finite-connected-components-is-path-connected C =
  is-finite-is-contr C

is-homotopy-finite-UU-Fin :
  (k n : ℕ) → is-homotopy-finite k (UU-Fin n)
is-homotopy-finite-UU-Fin zero-ℕ n =
  has-finite-connected-components-is-path-connected
    ( is-path-connected-UU-Fin n)
is-homotopy-finite-UU-Fin (succ-ℕ k) n =
  pair
    ( is-homotopy-finite-UU-Fin zero-ℕ n)
    ( λ x y →
      is-homotopy-finite-equiv k
        ( equiv-equiv-eq-UU-Fin x y)
        ( is-homotopy-finite-is-finite k
          ( is-finite-≃
            ( is-finite-has-finite-cardinality (pair n (pr2 x)))
            ( is-finite-has-finite-cardinality (pair n (pr2 y))))))

is-finite-has-finite-connected-components :
  {l : Level} {A : UU l} →
  is-set A → has-finite-connected-components A → is-finite A
is-finite-has-finite-connected-components H =
  is-finite-equiv' (equiv-unit-trunc-Set (pair _ H))

has-finite-connected-components-is-homotopy-finite :
  {l : Level} (k : ℕ) {A : UU l} →
  is-homotopy-finite k A → has-finite-connected-components A
has-finite-connected-components-is-homotopy-finite zero-ℕ H = H
has-finite-connected-components-is-homotopy-finite (succ-ℕ k) H = pr1 H

is-homotopy-finite-is-homotopy-finite-succ-ℕ :
  {l : Level} (k : ℕ) {A : UU l} →
  is-homotopy-finite (succ-ℕ k) A → is-homotopy-finite k A
is-homotopy-finite-is-homotopy-finite-succ-ℕ zero-ℕ H =
  has-finite-connected-components-is-homotopy-finite one-ℕ H
is-homotopy-finite-is-homotopy-finite-succ-ℕ (succ-ℕ k) H =
  pair
    ( has-finite-connected-components-is-homotopy-finite (succ-ℕ (succ-ℕ k)) H)
    ( λ x y → is-homotopy-finite-is-homotopy-finite-succ-ℕ k (pr2 H x y))

is-homotopy-finite-one-is-homotopy-finite-succ-ℕ :
  {l : Level} (k : ℕ) {A : UU l} →
  is-homotopy-finite (succ-ℕ k) A → is-homotopy-finite one-ℕ A
is-homotopy-finite-one-is-homotopy-finite-succ-ℕ zero-ℕ H = H
is-homotopy-finite-one-is-homotopy-finite-succ-ℕ (succ-ℕ k) H =
  is-homotopy-finite-one-is-homotopy-finite-succ-ℕ k
    ( is-homotopy-finite-is-homotopy-finite-succ-ℕ (succ-ℕ k) H)

is-finite-is-homotopy-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-set A →
  is-homotopy-finite k A → is-finite A
is-finite-is-homotopy-finite k H K =
  is-finite-equiv'
    ( equiv-unit-trunc-Set (pair _ H))
    ( has-finite-connected-components-is-homotopy-finite k K)

is-strong-homotopy-finite-is-homotopy-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-trunc (truncation-level-ℕ k) A →
  is-homotopy-finite k A → is-strong-homotopy-finite k A
is-strong-homotopy-finite-is-homotopy-finite zero-ℕ H K =
  is-finite-is-homotopy-finite zero-ℕ H K
is-strong-homotopy-finite-is-homotopy-finite (succ-ℕ k) H K =
  pair
    ( pr1 K)
    ( λ x y →
      is-strong-homotopy-finite-is-homotopy-finite k (H x y) (pr2 K x y))

is-homotopy-finite-is-strong-homotopy-finite :
  {l : Level} (k : ℕ) {A : UU l} →
  is-strong-homotopy-finite k A → is-homotopy-finite k A
is-homotopy-finite-is-strong-homotopy-finite zero-ℕ H =
  is-finite-equiv
    ( equiv-unit-trunc-Set (pair _ (is-set-is-finite H)))
    ( H)
is-homotopy-finite-is-strong-homotopy-finite (succ-ℕ k) H =
  pair
    ( pr1 H)
    ( λ x y → is-homotopy-finite-is-strong-homotopy-finite k (pr2 H x y))

-- Proposition 1.5

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
  is-locally-finite-is-contr (dependent-universal-property-empty' B)
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

-- Finite products of homotopy finite types

is-homotopy-finite-Π :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : A → UU l2} →
  is-finite A → ((a : A) → is-homotopy-finite k (B a)) →
  is-homotopy-finite k ((a : A) → B a)
is-homotopy-finite-Π zero-ℕ {A} {B} H K =
  is-finite-equiv'
    ( equiv-distributive-trunc-Π-is-finite-Set B H)
    ( is-finite-Π H K)
is-homotopy-finite-Π (succ-ℕ k) H K =
  pair
    ( is-homotopy-finite-Π zero-ℕ H (λ a → pr1 (K a)))
    ( λ f g →
      is-homotopy-finite-equiv k
        ( equiv-funext)
        ( is-homotopy-finite-Π k H (λ a → pr2 (K a) (f a) (g a))))

Homotopy-Finite-Π :
  {l : Level} (k : ℕ) (A : 𝔽) (B : type-𝔽 A → Homotopy-Finite l k) →
  Homotopy-Finite l k
Homotopy-Finite-Π k A B =
  pair
    ( (x : type-𝔽 A) → (type-Homotopy-Finite k (B x)))
    ( is-homotopy-finite-Π k
      ( is-finite-type-𝔽 A)
      ( λ x → is-homotopy-finite-type-Homotopy-Finite k (B x)))

-- Proposition 1.6

is-locally-finite-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-locally-finite A → ((x : A) → is-locally-finite (B x)) →
  is-locally-finite (Σ A B)
is-locally-finite-Σ {B = B} H K (pair x y) (pair x' y') =
  is-finite-equiv'
    ( equiv-pair-eq-Σ (pair x y) (pair x' y'))
    ( is-finite-Σ (H x x') (λ p → K x' (tr B p y) y'))

-- Proposition 1.7

has-finite-connected-components-Σ-is-path-connected :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-path-connected A → is-homotopy-finite one-ℕ A →
  ((x : A) → has-finite-connected-components (B x)) →
  has-finite-connected-components (Σ A B)
has-finite-connected-components-Σ-is-path-connected {A = A} {B} C H K =
  apply-universal-property-trunc-Prop
    ( is-inhabited-is-path-connected C)
    ( is-homotopy-finite-Prop zero-ℕ (Σ A B))
    ( α)
    
  where
  α : A → is-homotopy-finite zero-ℕ (Σ A B)
  α a =
    is-finite-codomain-has-decidable-equality
      ( K a)
      ( is-surjective-map-trunc-Set
        ( fiber-inclusion B a)
        ( is-surjective-fiber-inclusion C a))
      ( apply-dependent-universal-property-trunc-Set
        ( λ x →
          set-Prop
            ( Π-Prop
              ( type-trunc-Set (Σ A B))
              ( λ y → is-decidable-Prop (Id-Prop (trunc-Set (Σ A B)) x y))))
        ( β))
        
    where
    β : (x : Σ A B) (v : type-trunc-Set (Σ A B)) →
        is-decidable (Id (unit-trunc-Set x) v)
    β (pair x y) =
      apply-dependent-universal-property-trunc-Set
        ( λ u →
          set-Prop
            ( is-decidable-Prop
              ( Id-Prop (trunc-Set (Σ A B)) (unit-trunc-Set (pair x y)) u)))
        ( γ)
        
      where
      γ : (v : Σ A B) →
          is-decidable (Id (unit-trunc-Set (pair x y)) (unit-trunc-Set v))
      γ (pair x' y') =
        is-decidable-equiv
          ( is-effective-unit-trunc-Set
            ( Σ A B)
            ( pair x y)
            ( pair x' y'))
          ( apply-universal-property-trunc-Prop
            ( mere-eq-is-path-connected C a x)
            ( is-decidable-Prop
              ( mere-eq-Prop (pair x y) (pair x' y')))
              ( δ))
              
        where
        δ : Id a x → is-decidable (mere-eq (pair x y) (pair x' y'))
        δ refl =
          apply-universal-property-trunc-Prop
            ( mere-eq-is-path-connected C a x')
            ( is-decidable-Prop
              ( mere-eq-Prop (pair a y) (pair x' y')))
            ( ε)
            
          where
          ε : Id a x' → is-decidable (mere-eq (pair x y) (pair x' y'))
          ε refl =
            is-decidable-equiv e
              ( is-decidable-type-trunc-Prop-is-finite
                ( is-finite-Σ
                  ( pr2 H a a)
                  ( λ ω → is-finite-is-decidable-Prop (P ω) (d ω))))
            
            where
            ℙ : is-contr
                ( Σ ( type-hom-Set (trunc-Set (Id a a)) (UU-Prop-Set _))
                    ( λ h →
                      ( λ a₁ → h (unit-trunc-Set a₁)) ~
                      ( λ ω₁ → trunc-Prop (Id (tr B ω₁ y) y'))))
            ℙ = universal-property-trunc-Set
                ( Id a a)
                ( UU-Prop-Set _)
                ( λ ω → trunc-Prop (Id (tr B ω y) y'))
            P : type-trunc-Set (Id a a) → UU-Prop _
            P = pr1 (center ℙ)
            compute-P :
              ( ω : Id a a) →
              type-Prop (P (unit-trunc-Set ω)) ≃
              type-trunc-Prop (Id (tr B ω y) y') 
            compute-P ω = equiv-eq (ap pr1 (pr2 (center ℙ) ω))
            d : (t : type-trunc-Set (Id a a)) → is-decidable (type-Prop (P t))
            d = apply-dependent-universal-property-trunc-Set
                ( λ t → set-Prop (is-decidable-Prop (P t)))
                ( λ ω →
                  is-decidable-equiv'
                    ( inv-equiv (compute-P ω))
                    ( is-decidable-equiv'
                      ( is-effective-unit-trunc-Set (B a) (tr B ω y) y')
                      ( has-decidable-equality-is-finite
                        ( K a)
                        ( unit-trunc-Set (tr B ω y))
                        ( unit-trunc-Set y'))))
            f : type-hom-Prop
                ( trunc-Prop (Σ (type-trunc-Set (Id a a)) (type-Prop ∘ P)))
                ( mere-eq-Prop {A = Σ A B} (pair a y) (pair a y'))
            f t = apply-universal-property-trunc-Prop t
                    ( mere-eq-Prop (pair a y) (pair a y'))
                     λ { (pair u v) →
                         apply-dependent-universal-property-trunc-Set
                           ( λ u' →
                             hom-Set
                               ( set-Prop (P u'))
                               ( set-Prop
                                 ( mere-eq-Prop (pair a y) (pair a y'))))
                           ( λ ω v' →
                             apply-universal-property-trunc-Prop
                               ( map-equiv (compute-P ω) v')
                               ( mere-eq-Prop (pair a y) (pair a y'))
                               ( λ p → unit-trunc-Prop (eq-pair-Σ ω p)))
                           ( u)
                           ( v)}
            e : mere-eq {A = Σ A B} (pair a y) (pair a y') ≃
                type-trunc-Prop (Σ (type-trunc-Set (Id a a)) (type-Prop ∘ P))
            e = equiv-iff
                  ( mere-eq-Prop (pair a y) (pair a y'))
                  ( trunc-Prop (Σ (type-trunc-Set (Id a a)) (type-Prop ∘ P)))
                  ( λ t →
                    apply-universal-property-trunc-Prop t
                      ( trunc-Prop _)
                      ( ( λ { (pair ω r) →
                            unit-trunc-Prop
                              ( pair
                                ( unit-trunc-Set ω)
                                ( map-inv-equiv
                                  ( compute-P ω)
                                  ( unit-trunc-Prop r)))}) ∘
                        ( pair-eq-Σ)))
                  ( f)

-- Proposition 1.8

is-coprod-codomain :
  {l1 l2 l3 : Level} {A1 : UU l1} {A2 : UU l2} {B : UU l3}
  (f : coprod A1 A2 → B) (e : coprod A1 A2 ≃ type-trunc-Set B)
  (H : (unit-trunc-Set ∘ f) ~ map-equiv e) →
  coprod (im (f ∘ inl)) (im (f ∘ inr)) ≃ B
is-coprod-codomain {B = B} f e H =
  pair α (is-equiv-is-emb-is-surjective is-surj-α is-emb-α)
  where
  α : coprod (im (f ∘ inl)) (im (f ∘ inr)) → B
  α = ind-coprod (λ x → B) pr1 pr1
  triangle-α : (α ∘ map-coprod (map-unit-im (f ∘ inl)) (map-unit-im (f ∘ inr))) ~ f
  triangle-α (inl a1) = refl
  triangle-α (inr a2) = refl
  is-emb-α : is-emb α
  is-emb-α =
    is-emb-coprod
      ( is-emb-pr1 (λ b → is-prop-type-trunc-Prop))
      ( is-emb-pr1 (λ b → is-prop-type-trunc-Prop))
      ( λ { (pair b1 u) (pair b2 v) →
          apply-universal-property-trunc-Prop u
            ( function-Prop _ empty-Prop)
            ( λ
              { (pair x refl) →
                apply-universal-property-trunc-Prop v
                  ( function-Prop _ empty-Prop)
                  ( λ
                    { (pair y refl) r →
                      map-compute-eq-coprod-inl-inr x y
                        ( is-injective-is-equiv
                          ( is-equiv-map-equiv e)
                          ( ( inv (H (inl x))) ∙
                            ( ( ap unit-trunc-Set r) ∙
                              ( H (inr y)))))})})})
  is-surj-α : is-surjective α
  is-surj-α b =
    apply-universal-property-trunc-Prop
      ( apply-effectiveness-unit-trunc-Set
        ( inv (issec-map-inv-equiv e (unit-trunc-Set b)) ∙ inv (H a)))
      ( trunc-Prop (fib α b))
      ( λ p →
        unit-trunc-Prop
          ( pair
            ( map-coprod (map-unit-im (f ∘ inl)) (map-unit-im (f ∘ inr)) a)
            ( triangle-α a ∙ inv p)))
    where
    a = map-inv-equiv e (unit-trunc-Set b)

is-path-connected-unit : is-path-connected unit
is-path-connected-unit =
  is-contr-equiv' unit equiv-unit-trunc-unit-Set is-contr-unit

is-contr-im :
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) {f : A → type-Set B}
  (a : A) (H : f ~ const A (type-Set B) (f a)) → is-contr (im f)
is-contr-im B {f} a H =
  pair
    ( map-unit-im f a)
    ( λ { (pair x u) →
      apply-dependent-universal-property-trunc-Prop
        ( λ v → Id-Prop (im-Set B f) (map-unit-im f a) (pair x v))
        ( u)
        ( λ { (pair a' refl) →
              eq-Eq-im f (map-unit-im f a) (map-unit-im f a') (inv (H a'))})})

is-path-connected-im :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-path-connected A → is-path-connected (im f)
is-path-connected-im {l1} {l2} {A} {B} f C =
  apply-universal-property-trunc-Prop
    ( is-inhabited-is-path-connected C)
    ( is-contr-Prop _)
    ( λ a →
      is-contr-equiv'
        ( im (map-trunc-Set f))
        ( equiv-trunc-im-Set f)
        ( is-contr-im
          ( trunc-Set B)
          ( unit-trunc-Set a)
          ( apply-dependent-universal-property-trunc-Set
            ( λ x →
              set-Prop
                ( Id-Prop
                  ( trunc-Set B)
                  ( map-trunc-Set f x)
                  ( map-trunc-Set f (unit-trunc-Set a))))
            ( λ a' →
              apply-universal-property-trunc-Prop
                ( mere-eq-is-path-connected C a' a)
                ( Id-Prop
                  ( trunc-Set B)
                  ( map-trunc-Set f (unit-trunc-Set a'))
                  ( map-trunc-Set f (unit-trunc-Set a)))
                ( λ {refl → refl})))))

is-path-connected-im-unit :
  {l1 : Level} {A : UU l1} (f : unit → A) → is-path-connected (im f)
is-path-connected-im-unit f =
  is-path-connected-im f is-path-connected-unit

has-finite-connected-components-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (k : ℕ) → (Fin k ≃ (type-trunc-Set A)) →
  ((x y : A) → has-finite-connected-components (Id x y)) → 
  ((x : A) → has-finite-connected-components (B x)) →
  has-finite-connected-components (Σ A B)
has-finite-connected-components-Σ' zero-ℕ e H K =
  is-homotopy-finite-is-empty zero-ℕ
    ( is-empty-is-empty-trunc-Set (map-inv-equiv e) ∘ pr1)
has-finite-connected-components-Σ' {l1} {l2} {A} {B} (succ-ℕ k) e H K =
  apply-universal-property-trunc-Prop
    ( has-finite-presentation-has-cardinality-components (unit-trunc-Prop e))
    ( has-finite-connected-components-Prop (Σ A B))
    ( α)
  where
  α : Σ (Fin (succ-ℕ k) → A) (λ f → is-equiv (unit-trunc-Set ∘ f)) →
      has-finite-connected-components (Σ A B)
  α (pair f Eηf) =
    is-finite-equiv
      ( equiv-trunc-Set g)
      ( is-finite-equiv'
        ( equiv-distributive-trunc-coprod-Set
          ( Σ (im (f ∘ inl)) (B ∘ pr1))
          ( Σ (im (f ∘ inr)) (B ∘ pr1)))
        ( is-finite-coprod
          ( has-finite-connected-components-Σ' k
            ( h)
            ( λ x y →
              is-finite-equiv'
                ( equiv-trunc-Set
                  ( equiv-ap-emb
                    ( pair pr1
                      ( is-emb-pr1
                        ( λ u → is-prop-type-trunc-Prop)))))
                ( H (pr1 x) (pr1 y)))
            ( λ x → K (pr1 x)))
          ( has-finite-connected-components-Σ-is-path-connected
            ( is-path-connected-im (f ∘ inr) is-path-connected-unit)
            ( pair
              ( is-finite-is-contr
                ( is-path-connected-im (f ∘ inr) is-path-connected-unit))
              ( λ x y →
                is-homotopy-finite-equiv zero-ℕ
                  ( equiv-Eq-eq-im (f ∘ inr) x y)
                  ( H (pr1 x) (pr1 y))))
            ( λ x → K (pr1 x)))))
    where
    g : coprod (Σ (im (f ∘ inl)) (B ∘ pr1)) (Σ (im (f ∘ inr)) (B ∘ pr1)) ≃
        Σ A B
    g = ( equiv-Σ B
          ( is-coprod-codomain f
            ( pair (unit-trunc-Set ∘ f) Eηf)
            ( refl-htpy))
          ( λ { (inl x) → equiv-id ;
                (inr x) → equiv-id})) ∘e
        ( inv-equiv
          ( right-distributive-Σ-coprod
            ( im (f ∘ inl))
            ( im (f ∘ inr))
            ( ind-coprod (λ x → UU _) (B ∘ pr1) (B ∘ pr1))))
    i : Fin k → type-trunc-Set (im (f ∘ inl))
    i = unit-trunc-Set ∘ map-unit-im (f ∘ inl)
    is-surjective-i : is-surjective i
    is-surjective-i =
      is-surjective-comp'
        ( is-surjective-unit-trunc-Set _)
        ( is-surjective-map-unit-im (f ∘ inl))
    is-emb-i : is-emb i
    is-emb-i =
      is-emb-right-factor
        ( (unit-trunc-Set ∘ f) ∘ inl)
        ( inclusion-trunc-im-Set (f ∘ inl))
        ( i)
        ( ( inv-htpy (naturality-trunc-Set (inclusion-im (f ∘ inl)))) ·r
          ( map-unit-im (f ∘ inl)))
        ( is-emb-inclusion-trunc-im-Set (f ∘ inl))
        ( is-emb-comp'
          ( unit-trunc-Set ∘ f)
          ( inl)
          ( is-emb-is-equiv Eηf)
          ( is-emb-inl (Fin k) unit))
    h : Fin k ≃ type-trunc-Set (im (f ∘ inl))
    h = pair i (is-equiv-is-emb-is-surjective is-surjective-i is-emb-i)

has-finite-connected-components-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-homotopy-finite one-ℕ A →
  ((x : A) → has-finite-connected-components (B x)) →
  has-finite-connected-components (Σ A B)
has-finite-connected-components-Σ {l1} {l2} {A} {B} H K =
  apply-universal-property-trunc-Prop
    ( pr1 H)
    ( has-finite-connected-components-Prop (Σ A B))
    ( λ { (pair k e) →
          has-finite-connected-components-Σ' k e (λ x y → pr2 H x y) K})

is-homotopy-finite-Σ :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : A → UU l2} →
  is-homotopy-finite (succ-ℕ k) A → ((x : A) → is-homotopy-finite k (B x)) →
  is-homotopy-finite k (Σ A B)
is-homotopy-finite-Σ zero-ℕ {A} {B} H K = has-finite-connected-components-Σ H K
is-homotopy-finite-Σ (succ-ℕ k) H K =
  pair
    ( has-finite-connected-components-Σ
      ( is-homotopy-finite-one-is-homotopy-finite-succ-ℕ (succ-ℕ k) H)
      ( λ x →
        has-finite-connected-components-is-homotopy-finite (succ-ℕ k) (K x)))
    ( λ { (pair x u) (pair y v) →
          is-homotopy-finite-equiv k
            ( equiv-pair-eq-Σ (pair x u) (pair y v))
            ( is-homotopy-finite-Σ k
              ( pr2 H x y)
              ( λ { refl → pr2 (K x) u v}))})

Homotopy-Finite-Σ :
  {l1 l2 : Level} (k : ℕ) (A : Homotopy-Finite l1 (succ-ℕ k))
  (B : (x : type-Homotopy-Finite (succ-ℕ k) A) → Homotopy-Finite l2 k) →
  Homotopy-Finite (l1 ⊔ l2) k
Homotopy-Finite-Σ k A B =
  pair
    ( Σ ( type-Homotopy-Finite (succ-ℕ k) A)
        ( λ x → type-Homotopy-Finite k (B x)))
    ( is-homotopy-finite-Σ k
      ( is-homotopy-finite-type-Homotopy-Finite (succ-ℕ k) A)
      ( λ x → is-homotopy-finite-type-Homotopy-Finite k (B x)))
