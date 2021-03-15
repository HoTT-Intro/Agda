{-# OPTIONS --without-K --exact-split #-}

module extra.russell-paradox where

open import extra.W-types public

𝕎-UU : (l : Level) → UU (lsuc l)
𝕎-UU l = 𝕎 (UU l) (λ X → X)

arity-𝕎-UU : {l : Level} → 𝕎-UU l → UU l
arity-𝕎-UU {l} = arity-𝕎 (UU l) (λ X → X)

component-𝕎-UU : {l : Level} (X : 𝕎-UU l) → arity-𝕎-UU X → 𝕎-UU l
component-𝕎-UU {l} = component-𝕎 (UU l) (λ X → X)

η-𝕎-UU :
  {l : Level} (X : 𝕎-UU l) → Id (sup-𝕎 (arity-𝕎-UU X) (component-𝕎-UU X)) X
η-𝕎-UU {l} = η-𝕎 (UU l) (λ X → X)

raise-𝕎-UU : (l : Level) {l1 : Level} → 𝕎-UU l1 → 𝕎-UU (l1 ⊔ l)
raise-𝕎-UU l = map-𝕎 id (raise l) (equiv-raise l)

is-small-𝕎-UU :
  (l : Level) {l1 : Level} → 𝕎-UU l1 → UU (l1 ⊔ lsuc l)
is-small-𝕎-UU l (sup-𝕎 A α) =
  is-small l A × ((x : A) → is-small-𝕎-UU l (α x))

arity-resize-𝕎-UU :
  {l l1 : Level} (X : 𝕎-UU l1) → is-small-𝕎-UU l X → UU l
arity-resize-𝕎-UU (sup-𝕎 A α) (pair (pair A' e) H) = A'

equiv-arity-resize-𝕎-UU :
  {l l1 : Level} (X : 𝕎-UU l1) (H : is-small-𝕎-UU l X) →
  arity-𝕎-UU X ≃ arity-resize-𝕎-UU X H
equiv-arity-resize-𝕎-UU (sup-𝕎 A α) (pair (pair A' e) H) = e

resize-𝕎-UU :
  {l1 l2 : Level} (X : 𝕎-UU l1) → is-small-𝕎-UU l2 X → 𝕎-UU l2
resize-𝕎-UU (sup-𝕎 A α) (pair (pair A' e) H2) =
  sup-𝕎 A'
    ( λ x' → resize-𝕎-UU (α (map-inv-equiv e x')) (H2 (map-inv-equiv e x')))

-- The componenthood relation on 𝕎-UU l is valued in 𝕎-UU (lsuc l)

_∈-𝕎-UU_ : {l : Level} → 𝕎-UU l → 𝕎-UU l → UU (lsuc l)
_∈-𝕎-UU_ {l} X (sup-𝕎 A α) = fib α X

-- The condition that an component of 𝕎-UU l is empty

is-empty-𝕎-UU : {l : Level} (X : 𝕎-UU l) → UU l
is-empty-𝕎-UU (sup-𝕎 A α) = is-empty A

-- The condition that an component of 𝕎-UU l has no components

_∉-𝕎-UU_ : {l : Level} → 𝕎-UU l → 𝕎-UU l → UU (lsuc l)
X ∉-𝕎-UU Y = is-empty (X ∈-𝕎-UU Y)

has-no-components-𝕎-UU :
  {l : Level} (X : 𝕎-UU l) → UU (lsuc l)
has-no-components-𝕎-UU {l} X = (Y : 𝕎-UU l) → (Y ∉-𝕎-UU X)

-- An object X of 𝕎-UU l is empty if and only if it has no components

is-empty-has-no-components-𝕎-UU :
  {l : Level} (X : 𝕎-UU l) → has-no-components-𝕎-UU X → is-empty-𝕎-UU X
is-empty-has-no-components-𝕎-UU (sup-𝕎 A α) H a =
  H (α a) (pair a refl)

has-no-components-is-empty-𝕎-UU :
  {l : Level} (X : 𝕎-UU l) → is-empty-𝕎-UU X → has-no-components-𝕎-UU X
has-no-components-is-empty-𝕎-UU (sup-𝕎 A α) H (sup-𝕎 B β) t = H (pr1 t)

fam-𝕎-UU :
  (l : Level) {l1 : Level} (X : 𝕎-UU l1) → UU (l1 ⊔ lsuc l)
fam-𝕎-UU l (sup-𝕎 A α) = A → 𝕎-UU l

flatten-𝕎-UU : {l : Level} → 𝕎-UU l → 𝕎-UU l
flatten-𝕎-UU {l} (sup-𝕎 A α) =
  sup-𝕎
    ( Σ A (λ x → arity-𝕎-UU (α x)))
    ( ind-Σ (λ x → component-𝕎-UU (α x)))

subtree-𝕎-UU :
  {l : Level} (X : 𝕎-UU l) → (P : arity-𝕎-UU X → UU-Prop l) → 𝕎-UU l
subtree-𝕎-UU X P =
  sup-𝕎 (Σ (arity-𝕎-UU X) (λ x → type-Prop (P x))) ((component-𝕎-UU X) ∘ pr1)

tree-of-trees-𝕎-UU :
  (l : Level) → 𝕎-UU (lsuc l)
tree-of-trees-𝕎-UU l = sup-𝕎 (𝕎-UU l) (raise-𝕎-UU (lsuc l))

Russell : (l : Level) → 𝕎-UU (lsuc l)
Russell l =
  subtree-𝕎-UU
    ( tree-of-trees-𝕎-UU l)
    ( λ X → neg-Prop' (X ∈-𝕎-UU X))

is-small-universe :
  (l l1 : Level) → UU (lsuc l1 ⊔ lsuc l)
is-small-universe l l1 = is-small l (UU l1) × ((X : UU l1) → is-small l X)

is-small-tree-of-trees-𝕎-UU :
  (l : Level) {l1 : Level} →
  is-small-universe l l1 → is-small-𝕎-UU l (tree-of-trees-𝕎-UU l1)
is-small-tree-of-trees-𝕎-UU l (pair (pair U e) H) =
  pair
    ( pair
      ( 𝕎 U (λ x → pr1 (H (map-inv-equiv e x))))
      {! equiv-𝕎!})
    {!!}

paradox-Russell : {l : Level} → ¬ (is-small l (UU l))
paradox-Russell (pair A e) = {!!}

--------------------------------------------------------------------------------

module 𝕎-monoid

  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (ε₀ : (x : A) → (B x → A) → A)
--  (ε1 : {x : A} (y : B x) → B (ε0 x y) → B x)
--  (α0 : (x : A) (y : B x) (z : B (ε0 x y)) → Id (ε0 (ε0 x y) z) (ε0 x (ε1 y z)))
--  (α1 : {x : A} (y : B x) (z : B (ε0 x y)) (w : B (ε0 (ε0 x y) z)) →
--        Id (ε1 (ε1 y z) (tr B (α0 x y z) w)) (ε1 y (ε1 z w)))

  where

  μ-𝕎 : 𝕎 A B → 𝕎 A B
  μ-𝕎 (sup-𝕎 x α) =
    sup-𝕎 ( ε₀ x (λ y → arity-𝕎 A B (α y)))
           ( λ y → {!component-𝕎 A B!})
