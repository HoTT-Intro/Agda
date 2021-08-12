{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module extra.quaternion-group where

open import book public

cube : ℕ → UU (lsuc lzero)
cube d = Σ (UU-Fin d) (λ X → type-UU-Fin X → UU-Fin two-ℕ)

dim-cube-UU-Fin : {d : ℕ} (c : cube d) → UU-Fin d
dim-cube-UU-Fin c = pr1 c

dim-cube : {k : ℕ} → cube k → UU lzero
dim-cube c = type-UU-Fin (dim-cube-UU-Fin c)

has-finite-cardinality-dim-cube :
  {k : ℕ} (c : cube k) → has-finite-cardinality (dim-cube c)
has-finite-cardinality-dim-cube {k} c =
  pair k (pr2 (dim-cube-UU-Fin c))

is-finite-dim-cube :
  {k : ℕ} (c : cube k) → is-finite (dim-cube c)
is-finite-dim-cube c =
  is-finite-has-finite-cardinality (has-finite-cardinality-dim-cube c)

axis-cube-UU-2 :
  {d : ℕ} (c : cube d) → dim-cube c → UU-Fin two-ℕ
axis-cube-UU-2 c = pr2 c

axis-cube : {d : ℕ} (c : cube d) → dim-cube c → UU lzero
axis-cube c i = type-UU-Fin (axis-cube-UU-2 c i)

vertex-cube : {d : ℕ} (c : cube d) → UU lzero
vertex-cube c = (d : dim-cube c) → axis-cube c d

standard-cube : (k : ℕ) → cube k
standard-cube k =
  pair
    ( pair (Fin k) (unit-trunc-Prop equiv-id))
    ( λ x → pair (Fin two-ℕ) (unit-trunc-Prop equiv-id))

labelling-cube : {k : ℕ} (c : cube k) → UU (lsuc lzero)
labelling-cube {k} c = Id (standard-cube k) c

orientation-cube : {k : ℕ} → cube k → UU (lzero)
orientation-cube {k} c =
  Σ ( vertex-cube c → Fin two-ℕ)
    ( λ h →
      ( x y : vertex-cube c) →
        Id ( iterate
             ( number-of-elements-is-finite
               ( is-finite-Σ
                 ( is-finite-dim-cube c)
                 ( λ d →
                   is-finite-function-type
                     ( is-finite-eq
                       ( has-decidable-equality-is-finite
                         ( is-finite-has-finite-cardinality
                           ( pair two-ℕ (pr2 (axis-cube-UU-2 c d)))))
                     { x d}
                     { y d})
                     ( is-finite-empty))))
             ( succ-Fin)
             ( h x))
           ( h y))

face-cube :
  {k : ℕ} (c : cube (succ-ℕ k)) (d : dim-cube c) (a : axis-cube c d) → cube k
face-cube c d a =
  pair ( complement-point-UU-Fin' (pair (dim-cube-UU-Fin c) d))
       ( λ d' →
         axis-cube-UU-2 c
           ( inclusion-complement-point-UU-Fin'
             ( pair (dim-cube-UU-Fin c) d) d'))
