{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module extra.quaternion-group where

open import book public

cube : ℕ → UU (lsuc lzero)
cube d = Σ (UU-Fin d) (λ X → type-UU-Fin X → UU-Fin two-ℕ)

dim-cube-UU-Fin : {d : ℕ} (c : cube d) → UU-Fin d
dim-cube-UU-Fin c = pr1 c

dim-cube : {d : ℕ} → cube d → UU lzero
dim-cube c = type-UU-Fin (dim-cube-UU-Fin c)

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
                 ( is-finite-has-finite-cardinality
                   ( pair k (pr2 (dim-cube-UU-Fin c))))
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

coprod-UU-Fin' :
  {l1 l2 : Level} {k l : ℕ} → UU-Fin' l1 k → UU-Fin' l2 l →
  UU-Fin' (l1 ⊔ l2) (add-ℕ k l)
coprod-UU-Fin' {l1} {l2} {k} {l} (pair X H) (pair Y K) =
  pair
    ( coprod X Y)
    ( apply-universal-property-trunc-Prop H
      ( mere-equiv-Prop (Fin (add-ℕ k l)) (coprod X Y))
      ( λ e1 →
        apply-universal-property-trunc-Prop K
          ( mere-equiv-Prop (Fin (add-ℕ k l)) (coprod X Y))
          ( λ e2 →
            unit-trunc-Prop
              ( equiv-coprod e1 e2 ∘e inv-equiv (coprod-Fin k l)))))

coprod-UU-Fin :
  {k l : ℕ} → UU-Fin k → UU-Fin l → UU-Fin (add-ℕ k l)
coprod-UU-Fin X Y = coprod-UU-Fin' X Y

unit-UU-Fin : UU-Fin one-ℕ
unit-UU-Fin = pair unit (unit-trunc-Prop (left-unit-law-coprod unit))

add-free-point-UU-Fin' :
  {l1 : Level} {k : ℕ} → UU-Fin' l1 k → UU-Fin' l1 (succ-ℕ k)
add-free-point-UU-Fin' X = coprod-UU-Fin' X unit-UU-Fin

face-cube :
  (d : ℕ) (c : cube (succ-ℕ d)) (i : dim-cube c) (a : axis-cube c i) →
  cube d
face-cube c i a = {!!}
