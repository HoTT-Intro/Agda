{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-combinatorics.ramsey-theory where

open import book public

coloring : {l : Level} (k : ℕ) → UU l → UU l
coloring k X = X → Fin k

full-subset : {l : Level} (X : UU l) → X → UU-Prop lzero
full-subset X x = unit-Prop

subset-of-size : (k : ℕ) → 𝔽 → UU (lsuc lzero)
subset-of-size k X =
  Σ ( type-𝔽 X → UU-Prop lzero)
    ( λ P → has-cardinality (Σ (type-𝔽 X) (λ x → type-Prop (P x))) k)

is-ramsey-set : {k : ℕ} (q : Fin k → ℕ) (r : ℕ) (A : 𝔽) → UU (lsuc lzero)
is-ramsey-set {k} q r A =
  (c : coloring k (subset-of-size r A)) →
  Σ ( Fin k)
    ( λ i →
      Σ ( subset-of-size (q i) A)
        ( λ P →
          (Q : subset-of-size r A) →
          ((x : type-𝔽 A) → type-Prop ((pr1 Q) x) → type-Prop ((pr1 P) x)) →
          Id (c Q) i))
{-
is-ramsey-set-empty-coloring : (r : ℕ) → is-ramsey-set ex-falso r empty-𝔽
is-ramsey-set-empty-coloring zero-ℕ c = {!!}
is-ramsey-set-empty-coloring (succ-ℕ r) c = {!!}
  

is-ramsey-set-Fin-r :
  {k : ℕ} (q : Fin k → ℕ) (r : ℕ) → fib q r → is-ramsey-set q r (Fin-𝔽 r)
is-ramsey-set-Fin-r q .(q i) (pair i refl) c =
  pair
    ( c R)
    ( pair
      {!!}
      {!!})
    where
    R : subset-of-size (q i) (Fin-𝔽 (q i))
    R = pair
          ( full-subset (Fin (q i)))
          ( unit-trunc-Prop (inv-equiv right-unit-law-prod))
    {-
    ( pair
      ( pair ( full-subset (Fin {!!}))
             ( unit-trunc-Prop (inv-equiv right-unit-law-prod)))
      ( λ Q H → {!!}))
-}
-}
