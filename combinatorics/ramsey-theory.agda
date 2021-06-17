{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module extra.ramsey-theory where

open import book public

coloring : {l : Level} (k : ℕ) → UU l → UU l
coloring k X = X → Fin k

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
