{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module type-theories.syntax-of-type-theories where

open import book public

iterate-using-add :
  {l1 : Level} {A : ℕ → UU l1} (f : (n : ℕ) → A (succ-ℕ n) → A n) →
  (m n : ℕ) → A (add-ℕ m n) → A m
iterate-using-add f m zero-ℕ = id
iterate-using-add f m (succ-ℕ n) = iterate-using-add f m n ∘ f (add-ℕ m n)

interleaved mutual

data type-expr : ℕ → Set

data type-eq : {n : ℕ} (A B : type-expr n) → Set

data term-expr : {n : ℕ} (A : type-expr n) → Set

data term-eq : {n : ℕ} {A : type-expr n} (a b : term-expr A) → Set

data type-expr where
  ft-expr : {n : ℕ} → type-expr (succ-ℕ n) → type-expr n
  S-expr  : {n m : ℕ} {A : type-expr n} (a : term-expr A) →
            (B : type-expr (succ-ℕ (add-ℕ n m))) →
            type-eq A (iterate-using-add (λ x → ft-expr {x}) n (succ-ℕ m) B) →
            type-expr (add-ℕ n m)
  W0-expr : {m : ℕ} (A : type-expr zero-ℕ) →
            type-expr m → type-expr (succ-ℕ m)
  W-expr  : {n m : ℕ} (A : type-expr (succ-ℕ n))
            (B : type-expr (add-ℕ (succ-ℕ n) m)) →
            type-eq
              ( ft-expr A)
              ( ft-expr
                ( iterate-using-add (λ x → ft-expr {x}) (succ-ℕ n) m B)) →
            type-expr (succ-ℕ (add-ℕ (succ-ℕ n) m))
  Π-expr  : (n : ℕ) (A : type-expr n) (B : type-expr (succ-ℕ n)) →
            type-eq (ft-expr B) A → type-expr n
  Σ-expr  : (n : ℕ) (A : type-expr n) (B : type-expr (succ-ℕ n)) →
            type-eq (ft-expr B) A → type-expr n
  Id-expr : (n : ℕ) → type-expr n → type-expr (succ-ℕ (succ-ℕ n))
  U-expr  : list (Σ ℕ type-expr) → type-expr zero-ℕ
  El-expr : (l : list (Σ ℕ type-expr)) → type-expr one-ℕ
  ℕ-expr  : type-expr zero-ℕ
  empty-expr : type-expr zero-ℕ
  unit-expr : type-expr zero-ℕ

data term-expr where
  conv-expr : {n : ℕ} {A B : type-expr n} (e : type-eq A B) →
              term-expr A → term-expr B
  δ0-expr : (A : type-expr zero-ℕ) → term-expr (W0-expr A A)
--  δ-expr : {n : ℕ} (A : type-expr (succ-ℕ n)) →
--           term-expr (W-expr {n} {zero-ℕ} A A (refl-eq (ft-expr A)))
  S-expr : {n m : ℕ} {A : type-expr n} (a : term-expr A) →
           {B : type-expr (succ-ℕ (add-ℕ n m))} →
           (e : type-eq A
                  ( iterate-using-add (λ x → ft-expr {x}) n (succ-ℕ m) B)) →
           term-expr B → term-expr (type-expr.S-expr a B e)
  zero-expr : term-expr type-expr.ℕ-expr

data type-eq where
  refl-eq : {n : ℕ} (A : type-expr n) → type-eq A A
  S-cong  : {n m : ℕ} {A A' : type-expr n} (e : type-eq A A')
            {a : term-expr A} {a' : term-expr A'}
            (f : term-eq (conv-expr e a) a')
            {B B' : type-expr (succ-ℕ (add-ℕ n m))}
            (e : type-eq A
                   ( iterate-using-add (λ x → ft-expr {x}) n (succ-ℕ m) B)) →
            (e' : type-eq A'
                    ( iterate-using-add (λ x → ft-expr {x}) n (succ-ℕ m) B')) →
            type-eq B B' →
            type-eq (S-expr a B e) (S-expr a' B' e')

data term-eq where
  refl-eq : {n : ℕ} {A : type-expr n} (a : term-expr A) → term-eq a a
