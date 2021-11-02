{-# OPTIONS --without-K --allow-unsolved-metas #-}

module extra.universes where

open import book public

record universe-structure
  {l1 l2 : Level} {U : UU l1} (El : U → UU l2) : UU (l1 ⊔ l2)
  where
  field
    name-Π : (A : U) (B : El A → U) → U
    El-Π : (A : U) (B : El A → U) → El (name-Π A B) ≃ ((x : El A) → El (B x))
    name-Σ : (A : U) (B : El A → U) → U
    El-Σ : (A : U) (B : El A → U) → El (name-Σ A B) ≃ Σ (El A) (λ x → El (B x))
    name-Id : (A : U) (x y : El A) → U
    El-Id : (A : U) (x y : El A) → El (name-Id A x y) ≃ Id x y
    name-∅ : U
    El-∅ : El name-∅ ≃ empty
    name-1 : U
    El-1 : El name-1 ≃ unit
    name-ℕ : U
    El-ℕ : El name-ℕ ≃ ℕ

record super-universe-structure
  {l1 l2 : Level} {U : UU l1} (El : U → UU l2) : UU (l1 ⊔ l2)
  where
  field
    su-str  : universe-structure El
    name-U  : list (Σ U (λ A → El A → U)) → U
    name-El : (l : list (Σ U (λ A → El A → U))) → El (name-U l) → U
    u-str   : (l : list (Σ U (λ A → El A → U))) →
              universe-structure (λ (X : El (name-U l)) → El (name-El l X))
