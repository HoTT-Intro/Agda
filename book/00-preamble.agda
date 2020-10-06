{-# OPTIONS --without-K --exact-split --safe #-}

module book.00-preamble where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public

UU : (i : Level) → Set (lsuc i)
UU i = Set i

data raise (l : Level) {l1 : Level} (A : UU l1) : UU (l1 ⊔ l) where
  map-raise : A → raise l A

inv-map-raise :
  {l l1 : Level} {A : UU l1} → raise l A → A
inv-map-raise (map-raise x) = x
