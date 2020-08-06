{-# OPTIONS --without-K --exact-split #-}

module W-types where

import 17-number-theory
open 17-number-theory public

data 𝕎 {i j : Level} (A : UU i) (B : A → UU j) : UU (i ⊔ j) where
  sup-𝕎 : (x : A) (α : B x → 𝕎 A B) → 𝕎 A B

Eq-𝕎 :
  {i j : Level} {A : UU i} {B : A → UU j} →
  𝕎 A B → 𝕎 A B → UU (i ⊔ j)
Eq-𝕎 {B = B} (sup-𝕎 x α) (sup-𝕎 y β) =
  Σ (Id x y) (λ p → (z : B x) → Eq-𝕎 (α z) (β (tr B p z))) 

refl-Eq-𝕎 :
  {i j : Level} {A : UU i} {B : A → UU j} →
  (w : 𝕎 A B) → Eq-𝕎 w w
refl-Eq-𝕎 (sup-𝕎 x α) = pair refl (λ z → refl-Eq-𝕎 (α z))

center-total-Eq-𝕎 :
  {i j : Level} {A : UU i} {B : A → UU j} →
  (w : 𝕎 A B) → Σ (𝕎 A B) (Eq-𝕎 w)
center-total-Eq-𝕎 w = pair w (refl-Eq-𝕎 w)

aux-total-Eq-𝕎 :
  {i j : Level} {A : UU i} {B : A → UU j} (x : A) (α : B x → 𝕎 A B) →
  Σ (B x → 𝕎 A B) (λ β → (y : B x) → Eq-𝕎 (α y) (β y)) →
  Σ (𝕎 A B) (Eq-𝕎 (sup-𝕎 x α))
aux-total-Eq-𝕎 x α (pair β e) = pair (sup-𝕎 x β) (pair refl e)

contraction-total-Eq-𝕎 :
  {i j : Level} {A : UU i} {B : A → UU j} (w : 𝕎 A B) →
  (t : Σ (𝕎 A B) (Eq-𝕎 w)) → Id (center-total-Eq-𝕎 w) t
contraction-total-Eq-𝕎 {i} {j} {A} {B}
  ( sup-𝕎 x α) (pair (sup-𝕎 .x β) (pair refl e)) =
  ap ( ( aux-total-Eq-𝕎 x α) ∘
       ( choice-∞ {A = B x} {B = λ y → 𝕎 A B} {C = λ y → Eq-𝕎 (α y)}))
     { x = λ y → pair (α y) (refl-Eq-𝕎 (α y))}
     { y = λ y → pair (β y) (e y)}
     ( eq-htpy (λ y → contraction-total-Eq-𝕎 (α y) (pair (β y) (e y))))

is-contr-total-Eq-𝕎 :
  {i j : Level} {A : UU  i} {B : A → UU j} →
  (w : 𝕎 A B) → is-contr (Σ (𝕎 A B) (Eq-𝕎 w))
is-contr-total-Eq-𝕎 w =
  pair
    ( center-total-Eq-𝕎 w)
    ( contraction-total-Eq-𝕎 w)
