{-# OPTIONS --without-K --exact-split #-}

module extra.wild-unital-magma where

open import extra.lists public
open import extra.interchange public

unital-mul :
  {l : Level} → UU-pt l → UU l
unital-mul X =
  Σ ( type-UU-pt X → type-UU-pt X → type-UU-pt X)
    ( λ μ →
      Σ ( (x : type-UU-pt X) → Id (μ (pt-UU-pt X) x) x)
        ( λ α →
          Σ ( (x : type-UU-pt X) → Id (μ x (pt-UU-pt X)) x)
            ( λ β → Id (α (pt-UU-pt X)) (β (pt-UU-pt X)))))

Wild-Unital-Magma : (l : Level) → UU (lsuc l)
Wild-Unital-Magma l =
  Σ ( UU-pt l) unital-mul

pointed-type-Wild-Unital-Magma :
  {l : Level} (M : Wild-Unital-Magma l) → UU-pt l
pointed-type-Wild-Unital-Magma = pr1

type-Wild-Unital-Magma :
  {l : Level} (M : Wild-Unital-Magma l) → UU l
type-Wild-Unital-Magma M = type-UU-pt (pointed-type-Wild-Unital-Magma M)

unit-Wild-Unital-Magma :
  {l : Level} (M : Wild-Unital-Magma l) → type-Wild-Unital-Magma M
unit-Wild-Unital-Magma M = pt-UU-pt (pointed-type-Wild-Unital-Magma M)

unital-mul-Wild-Unital-Magma :
  {l : Level} (M : Wild-Unital-Magma l) →
  unital-mul (pointed-type-Wild-Unital-Magma M)
unital-mul-Wild-Unital-Magma = pr2

mul-Wild-Unital-Magma :
  {l : Level} (M : Wild-Unital-Magma l) →
  type-Wild-Unital-Magma M → type-Wild-Unital-Magma M → type-Wild-Unital-Magma M
mul-Wild-Unital-Magma M = pr1 (unital-mul-Wild-Unital-Magma M)

mul-Wild-Unital-Magma' :
  {l : Level} (M : Wild-Unital-Magma l) →
  type-Wild-Unital-Magma M → type-Wild-Unital-Magma M → type-Wild-Unital-Magma M
mul-Wild-Unital-Magma' M x y = mul-Wild-Unital-Magma M y x

ap-mul-Wild-Unital-Magma :
  {l : Level} (M : Wild-Unital-Magma l) →
  {a b c d : type-Wild-Unital-Magma M} → Id a b → Id c d →
  Id (mul-Wild-Unital-Magma M a c) (mul-Wild-Unital-Magma M b d)
ap-mul-Wild-Unital-Magma M p q = ap-binary (mul-Wild-Unital-Magma M) p q

left-unit-law-mul-Wild-Unital-Magma :
  {l : Level} (M : Wild-Unital-Magma l) (x : type-Wild-Unital-Magma M) →
  Id (mul-Wild-Unital-Magma M (unit-Wild-Unital-Magma M) x) x
left-unit-law-mul-Wild-Unital-Magma M =
  pr1 (pr2 (unital-mul-Wild-Unital-Magma M))

right-unit-law-mul-Wild-Unital-Magma :
  {l : Level} (M : Wild-Unital-Magma l) (x : type-Wild-Unital-Magma M) →
  Id (mul-Wild-Unital-Magma M x (unit-Wild-Unital-Magma M)) x
right-unit-law-mul-Wild-Unital-Magma M =
  pr1 (pr2 (pr2 (unital-mul-Wild-Unital-Magma M)))

coh-unit-laws-mul-Wild-Unital-Magma :
  {l : Level} (M : Wild-Unital-Magma l) →
  Id (left-unit-law-mul-Wild-Unital-Magma M (unit-Wild-Unital-Magma M))
     (right-unit-law-mul-Wild-Unital-Magma M (unit-Wild-Unital-Magma M))
coh-unit-laws-mul-Wild-Unital-Magma M =
  pr2 (pr2 (pr2 (unital-mul-Wild-Unital-Magma M)))

list-Wild-Unital-Magma :
  {l : Level} (X : UU l) → Wild-Unital-Magma l
list-Wild-Unital-Magma X =
  pair
    ( pair (list X) nil)
    ( pair
      ( concat-list)
      ( pair
        ( left-unit-law-concat-list)
        ( pair right-unit-law-concat-list refl)))

-- We describe morphisms that reserve unital multiplication

preserves-left-unit-law-mul :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (μ : A → A → A) {eA : A} → ((x : A) → Id (μ eA x) x) →
  (ν : B → B → B) {eB : B} → ((y : B) → Id (ν eB y) y) →
  (f : A → B) → Id (f eA) eB → preserves-mul μ ν f → UU (l1 ⊔ l2)
preserves-left-unit-law-mul {A = A} {B} μ {eA} lA ν {eB} lB f p μf =
  (x : A) → Id (ap f (lA x)) (μf eA x ∙ (ap (λ t → ν t (f x)) p ∙ lB (f x)))

preserves-right-unit-law-mul :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (μ : A → A → A) {eA : A} → ((x : A) → Id (μ x eA) x) →
  (ν : B → B → B) {eB : B} → ((y : B) → Id (ν y eB) y) →
  (f : A → B) → Id (f eA) eB → preserves-mul μ ν f → UU (l1 ⊔ l2)
preserves-right-unit-law-mul {A = A} {B} μ {eA} rA ν {eB} rB f p μf =
  (x : A) → Id (ap f (rA x)) (μf x eA ∙ (ap (ν (f x)) p ∙ rB (f x)))

preserves-coh-unit-laws-mul :
  {l1 l2 : Level} (M : Wild-Unital-Magma l1) (N : Wild-Unital-Magma l2) →
  ( f : pointed-type-Wild-Unital-Magma M →* pointed-type-Wild-Unital-Magma N) →
  ( μf :
    preserves-mul (mul-Wild-Unital-Magma M) (mul-Wild-Unital-Magma N) (pr1 f)) →
  preserves-left-unit-law-mul
    ( mul-Wild-Unital-Magma M)
    ( left-unit-law-mul-Wild-Unital-Magma M)
    ( mul-Wild-Unital-Magma N)
    ( left-unit-law-mul-Wild-Unital-Magma N)
    ( pr1 f)
    ( pr2 f)
    ( μf) →
  preserves-right-unit-law-mul
    ( mul-Wild-Unital-Magma M)
    ( right-unit-law-mul-Wild-Unital-Magma M)
    ( mul-Wild-Unital-Magma N)
    ( right-unit-law-mul-Wild-Unital-Magma N)
    ( pr1 f)
    ( pr2 f)
    ( μf) →
  UU l2
preserves-coh-unit-laws-mul M
  (pair (pair B .(f (pr2 (pr1 M)))) (pair ν (pair lB (pair rB cB))))
  (pair f refl) μf lf rf = 
  Id (ap (ap f) cA ∙ rf eA) (lf eA ∙ ap (concat (μf eA eA) (f eA)) cB)
  where
  cA = coh-unit-laws-mul-Wild-Unital-Magma M
  eA = unit-Wild-Unital-Magma M

preserves-unital-mul :
  {l1 l2 : Level} (M : Wild-Unital-Magma l1) (N : Wild-Unital-Magma l2) →
  (f : pointed-type-Wild-Unital-Magma M →* pointed-type-Wild-Unital-Magma N) →
  UU (l1 ⊔ l2)
preserves-unital-mul M N f =
  Σ ( preserves-mul μM μN (pr1 f))
    ( λ μ11 →
      Σ ( preserves-left-unit-law-mul μM lM μN lN (pr1 f) (pr2 f) μ11)
        ( λ μ01 →
          Σ ( preserves-right-unit-law-mul μM rM μN rN (pr1 f) (pr2 f) μ11)
            ( λ μ10 → preserves-coh-unit-laws-mul M N f μ11 μ01 μ10)))
  where
  μM = mul-Wild-Unital-Magma M
  lM = left-unit-law-mul-Wild-Unital-Magma M
  rM = right-unit-law-mul-Wild-Unital-Magma M
  μN = mul-Wild-Unital-Magma N
  lN = left-unit-law-mul-Wild-Unital-Magma N
  rN = right-unit-law-mul-Wild-Unital-Magma N

hom-Wild-Unital-Magma :
  {l1 l2 : Level} (M : Wild-Unital-Magma l1) (N : Wild-Unital-Magma l2) →
  UU (l1 ⊔ l2)
hom-Wild-Unital-Magma M N =
  Σ ( pointed-type-Wild-Unital-Magma M →* pointed-type-Wild-Unital-Magma N)
    ( preserves-unital-mul M N)
