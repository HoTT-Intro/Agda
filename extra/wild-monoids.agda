{-# OPTIONS --without-K --exact-split #-}

module extra.wild-monoids where

open import extra.lists public

Wild-Monoid : (l : Level) → UU (lsuc l)
Wild-Monoid l =
  Σ ( Σ ( UU l)
        ( λ X →
          Σ ( X → X → X)
            ( λ μ →
              ( x y z : X) → Id (μ (μ x y) z) (μ x (μ y z)))))
    ( λ Xμ →
      Σ ( pr1 Xμ)
        ( λ e →
          ( (x : pr1 Xμ) → Id (pr1 (pr2 Xμ) e x) x) ×
          ( ((x : pr1 Xμ) → Id (pr1 (pr2 Xμ) x e) x))))

type-Wild-Monoid :
  {l : Level} → Wild-Monoid l → UU l
type-Wild-Monoid X = pr1 (pr1 X)

mul-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l) →
  type-Wild-Monoid M → type-Wild-Monoid M → type-Wild-Monoid M
mul-Wild-Monoid M = pr1 (pr2 (pr1 M))

ap-mul-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l) {a b c d : type-Wild-Monoid M} →
  Id a b → Id c d → Id (mul-Wild-Monoid M a c) (mul-Wild-Monoid M b d)
ap-mul-Wild-Monoid M p q = ap-binary (mul-Wild-Monoid M) p q

associative-mul-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l) (x y z : type-Wild-Monoid M) →
  Id ( mul-Wild-Monoid M (mul-Wild-Monoid M x y) z)
     ( mul-Wild-Monoid M x (mul-Wild-Monoid M y z))
associative-mul-Wild-Monoid M = pr2 (pr2 (pr1 M))

unit-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l) → type-Wild-Monoid M
unit-Wild-Monoid M = pr1 (pr2 M)

left-unit-law-mul-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l) (x : type-Wild-Monoid M) →
  Id (mul-Wild-Monoid M (unit-Wild-Monoid M) x) x
left-unit-law-mul-Wild-Monoid M = pr1 (pr2 (pr2 M))

right-unit-law-mul-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l) (x : type-Wild-Monoid M) →
  Id (mul-Wild-Monoid M x (unit-Wild-Monoid M)) x
right-unit-law-mul-Wild-Monoid M = pr2 (pr2 (pr2 M))

hom-Wild-Monoid :
  {l1 l2 : Level} (M : Wild-Monoid l1) (N : Wild-Monoid l2) → UU (l1 ⊔ l2)
hom-Wild-Monoid M N =
  Σ ( Σ ( type-Wild-Monoid M → type-Wild-Monoid N)
        ( λ f →
          ( x y : type-Wild-Monoid M) →
          Id (f (mul-Wild-Monoid M x y)) (mul-Wild-Monoid N (f x) (f y))))
    ( λ fμ → Id (pr1 fμ (unit-Wild-Monoid M)) (unit-Wild-Monoid N))

map-hom-Wild-Monoid :
  {l1 l2 : Level} (M : Wild-Monoid l1) (N : Wild-Monoid l2) →
  hom-Wild-Monoid M N → type-Wild-Monoid M → type-Wild-Monoid N
map-hom-Wild-Monoid M N f = pr1 (pr1 f)

preserves-mul-map-hom-Wild-Monoid :
  {l1 l2 : Level} (M : Wild-Monoid l1) (N : Wild-Monoid l2)
  (f : hom-Wild-Monoid M N) (x y : type-Wild-Monoid M) →
  Id (map-hom-Wild-Monoid M N f (mul-Wild-Monoid M x y))
     (mul-Wild-Monoid N (map-hom-Wild-Monoid M N f x) (map-hom-Wild-Monoid M N f y))
preserves-mul-map-hom-Wild-Monoid M N f = pr2 (pr1 f)

preserves-unit-map-hom-Wild-Monoid :
  {l1 l2 : Level} (M : Wild-Monoid l1) (N : Wild-Monoid l2)
  (f : hom-Wild-Monoid M N) →
  Id (map-hom-Wild-Monoid M N f (unit-Wild-Monoid M))
     (unit-Wild-Monoid N)
preserves-unit-map-hom-Wild-Monoid M N f = pr2 f

htpy-hom-Wild-Monoid :
  {l1 l2 : Level} (M : Wild-Monoid l1) (N : Wild-Monoid l2)
  (f g : hom-Wild-Monoid M N) → UU (l1 ⊔ l2)
htpy-hom-Wild-Monoid M N f g =
  Σ ( Σ ( map-hom-Wild-Monoid M N f ~ map-hom-Wild-Monoid M N g)
        ( λ H →
          ( x y : type-Wild-Monoid M) →
          Id ( ( preserves-mul-map-hom-Wild-Monoid M N f x y) ∙
               ( ap-mul-Wild-Monoid N (H x) (H y)))
             ( ( H (mul-Wild-Monoid M x y)) ∙
               ( preserves-mul-map-hom-Wild-Monoid M N g x y))))
    ( λ Hμ →
      Id ( preserves-unit-map-hom-Wild-Monoid M N f)
         ( pr1 Hμ (unit-Wild-Monoid M) ∙ preserves-unit-map-hom-Wild-Monoid M N g))

refl-htpy-hom-Wild-Monoid :
  {l1 l2 : Level} (M : Wild-Monoid l1) (N : Wild-Monoid l2)
  (f : hom-Wild-Monoid M N) → htpy-hom-Wild-Monoid M N f f
refl-htpy-hom-Wild-Monoid M N f =
  pair (pair refl-htpy (λ x y → right-unit)) refl

{-
is-contr-total-htpy-hom-Wild-Monoid :
  {l1 l2 : Level} (M : Wild-Monoid l1) (N : Wild-Monoid l2)
  (f : hom-Wild-Monoid M N) →
  is-contr (Σ (hom-Wild-Monoid M N) (htpy-hom-Wild-Monoid M N f))
is-contr-total-htpy-hom-Wild-Monoid M N f =
  is-contr-total-Eq-structure
    {! λ fμ p!}
    {!!}
    {!!}
    {!!}
-}

list-Wild-Monoid : {l : Level} → UU l → Wild-Monoid l
list-Wild-Monoid X =
  pair
    ( pair (list X) (pair concat-list assoc-concat-list))
    ( pair nil (pair left-unit-law-concat-list right-unit-law-concat-list))
