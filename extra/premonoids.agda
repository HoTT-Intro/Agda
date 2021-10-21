{-# OPTIONS --without-K --exact-split #-}

module extra.premonoids where

open import extra.lists public

Premonoid : (l : Level) → UU (lsuc l)
Premonoid l =
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

type-Premonoid :
  {l : Level} → Premonoid l → UU l
type-Premonoid X = pr1 (pr1 X)

mul-Premonoid :
  {l : Level} (M : Premonoid l) →
  type-Premonoid M → type-Premonoid M → type-Premonoid M
mul-Premonoid M = pr1 (pr2 (pr1 M))

ap-mul-Premonoid :
  {l : Level} (M : Premonoid l) {a b c d : type-Premonoid M} →
  Id a b → Id c d → Id (mul-Premonoid M a c) (mul-Premonoid M b d)
ap-mul-Premonoid M p q = ap-binary (mul-Premonoid M) p q

associative-mul-Premonoid :
  {l : Level} (M : Premonoid l) (x y z : type-Premonoid M) →
  Id ( mul-Premonoid M (mul-Premonoid M x y) z)
     ( mul-Premonoid M x (mul-Premonoid M y z))
associative-mul-Premonoid M = pr2 (pr2 (pr1 M))

unit-Premonoid :
  {l : Level} (M : Premonoid l) → type-Premonoid M
unit-Premonoid M = pr1 (pr2 M)

left-unit-law-mul-Premonoid :
  {l : Level} (M : Premonoid l) (x : type-Premonoid M) →
  Id (mul-Premonoid M (unit-Premonoid M) x) x
left-unit-law-mul-Premonoid M = pr1 (pr2 (pr2 M))

right-unit-law-mul-Premonoid :
  {l : Level} (M : Premonoid l) (x : type-Premonoid M) →
  Id (mul-Premonoid M x (unit-Premonoid M)) x
right-unit-law-mul-Premonoid M = pr2 (pr2 (pr2 M))

hom-Premonoid :
  {l1 l2 : Level} (M : Premonoid l1) (N : Premonoid l2) → UU (l1 ⊔ l2)
hom-Premonoid M N =
  Σ ( Σ ( type-Premonoid M → type-Premonoid N)
        ( λ f →
          ( x y : type-Premonoid M) →
          Id (f (mul-Premonoid M x y)) (mul-Premonoid N (f x) (f y))))
    ( λ fμ → Id (pr1 fμ (unit-Premonoid M)) (unit-Premonoid N))

map-hom-Premonoid :
  {l1 l2 : Level} (M : Premonoid l1) (N : Premonoid l2) →
  hom-Premonoid M N → type-Premonoid M → type-Premonoid N
map-hom-Premonoid M N f = pr1 (pr1 f)

preserves-mul-map-hom-Premonoid :
  {l1 l2 : Level} (M : Premonoid l1) (N : Premonoid l2)
  (f : hom-Premonoid M N) (x y : type-Premonoid M) →
  Id (map-hom-Premonoid M N f (mul-Premonoid M x y))
     (mul-Premonoid N (map-hom-Premonoid M N f x) (map-hom-Premonoid M N f y))
preserves-mul-map-hom-Premonoid M N f = pr2 (pr1 f)

preserves-unit-map-hom-Premonoid :
  {l1 l2 : Level} (M : Premonoid l1) (N : Premonoid l2)
  (f : hom-Premonoid M N) →
  Id (map-hom-Premonoid M N f (unit-Premonoid M))
     (unit-Premonoid N)
preserves-unit-map-hom-Premonoid M N f = pr2 f

htpy-hom-Premonoid :
  {l1 l2 : Level} (M : Premonoid l1) (N : Premonoid l2)
  (f g : hom-Premonoid M N) → UU (l1 ⊔ l2)
htpy-hom-Premonoid M N f g =
  Σ ( Σ ( map-hom-Premonoid M N f ~ map-hom-Premonoid M N g)
        ( λ H →
          ( x y : type-Premonoid M) →
          Id ( ( preserves-mul-map-hom-Premonoid M N f x y) ∙
               ( ap-mul-Premonoid N (H x) (H y)))
             ( ( H (mul-Premonoid M x y)) ∙
               ( preserves-mul-map-hom-Premonoid M N g x y))))
    ( λ Hμ →
      Id ( preserves-unit-map-hom-Premonoid M N f)
         ( pr1 Hμ (unit-Premonoid M) ∙ preserves-unit-map-hom-Premonoid M N g))

refl-htpy-hom-Premonoid :
  {l1 l2 : Level} (M : Premonoid l1) (N : Premonoid l2)
  (f : hom-Premonoid M N) → htpy-hom-Premonoid M N f f
refl-htpy-hom-Premonoid M N f =
  pair (pair refl-htpy (λ x y → right-unit)) refl

{-
is-contr-total-htpy-hom-Premonoid :
  {l1 l2 : Level} (M : Premonoid l1) (N : Premonoid l2)
  (f : hom-Premonoid M N) →
  is-contr (Σ (hom-Premonoid M N) (htpy-hom-Premonoid M N f))
is-contr-total-htpy-hom-Premonoid M N f =
  is-contr-total-Eq-structure
    {! λ fμ p!}
    {!!}
    {!!}
    {!!}
-}

list-Premonoid : {l : Level} → UU l → Premonoid l
list-Premonoid X =
  pair
    ( pair (list X) (pair concat-list assoc-concat-list))
    ( pair nil (pair left-unit-law-concat-list right-unit-law-concat-list))
