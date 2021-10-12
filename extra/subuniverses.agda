{-# OPTIONS --without-K --allow-unsolved-metas #-}

module extra.subuniverses where

open import book public

{-
is-local :
  {l1 l2 l3 l4 : Level}
  {I : UU l1} {A : I → UU l2} {B : I → UU l3} (f : (i : I) → A i → B i)
  (X : UU l4) → UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l4)))
is-local {I = I} {B = B} f X =
  (i : I) → is-equiv (λ (h : B i → X) → h ∘ (f i))

is-subuniverse-is-local :
  {l1 l2 l3 l4 : Level}
  {I : UU l1} {A : I → UU l2} {B : I → UU l3} (f : (i : I) → A i → B i) →
  is-subuniverse (is-local {l4 = l4} f)
is-subuniverse-is-local f X = is-prop-Π (λ i → is-subtype-is-equiv _)
-}

universal-property-localization :
  {l1 l2 : Level} (P : subuniverse l1 l2)
  (X : UU l1) (Y : total-subuniverse P) (l : X → pr1 Y) →
  UU ((lsuc l1) ⊔ l2)
universal-property-localization {l1} P X (pair Y p) l =
  (Z : UU l1) (q : type-Prop (P Z)) → is-equiv (λ (h : Y → Z) → h ∘ l)

universal-property-localization' :
  (l : Level) (α : Level → Level) (P : (l : Level) → subuniverse l (α l))
  (g : (l1 l2 : Level) → is-global-subuniverse α P l1 l2)
  {l1 l2 : Level} (X : UU l1) (Y : total-subuniverse (P l2)) (f : X → pr1 Y) →
  UU ((lsuc l) ⊔ ((α l) ⊔ (l1 ⊔ l2)))
universal-property-localization' l α P g X Y f =
  (Z : total-subuniverse (P l)) → is-equiv (λ (h : (pr1 Y) → (pr1 Z)) → h ∘ f)

is-prop-universal-property-localization :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1)
  (Y : total-subuniverse P) (l : X → pr1 Y) →
  is-prop (universal-property-localization P X Y l)
is-prop-universal-property-localization P X (pair Y p) l =
  is-prop-Π (λ Z → is-prop-Π (λ q → is-subtype-is-equiv _))

has-localization :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  UU ((lsuc l1) ⊔ l2)
has-localization {l1} P X =
  Σ ( total-subuniverse P)
    ( λ Y → Σ (X → pr1 Y) (universal-property-localization P X Y))

Eq-localizations :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  ( s t : has-localization P X) → UU l1
Eq-localizations P X
  (pair (pair Y p) (pair l up)) t =
  let Y' = pr1 (pr1 t)
      p' = pr1 (pr1 t)
      l' = pr1 (pr2 t)
      up' = pr2 (pr2 t)
  in
  Σ ( Y ≃ Y')
    ( λ e → ((map-equiv e) ∘ l) ~ l' )

reflexive-Eq-localizations :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  (s : has-localization P X) → Eq-localizations P X s s
reflexive-Eq-localizations P X (pair (pair Y p) (pair l up)) =
  pair equiv-id refl-htpy

Eq-localizations-eq :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  ( s t : has-localization P X) → Id s t → Eq-localizations P X s t
Eq-localizations-eq P X s s refl = reflexive-Eq-localizations P X s

is-contr-total-Eq-localizations :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1)
  (s : has-localization P X) →
  is-contr (Σ (has-localization P X) (Eq-localizations P X s))
is-contr-total-Eq-localizations P X (pair (pair Y p) (pair l up)) =
  is-contr-total-Eq-structure
    ( λ Y' l' e → ((map-equiv e) ∘ l) ~ (pr1 l'))
    ( is-contr-total-equiv-subuniverse P (pair Y p))
    ( pair (pair Y p) equiv-id)
    ( is-contr-total-Eq-substructure
      ( is-contr-total-htpy l)
      ( is-prop-universal-property-localization P X (pair Y p))
      ( l)
      ( refl-htpy)
      ( up))

is-equiv-Eq-localizations-eq :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  ( s t : has-localization P X) → is-equiv (Eq-localizations-eq P X s t)
is-equiv-Eq-localizations-eq P X s =
  fundamental-theorem-id s
  ( reflexive-Eq-localizations P X s)
  ( is-contr-total-Eq-localizations P X s)
  ( Eq-localizations-eq P X s)

eq-Eq-localizations :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1)
  ( s t : has-localization P X) → (Eq-localizations P X s t) → Id s t
eq-Eq-localizations P X s t =
  map-inv-is-equiv (is-equiv-Eq-localizations-eq P X s t)

uniqueness-localizations :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  ( s t : has-localization P X) → Eq-localizations P X s t
uniqueness-localizations P X
  (pair (pair Y p) (pair l up)) (pair (pair Y' p') (pair l' up')) =
  pair
    ( pair
      ( map-inv-is-equiv (up Y' p') l')
      ( is-equiv-has-inverse
        ( map-inv-is-equiv (up' Y p) l)
        ( htpy-eq
          ( ap
            ( pr1 {B = λ h → Id (h ∘ l') l'})
            ( center
              ( is-prop-is-contr
                ( is-contr-map-is-equiv (up' Y' p') l')
                ( pair
                  ( ( map-inv-is-equiv (up Y' p') l') ∘
                    ( map-inv-is-equiv (up' Y p) l))
                  ( ( ap
                      ( λ t → (map-inv-is-equiv (up Y' p') l') ∘ t)
                      ( issec-map-inv-is-equiv (up' Y p) l)) ∙
                    ( issec-map-inv-is-equiv (up Y' p') l')))
                ( pair id refl)))))
        ( htpy-eq
              ( ap
                ( pr1 {B = λ h → Id (h ∘ l) l})
                ( center
                  ( is-prop-is-contr
                    ( is-contr-map-is-equiv (up Y p) l)
                    ( pair
                      ( ( map-inv-is-equiv (up' Y p) l) ∘
                        ( map-inv-is-equiv (up Y' p') l'))
                      ( ( ap
                          ( λ t → (map-inv-is-equiv (up' Y p) l) ∘ t)
                          ( issec-map-inv-is-equiv (up Y' p') l')) ∙
                         issec-map-inv-is-equiv (up' Y p) l))
                    ( pair id refl)))))))
    ( htpy-eq (issec-map-inv-is-equiv (up Y' p') l'))

is-prop-localizations :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  is-prop (has-localization P X)
is-prop-localizations P X =
  is-prop-all-elements-equal
    ( λ Y Y' → eq-Eq-localizations P X Y Y'
      ( uniqueness-localizations P X Y Y'))

universal-property-localization-equiv-is-local :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  (Y : UU l1) (p : type-Prop (P Y)) (l : X → Y) →
  is-equiv l → universal-property-localization P X (pair Y p) l
universal-property-localization-equiv-is-local P X Y p l is-equiv-l Z q =
  is-equiv-precomp-is-equiv l is-equiv-l Z

universal-property-localization-id-is-local :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) (q : type-Prop (P X)) →
  universal-property-localization P X (pair X q) id
universal-property-localization-id-is-local P X q =
  universal-property-localization-equiv-is-local P X X q id is-equiv-id

is-equiv-localization-is-local :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  ( Y : has-localization P X) → type-Prop (P X) → is-equiv (pr1 (pr2 Y))
is-equiv-localization-is-local P X (pair (pair Y p) (pair l up)) q =
  is-equiv-right-factor
    ( id)
    ( map-inv-is-equiv (up X q) id)
    ( l)
    ( htpy-eq (inv (issec-map-inv-is-equiv (up X q) id)))
    ( pr2
      ( pr1
        ( uniqueness-localizations P X
          ( pair (pair Y p) (pair l up))
          ( pair
            ( pair X q)
            ( pair id
              ( universal-property-localization-id-is-local P X q))))))
    ( is-equiv-id)

is-local-is-equiv-localization :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  ( Y : has-localization P X) → is-equiv (pr1 (pr2 Y)) → type-Prop (P X)
is-local-is-equiv-localization P X (pair (pair Y p) (pair l up)) is-equiv-l =
  in-subuniverse-equiv' (λ X → type-Prop (P X)) (pair l is-equiv-l) p

strong-retraction-property-localization :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  (Y : total-subuniverse P) (l : X → pr1 Y) → UU l1
strong-retraction-property-localization P X (pair Y p) l =
  is-equiv (λ (h : Y → X) → h ∘ l)

retraction-property-localization :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  (Y : total-subuniverse P) (l : X → pr1 Y) → UU l1
retraction-property-localization P X (pair Y p) l =
  retr l

strong-retraction-property-localization-is-equiv-localization :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  (Y : total-subuniverse P) (l : X → pr1 Y) →
  is-equiv l → strong-retraction-property-localization P X Y l
strong-retraction-property-localization-is-equiv-localization
  P X (pair Y p) l is-equiv-l =
  is-equiv-precomp-is-equiv l is-equiv-l X

retraction-property-localization-strong-retraction-property-localization :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  (Y : total-subuniverse P) (l : X → pr1 Y) →
  strong-retraction-property-localization P X Y l →
  retraction-property-localization P X Y l
retraction-property-localization-strong-retraction-property-localization
  P X (pair Y p) l s =
  tot (λ h → htpy-eq) (center (is-contr-map-is-equiv s id))

is-equiv-localization-retraction-property-localization :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  (Y : has-localization P X) →
  retraction-property-localization P X (pr1 Y) (pr1 (pr2 Y)) →
  is-equiv (pr1 (pr2 Y))
is-equiv-localization-retraction-property-localization
  P X (pair (pair Y p) (pair l up)) (pair g isretr-g) =
  is-equiv-has-inverse g
    ( htpy-eq
      ( ap
        ( pr1 {B = λ (h : Y → Y) → Id (h ∘ l) l})
        ( center
          ( is-prop-is-contr
            ( is-contr-map-is-equiv (up Y p) l)
            ( pair (l ∘ g) (ap (λ t → l ∘ t) (eq-htpy isretr-g)))
            ( pair id refl)))))
    ( isretr-g)

is-local-retraction-property-localization :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  (Y : has-localization P X) →
  retraction-property-localization P X (pr1 Y) (pr1 (pr2 Y)) →
  type-Prop (P X)
is-local-retraction-property-localization P X Y r =
  is-local-is-equiv-localization P X Y
    ( is-equiv-localization-retraction-property-localization P X Y r)

is-local-has-localization-is-contr :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  is-contr X → has-localization P X → type-Prop (P X)
is-local-has-localization-is-contr
  P X is-contr-X (pair (pair Y p) (pair l up)) =
  is-local-retraction-property-localization P X
    ( pair (pair Y p) (pair l up))
    ( pair
      ( λ _ → center is-contr-X)
      ( contraction is-contr-X))

has-localization-is-local-is-contr :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  is-contr X → type-Prop (P X) → has-localization P X
has-localization-is-local-is-contr P X is-contr-X p =
  pair
    ( pair X p)
    ( pair id (universal-property-localization-id-is-local P X p))

is-local-unit-localization-unit :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  (Y : has-localization P (raise l1 unit)) →
  type-Prop (P (raise l1 unit))
is-local-unit-localization-unit P Y =
  is-local-has-localization-is-contr P (raise _ unit) (is-contr-raise-unit) Y

map-Σ-dependent-elimination-localization :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  (has-loc-X : has-localization P X) →
  let Y = pr1 (pr1 has-loc-X)
      l = pr1 (pr2 has-loc-X)
  in
  (Z : Y → UU l1) →
  Σ (Y → Y) (λ h → (y : Y) → Z (h y)) →
  Σ (X → Y) (λ h → (x : X) → Z (h x))
map-Σ-dependent-elimination-localization P X
  (pair (pair Y p) (pair l up)) Z =
  map-Σ
    ( λ (h : X → Y) → (x : X) → Z (h x))
    ( λ h → h ∘ l)
    ( λ h h' x → h' (l x))

square-dependent-elimination-localization :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  (has-loc-X : has-localization P X) →
  let Y = pr1 (pr1 has-loc-X)
      l = pr1 (pr2 has-loc-X)
  in
  (Z : Y → UU l1) (q : type-Prop (P (Σ _ Z))) →
  ( ( λ (h : Y → Σ Y Z) → h ∘ l) ∘
    ( inv-choice-∞)) ~
  ( ( inv-choice-∞) ∘
    ( map-Σ-dependent-elimination-localization P X has-loc-X Z))
square-dependent-elimination-localization
  P X (pair (pair Y p) (pair l up)) Z q =
  refl-htpy

is-equiv-map-Σ-dependent-elimination-localization :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  (has-loc-X : has-localization P X)
  (Z : pr1 (pr1 has-loc-X) → UU l1) (q : type-Prop (P (Σ _ Z))) →
  is-equiv (map-Σ-dependent-elimination-localization P X has-loc-X Z)
is-equiv-map-Σ-dependent-elimination-localization
  P X (pair (pair Y p) (pair l up)) Z q =
  is-equiv-top-is-equiv-bottom-square
    ( inv-choice-∞)
    ( inv-choice-∞)
    ( map-Σ-dependent-elimination-localization
      P X (pair (pair Y p) (pair l up)) Z)
    ( λ h → h ∘ l)
    ( square-dependent-elimination-localization
      P X (pair (pair Y p) (pair l up)) Z q)
    ( is-equiv-inv-choice-∞)
    ( is-equiv-inv-choice-∞)
    ( up (Σ Y Z) q)

dependent-elimination-localization :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  (X : UU l1) (Y : has-localization P X) →
  (Z : (pr1 (pr1 Y)) → UU l1) (q : type-Prop (P (Σ _ Z))) →
  is-equiv (λ (h : (y : (pr1 (pr1 Y))) → (Z y)) → λ x → h (pr1 (pr2 Y) x))
dependent-elimination-localization P X (pair (pair Y p) (pair l up)) Z q =
  is-fiberwise-equiv-is-equiv-map-Σ
    ( λ (h : X → Y) → (x : X) → Z (h x))
    ( λ (h : Y → Y) → h ∘ l)
    ( λ (h : Y → Y) (h' : (y : Y) → Z (h y)) (x : X) → h' (l x))
    ( up Y p)
    ( is-equiv-map-Σ-dependent-elimination-localization
      P X (pair (pair Y p) (pair l up)) Z q)
    ( id)

is-reflective-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) → UU ((lsuc l1) ⊔ l2)
is-reflective-subuniverse {l1} P = (X : UU l1) → has-localization P X

reflective-subuniverse :
  (l1 l2 : Level) → UU ((lsuc l1) ⊔ (lsuc l2))
reflective-subuniverse l1 l2 = Σ (subuniverse l1 l2) is-reflective-subuniverse

is-local :
  {l1 l2 : Level} (L : reflective-subuniverse l1 l2) →
  UU l1 → UU l2
is-local L X = type-Prop (pr1 L X)

is-prop-is-local :
  {l1 l2 : Level} (L : reflective-subuniverse l1 l2) →
  (X : UU l1) → is-prop (is-local L X)
is-prop-is-local L X = is-prop-type-Prop (pr1 L X)

total-reflective-subuniverse :
  {l1 l2 : Level} (L : reflective-subuniverse l1 l2) → UU ((lsuc l1) ⊔ l2)
total-reflective-subuniverse L = total-subuniverse (pr1 L)

local-type-localization :
  {l1 l2 : Level} (L : reflective-subuniverse l1 l2)
  (X : UU l1) → total-reflective-subuniverse L
local-type-localization L X = pr1 ((pr2 L) X)

type-localization :
  {l1 l2 : Level} (L : reflective-subuniverse l1 l2) →
  UU l1 → UU l1
type-localization L X = pr1 (local-type-localization L X)

is-local-type-localization :
  {l1 l2 : Level} (L : reflective-subuniverse l1 l2)
  (X : UU l1) → is-local L (type-localization L X)
is-local-type-localization L X = pr2 (local-type-localization L X)

universal-map-localization :
  {l1 l2 : Level} (L : reflective-subuniverse l1 l2) (X : UU l1) →
  Σ ( X → type-localization L X)
    ( universal-property-localization (pr1 L) X (local-type-localization L X))
universal-map-localization L X = pr2 ((pr2 L) X)

unit-localization :
  {l1 l2 : Level} (L : reflective-subuniverse l1 l2)
  (X : UU l1) → X → type-localization L X
unit-localization L X = pr1 (universal-map-localization L X)

universal-property-map-localization :
  {l1 l2 : Level} (L : reflective-subuniverse l1 l2) (X : UU l1) → 
  universal-property-localization (pr1 L) X
    ( local-type-localization L X)
    ( unit-localization L X)
universal-property-map-localization L X = pr2 (universal-map-localization L X)

dependent-elimination-reflective-subuniverse :
  {l1 l2 : Level} (L : reflective-subuniverse l1 l2) (X : UU l1) →
  (Y : type-localization L X → UU l1)
  (is-loc-total-Y : is-local L (Σ _ Y)) →
  is-equiv
    ( λ (h : (x' : type-localization L X) → Y x') x → h (unit-localization L X x))
dependent-elimination-reflective-subuniverse L X =
  dependent-elimination-localization (pr1 L) X ((pr2 L) X)

is-contr-square-localization :
  {l1 l2 : Level} (L : reflective-subuniverse l1 l2) {X Y : UU l1} (f : X → Y) →
  is-contr
    ( Σ (type-localization L X → type-localization L Y)
      ( λ Lf → coherence-square (unit-localization L X) f Lf (unit-localization L Y)))
is-contr-square-localization L f = {!!}
