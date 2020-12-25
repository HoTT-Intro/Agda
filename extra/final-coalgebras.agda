{-# OPTIONS --without-K --exact-split #-}

module extra.final-coalgebras where

open import extra.sequential-limits public
open import extra.W-types public

-- Coalgebras for polynomial endofunctors

coalgebra-polynomial-endofunctor-UU :
  (l : Level) {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  UU (lsuc l ⊔ l1 ⊔ l2)
coalgebra-polynomial-endofunctor-UU l A B =
  Σ (UU l) (λ X → X → type-polynomial-endofunctor A B X)

type-coalgebra-polynomial-endofunctor :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} →
  coalgebra-polynomial-endofunctor-UU l3 A B → UU l3
type-coalgebra-polynomial-endofunctor = pr1

costructure-coalgebra-polynomial-endofunctor :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} →
  (X : coalgebra-polynomial-endofunctor-UU l3 A B) →
  type-coalgebra-polynomial-endofunctor X →
  type-polynomial-endofunctor A B (type-coalgebra-polynomial-endofunctor X)
costructure-coalgebra-polynomial-endofunctor = pr2

-- Morphisms of coalgebras for polynomial endofunctors

hom-coalgebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} →
  (X : coalgebra-polynomial-endofunctor-UU l3 A B) →
  (Y : coalgebra-polynomial-endofunctor-UU l4 A B) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
hom-coalgebra-polynomial-endofunctor {A = A} {B} X Y =
  Σ ( type-coalgebra-polynomial-endofunctor X →
      type-coalgebra-polynomial-endofunctor Y)
    ( λ h →
      ( ( map-polynomial-endofunctor A B h) ∘
        ( costructure-coalgebra-polynomial-endofunctor X)) ~
      ( costructure-coalgebra-polynomial-endofunctor Y ∘ h))

map-hom-coalgebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} →
  (X : coalgebra-polynomial-endofunctor-UU l3 A B) →
  (Y : coalgebra-polynomial-endofunctor-UU l4 A B) →
  (h : hom-coalgebra-polynomial-endofunctor X Y) →
  type-coalgebra-polynomial-endofunctor X →
  type-coalgebra-polynomial-endofunctor Y
map-hom-coalgebra-polynomial-endofunctor X Y = pr1

square-hom-coalgebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} →
  (X : coalgebra-polynomial-endofunctor-UU l3 A B) →
  (Y : coalgebra-polynomial-endofunctor-UU l4 A B) →
  (h : hom-coalgebra-polynomial-endofunctor X Y) →
  ( ( map-polynomial-endofunctor A B
      ( map-hom-coalgebra-polynomial-endofunctor X Y h)) ∘
    ( costructure-coalgebra-polynomial-endofunctor X)) ~
  ( ( costructure-coalgebra-polynomial-endofunctor Y) ∘
    ( map-hom-coalgebra-polynomial-endofunctor X Y h))
square-hom-coalgebra-polynomial-endofunctor X Y = pr2

-- We characterize the identity type of hom-coalgebra-polynomial-endofunctor

naturality-htpy-hom-coalgebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} →
  (X : coalgebra-polynomial-endofunctor-UU l3 A B) →
  (Y : coalgebra-polynomial-endofunctor-UU l4 A B) →
  (f g : hom-coalgebra-polynomial-endofunctor X Y) →
  (H : map-hom-coalgebra-polynomial-endofunctor X Y f ~
       map-hom-coalgebra-polynomial-endofunctor X Y g) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
naturality-htpy-hom-coalgebra-polynomial-endofunctor {A = A} {B} X Y f g H =
  ( ( ( htpy-polynomial-endofunctor A B H) ·r
      ( costructure-coalgebra-polynomial-endofunctor X)) ∙h
    ( square-hom-coalgebra-polynomial-endofunctor X Y g)) ~
  ( ( square-hom-coalgebra-polynomial-endofunctor X Y f) ∙h
    ( ( costructure-coalgebra-polynomial-endofunctor Y) ·l H))

htpy-hom-coalgebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} →
  (X : coalgebra-polynomial-endofunctor-UU l3 A B) →
  (Y : coalgebra-polynomial-endofunctor-UU l4 A B) →
  (f g : hom-coalgebra-polynomial-endofunctor X Y) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
htpy-hom-coalgebra-polynomial-endofunctor X Y f g =
  Σ ( map-hom-coalgebra-polynomial-endofunctor X Y f ~
      map-hom-coalgebra-polynomial-endofunctor X Y g)
    ( naturality-htpy-hom-coalgebra-polynomial-endofunctor X Y f g)

refl-htpy-hom-coalgebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} →
  (X : coalgebra-polynomial-endofunctor-UU l3 A B) →
  (Y : coalgebra-polynomial-endofunctor-UU l4 A B) →
  (f : hom-coalgebra-polynomial-endofunctor X Y) →
  htpy-hom-coalgebra-polynomial-endofunctor X Y f f
refl-htpy-hom-coalgebra-polynomial-endofunctor {A = A} {B} X Y f =
  pair ( refl-htpy)
       ( ( λ x →
           ap ( concat'
                ( map-polynomial-endofunctor A B (pr1 f) (pr2 X x))
                ( pr2 f x))
              ( coh-refl-htpy-polynomial-endofunctor A B
                ( pr1 f)
                ( costructure-coalgebra-polynomial-endofunctor X x))) ∙h
         ( inv-htpy right-unit-htpy))

htpy-hom-coalgebra-polynomial-endofunctor-eq :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} →
  (X : coalgebra-polynomial-endofunctor-UU l3 A B) →
  (Y : coalgebra-polynomial-endofunctor-UU l4 A B) →
  (f g : hom-coalgebra-polynomial-endofunctor X Y) →
  Id f g → htpy-hom-coalgebra-polynomial-endofunctor X Y f g
htpy-hom-coalgebra-polynomial-endofunctor-eq X Y f .f refl =
  refl-htpy-hom-coalgebra-polynomial-endofunctor X Y f

is-contr-total-htpy-hom-coalgebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} →
  (X : coalgebra-polynomial-endofunctor-UU l3 A B) →
  (Y : coalgebra-polynomial-endofunctor-UU l4 A B) →
  (f : hom-coalgebra-polynomial-endofunctor X Y) →
  is-contr
    ( Σ ( hom-coalgebra-polynomial-endofunctor X Y)
        ( htpy-hom-coalgebra-polynomial-endofunctor X Y f))
is-contr-total-htpy-hom-coalgebra-polynomial-endofunctor {A = A} {B} X Y f =
  is-contr-total-Eq-structure
    ( λ g G →
      naturality-htpy-hom-coalgebra-polynomial-endofunctor X Y f (pair g G))
    ( is-contr-total-htpy (map-hom-coalgebra-polynomial-endofunctor X Y f))
    ( pair (map-hom-coalgebra-polynomial-endofunctor X Y f) refl-htpy)
    ( is-contr-equiv
      ( Σ ( ( ( map-polynomial-endofunctor A B
                ( map-hom-coalgebra-polynomial-endofunctor X Y f)) ∘
              ( costructure-coalgebra-polynomial-endofunctor X)) ~
            ( ( costructure-coalgebra-polynomial-endofunctor Y) ∘
              ( map-hom-coalgebra-polynomial-endofunctor X Y f)))
          ( λ H → H ~ (square-hom-coalgebra-polynomial-endofunctor X Y f)))
      ( equiv-tot
        ( λ H →
          ( equiv-concat-htpy
            ( inv-htpy
              ( λ x →
                ap ( concat'
                     ( map-polynomial-endofunctor A B (pr1 f) (pr2 X x))
                     ( H x))
                   ( coh-refl-htpy-polynomial-endofunctor A B
                     ( pr1 f)
                     ( costructure-coalgebra-polynomial-endofunctor X x))))
            ( square-hom-coalgebra-polynomial-endofunctor X Y f)) ∘e
          ( equiv-concat-htpy'
            ( ( ( htpy-polynomial-endofunctor A B refl-htpy) ·r
                ( costructure-coalgebra-polynomial-endofunctor X)) ∙h
              ( H))
            ( right-unit-htpy))))
      ( is-contr-total-htpy'
        ( square-hom-coalgebra-polynomial-endofunctor X Y f)))

is-equiv-htpy-hom-coalgebra-polynomial-endofunctor-eq :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} →
  (X : coalgebra-polynomial-endofunctor-UU l3 A B) →
  (Y : coalgebra-polynomial-endofunctor-UU l4 A B) →
  (f g : hom-coalgebra-polynomial-endofunctor X Y) →
  is-equiv (htpy-hom-coalgebra-polynomial-endofunctor-eq X Y f g)
is-equiv-htpy-hom-coalgebra-polynomial-endofunctor-eq X Y f =
  fundamental-theorem-id f
    ( refl-htpy-hom-coalgebra-polynomial-endofunctor X Y f)
    ( is-contr-total-htpy-hom-coalgebra-polynomial-endofunctor X Y f)
    ( htpy-hom-coalgebra-polynomial-endofunctor-eq X Y f)
