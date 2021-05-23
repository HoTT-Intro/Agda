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

--------------------------------------------------------------------------------

{- We define the underlying type of the final coalgebra of a polynomial 
   endofunctor -}

type-coseq-final-coalgebra-polynomial-endofunctor :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) → ℕ → UU (l1 ⊔ l2)
type-coseq-final-coalgebra-polynomial-endofunctor A B zero-ℕ =
  raise _ unit
type-coseq-final-coalgebra-polynomial-endofunctor A B (succ-ℕ n) =
  type-polynomial-endofunctor A B
    ( type-coseq-final-coalgebra-polynomial-endofunctor A B n)

map-coseq-final-coalgebra-polynomial-endofunctor :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) (n : ℕ) →
  type-coseq-final-coalgebra-polynomial-endofunctor A B (succ-ℕ n) →
  type-coseq-final-coalgebra-polynomial-endofunctor A B n
map-coseq-final-coalgebra-polynomial-endofunctor A B zero-ℕ x =
  raise-star
map-coseq-final-coalgebra-polynomial-endofunctor A B (succ-ℕ n) =
  map-polynomial-endofunctor A B
    ( map-coseq-final-coalgebra-polynomial-endofunctor A B n)

coseq-final-coalgebra-polynomial-endofunctor :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) → Coseq-UU (l1 ⊔ l2)
coseq-final-coalgebra-polynomial-endofunctor A B =
  pair ( type-coseq-final-coalgebra-polynomial-endofunctor A B)
       ( map-coseq-final-coalgebra-polynomial-endofunctor A B)

type-final-coalgebra-polynomial-endofunctor :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) → UU (l1 ⊔ l2)
type-final-coalgebra-polynomial-endofunctor A B =
  limit-Coseq
    ( coseq-final-coalgebra-polynomial-endofunctor A B)

{-
point-type-final-coalgebra-polynomial-endofunctor :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (x : type-final-coalgebra-polynomial-endofunctor A B) (n : ℕ) →
  type-coseq-final-coalgebra-polynomial-endofunctor A B n
point-type-final-coalgebra-polynomial-endofunctor {A = A} {B} =
  limit-Coseq
    ( coseq-final-coalgebra-polynomial-endofunctor A B)

path-type-final-coalgebra-polynomial-endofunctor :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (x : type-final-coalgebra-polynomial-endofunctor A B) (n : ℕ) →
  Id ( map-coseq-final-coalgebra-polynomial-endofunctor A B n
       ( point-type-final-coalgebra-polynomial-endofunctor x (succ-ℕ n)))
     ( point-type-final-coalgebra-polynomial-endofunctor x n)
path-type-final-coalgebra-polynomial-endofunctor {A = A} {B} =
  path-limit-Coseq
    ( coseq-final-coalgebra-polynomial-endofunctor A B)

cone-final-coalgebra-polynomial-endofunctor :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  cone-Coseq (coseq-final-coalgebra-polynomial-endofunctor A B)
             (type-final-coalgebra-polynomial-endofunctor A B)
cone-final-coalgebra-polynomial-endofunctor A B =
  cone-limit-Coseq
    ( coseq-final-coalgebra-polynomial-endofunctor A B)

universal-property-cone-final-coalgebra-polynomial-endofunctor :
  ( l : Level) {l1 l2 : Level} (A : UU l1) (B : A → UU l2) → 
  universal-property-limit-Coseq l
    ( coseq-final-coalgebra-polynomial-endofunctor A B)
    ( cone-final-coalgebra-polynomial-endofunctor A B)
universal-property-cone-final-coalgebra-polynomial-endofunctor l A B =
  universal-property-limit-limit-Coseq l
    ( coseq-final-coalgebra-polynomial-endofunctor A B)

--------------------------------------------------------------------------------

{- We define the costructure on the final coalgebra -}

costructure-final-coalgebra-polynomial-endofunctor :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  type-final-coalgebra-polynomial-endofunctor A B →
  type-polynomial-endofunctor A B
    ( type-final-coalgebra-polynomial-endofunctor A B)
costructure-final-coalgebra-polynomial-endofunctor A B =
  map-inv-equiv
    ( ( equiv-limit-shift-Coseq
        ( coseq-final-coalgebra-polynomial-endofunctor A B)) ∘e
      {!!})  

head-type-final-coalgebra-polynomial-endofunctor :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  type-final-coalgebra-polynomial-endofunctor A B → A
head-type-final-coalgebra-polynomial-endofunctor x = pr1 (pr1 x one-ℕ)

eq-head-type-final-coalgebra-polynomial-endofunctor :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (x : type-final-coalgebra-polynomial-endofunctor A B) (n : ℕ) →
  Id ( pr1 (point-type-final-coalgebra-polynomial-endofunctor x (succ-ℕ n)))
     ( head-type-final-coalgebra-polynomial-endofunctor x)
eq-head-type-final-coalgebra-polynomial-endofunctor x zero-ℕ = refl
eq-head-type-final-coalgebra-polynomial-endofunctor x (succ-ℕ n) =
  ( ap pr1 (path-type-final-coalgebra-polynomial-endofunctor x (succ-ℕ n))) ∙
  ( eq-head-type-final-coalgebra-polynomial-endofunctor x n)

points-tail-type-final-coalgebra-polynomial-endofunctor :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (x : type-final-coalgebra-polynomial-endofunctor A B) →
  B (head-type-final-coalgebra-polynomial-endofunctor x) →
  (n : ℕ) → type-coseq-final-coalgebra-polynomial-endofunctor A B n
points-tail-type-final-coalgebra-polynomial-endofunctor {A = A} {B} x y n =
  pr2 ( point-type-final-coalgebra-polynomial-endofunctor x (succ-ℕ n))
      ( inv-tr B (eq-head-type-final-coalgebra-polynomial-endofunctor x n) y)

tail-type-final-coalgebra-polynomial-endofunctor :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (x : type-final-coalgebra-polynomial-endofunctor A B) →
  B (head-type-final-coalgebra-polynomial-endofunctor x) →
  type-final-coalgebra-polynomial-endofunctor A B
tail-type-final-coalgebra-polynomial-endofunctor x y =
  pair
    ( points-tail-type-final-coalgebra-polynomial-endofunctor x y)
    {!!}
-}
