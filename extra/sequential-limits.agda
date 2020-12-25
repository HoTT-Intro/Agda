{-# OPTIONS --without-K --exact-split #-}

module extra.sequential-limits where

open import book public

--------------------------------------------------------------------------------

{- We introduce cosequences (i.e. sequences going in the other way) -}

Coseq-UU : (l : Level) → UU (lsuc l)
Coseq-UU l = Σ (ℕ → UU l) (λ A → (n : ℕ) → A (succ-ℕ n) → A n)

type-Coseq : {l : Level} (A : Coseq-UU l) → (n : ℕ) → UU l
type-Coseq A = pr1 A

map-Coseq :
  {l : Level} (A : Coseq-UU l) →
  (n : ℕ) → (type-Coseq A (succ-ℕ n)) → (type-Coseq A n)
map-Coseq A = pr2 A

{- We introduce morphisms of cosequences -}

naturality-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) →
  (h : (n : ℕ) → type-Coseq A n → type-Coseq B n) → UU (l1 ⊔ l2)
naturality-hom-Coseq A B h =
  (n : ℕ) → ((map-Coseq B n) ∘ (h (succ-ℕ n))) ~ ((h n) ∘ (map-Coseq A n))

hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) → UU (l1 ⊔ l2)
hom-Coseq A B =
  Σ ((n : ℕ) → type-Coseq A n → type-Coseq B n) (naturality-hom-Coseq A B)

map-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) →
  hom-Coseq A B → (n : ℕ) → type-Coseq A n → type-Coseq B n
map-hom-Coseq A B h = pr1 h

naturality-map-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (h : hom-Coseq A B) →
  naturality-hom-Coseq A B (map-hom-Coseq A B h)
naturality-map-hom-Coseq A B h = pr2 h

{- We introduce natural homotopies of morphism between cosequences -}

naturality-htpy-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f g : hom-Coseq A B)
  (H : (n : ℕ) → (map-hom-Coseq A B f n) ~ (map-hom-Coseq A B g n))
  → UU (l1 ⊔ l2)
naturality-htpy-hom-Coseq A B f g H =
  (n : ℕ) →
  ( ( (map-Coseq B n) ·l (H (succ-ℕ n))) ∙h
    ( naturality-map-hom-Coseq A B g n)) ~
  ( ( naturality-map-hom-Coseq A B f n) ∙h
    ( (H n) ·r (map-Coseq A n)))

htpy-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) →
  hom-Coseq A B → hom-Coseq A B → UU (l1 ⊔ l2)
htpy-hom-Coseq A B f g =
  Σ ( (n : ℕ) → (map-hom-Coseq A B f n) ~ (map-hom-Coseq A B g n))
    ( naturality-htpy-hom-Coseq A B f g)

htpy-map-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2)
  (f g : hom-Coseq A B) → htpy-hom-Coseq A B f g → (n : ℕ) →
  (map-hom-Coseq A B f n) ~ (map-hom-Coseq A B g n)
htpy-map-hom-Coseq A B f g H = pr1 H

naturality-htpy-map-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2)
  (f g : hom-Coseq A B) (H : htpy-hom-Coseq A B f g) →
  naturality-htpy-hom-Coseq A B f g (htpy-map-hom-Coseq A B f g H)
naturality-htpy-map-hom-Coseq A B f g H = pr2 H

--------------------------------------------------------------------------------

{- We characterize the identity type of Coseq-UU l. -}

equiv-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) → UU (l1 ⊔ l2)
equiv-Coseq A B =
  Σ ( (n : ℕ) → (type-Coseq A n) ≃ (type-Coseq B n)) (λ e →
    ( n : ℕ) →
      ( (map-Coseq B n) ∘ (map-equiv (e (succ-ℕ n)))) ~
      ( (map-equiv (e n)) ∘ (map-Coseq A n)))

reflexive-equiv-Coseq :
  { l1 : Level} (A : Coseq-UU l1) → equiv-Coseq A A
reflexive-equiv-Coseq A =
  pair
    ( λ n → equiv-id)
    ( λ n → refl-htpy)

equiv-eq-Coseq :
  { l1 : Level} (A B : Coseq-UU l1) → Id A B → equiv-Coseq A B
equiv-eq-Coseq A .A refl = reflexive-equiv-Coseq A

is-contr-total-equiv-Coseq :
  { l1 : Level} (A : Coseq-UU l1) →
  is-contr (Σ (Coseq-UU l1) (equiv-Coseq A))
is-contr-total-equiv-Coseq A =
  is-contr-total-Eq-structure
    ( λ B g (e : (n : ℕ) → (type-Coseq A n) ≃ (B n)) → (n : ℕ) →
      ( (g n) ∘ (map-equiv (e (succ-ℕ n)))) ~
      ( (map-equiv (e n)) ∘ (map-Coseq A n)))
    ( is-contr-total-Eq-Π
      ( λ n B → (type-Coseq A n) ≃ B)
      ( λ n → is-contr-total-equiv (type-Coseq A n))
      ( type-Coseq A))
    ( pair (type-Coseq A) (λ n → equiv-id))
    ( is-contr-total-Eq-Π
      ( λ n g → g ~ (map-Coseq A n))
      ( λ n → is-contr-total-htpy' (map-Coseq A n))
      ( map-Coseq A))

is-equiv-equiv-eq-Coseq :
  { l1 : Level} (A B : Coseq-UU l1) → is-equiv (equiv-eq-Coseq A B)
is-equiv-equiv-eq-Coseq A =
  fundamental-theorem-id A
    ( reflexive-equiv-Coseq A)
    ( is-contr-total-equiv-Coseq A)
    ( equiv-eq-Coseq A)

eq-equiv-Coseq :
  { l1 : Level} (A B : Coseq-UU l1) → equiv-Coseq A B → Id A B
eq-equiv-Coseq A B = map-inv-is-equiv (is-equiv-equiv-eq-Coseq A B)

--------------------------------------------------------------------------------

{- We characterize the identity type of hom-Coseq. -}

refl-htpy-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  htpy-hom-Coseq A B f f
refl-htpy-hom-Coseq A B f =
  pair ((λ n → refl-htpy)) (λ n → inv-htpy right-unit-htpy)

htpy-hom-Coseq-eq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2)
  (f g : hom-Coseq A B) → Id f g → htpy-hom-Coseq A B f g
htpy-hom-Coseq-eq A B f .f refl = refl-htpy-hom-Coseq A B f

is-contr-total-htpy-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  is-contr (Σ (hom-Coseq A B) (htpy-hom-Coseq A B f))
is-contr-total-htpy-hom-Coseq A B f =
  is-contr-total-Eq-structure
    ( λ g G → naturality-htpy-hom-Coseq A B f (pair g G))
    ( is-contr-total-Eq-Π
      ( λ n gn → map-hom-Coseq A B f n ~ gn)
      ( λ n → is-contr-total-htpy (map-hom-Coseq A B f n))
      ( λ n → map-hom-Coseq A B f n))
    ( pair (map-hom-Coseq A B f) (λ n → refl-htpy))
    ( is-contr-total-Eq-Π
      ( λ n Gn →
        ( ((map-Coseq B n) ·l refl-htpy) ∙h Gn) ~
        ( ((naturality-map-hom-Coseq A B f n) ∙h refl-htpy)))
      ( λ n →
        is-contr-equiv
          ( Σ ( ( (map-Coseq B n) ∘ (map-hom-Coseq A B f (succ-ℕ n))) ~
                ( (map-hom-Coseq A B f n) ∘ (map-Coseq A n)))
              ( (λ Gn → Gn ~ (naturality-map-hom-Coseq A B f n))))
          ( equiv-tot ((λ Gn → equiv-concat-htpy' Gn right-unit-htpy)))
          ( is-contr-total-htpy' (naturality-map-hom-Coseq A B f n)))
      ( naturality-map-hom-Coseq A B f))

is-equiv-htpy-hom-Coseq-eq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2)
  (f g : hom-Coseq A B) → is-equiv (htpy-hom-Coseq-eq A B f g)
is-equiv-htpy-hom-Coseq-eq A B f =
  fundamental-theorem-id f
    ( refl-htpy-hom-Coseq A B f)
    ( is-contr-total-htpy-hom-Coseq A B f)
    ( htpy-hom-Coseq-eq A B f)

equiv-htpy-hom-Coseq-eq :
  { l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f g : hom-Coseq A B) →
  Id f g ≃ (htpy-hom-Coseq A B f g)
equiv-htpy-hom-Coseq-eq A B f g =
  pair
    ( htpy-hom-Coseq-eq A B f g)
    ( is-equiv-htpy-hom-Coseq-eq A B f g)

eq-htpy-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2)
  (f g : hom-Coseq A B) → htpy-hom-Coseq A B f g → Id f g
eq-htpy-hom-Coseq A B f g =
  map-inv-is-equiv (is-equiv-htpy-hom-Coseq-eq A B f g)

--------------------------------------------------------------------------------

{- We introduce cones on a type sequence. -}

constant-Coseq : {l : Level} (X : UU l) → Coseq-UU l
constant-Coseq X = pair (λ n → X) (λ n → id)

cone-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) (X : UU l2) → UU (l1 ⊔ l2)
cone-Coseq A X = hom-Coseq (constant-Coseq X) A

map-cone-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( n : ℕ) → X → type-Coseq A n
map-cone-Coseq A c = pr1 c

triangle-cone-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( n : ℕ) →
  ( (map-Coseq A n) ∘ (map-cone-Coseq A c (succ-ℕ n))) ~
  ( map-cone-Coseq A c n)
triangle-cone-Coseq A c = pr2 c

--------------------------------------------------------------------------------

{- We characterize the identity type of cone-Coseq. -}

naturality-htpy-cone-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2} (c c' : cone-Coseq A X) →
  ( H : (n : ℕ) → (map-cone-Coseq A c n) ~ (map-cone-Coseq A c' n)) →
  UU (l1 ⊔ l2)
naturality-htpy-cone-Coseq A {X} =
  naturality-htpy-hom-Coseq (constant-Coseq X) A

htpy-cone-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2} →
  ( c c' : cone-Coseq A X) → UU (l1 ⊔ l2)
htpy-cone-Coseq A {X} = htpy-hom-Coseq (constant-Coseq X) A

refl-htpy-cone-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  htpy-cone-Coseq A c c
refl-htpy-cone-Coseq A {X} = refl-htpy-hom-Coseq (constant-Coseq X) A

htpy-cone-Coseq-eq :
  { l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2} (c c' : cone-Coseq A X) →
  Id c c' → htpy-cone-Coseq A c c'
htpy-cone-Coseq-eq A {X} = htpy-hom-Coseq-eq (constant-Coseq X) A

is-contr-total-htpy-cone-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  is-contr (Σ (cone-Coseq A X) (htpy-cone-Coseq A c))
is-contr-total-htpy-cone-Coseq A {X} =
  is-contr-total-htpy-hom-Coseq (constant-Coseq X) A

is-equiv-htpy-cone-Coseq-eq :
  { l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2} (c c' : cone-Coseq A X) →
  is-equiv (htpy-cone-Coseq-eq A c c')
is-equiv-htpy-cone-Coseq-eq A {X} =
  is-equiv-htpy-hom-Coseq-eq (constant-Coseq X) A

eq-htpy-cone-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2} (c c' : cone-Coseq A X) →
  htpy-cone-Coseq A c c' → Id c c'
eq-htpy-cone-Coseq A {X} = eq-htpy-hom-Coseq (constant-Coseq X) A

equiv-htpy-cone-Coseq-eq :
  { l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2} (c c' : cone-Coseq A X) →
  Id c c' ≃ (htpy-cone-Coseq A c c')
equiv-htpy-cone-Coseq-eq A {X} =
  equiv-htpy-hom-Coseq-eq (constant-Coseq X) A

--------------------------------------------------------------------------------

{- We introduce sequential limits. -}

cone-map-Coseq :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( Y : UU l3) → (Y → X) → cone-Coseq A Y
cone-map-Coseq A c Y h =
  pair
    ( λ n → (map-cone-Coseq A c n) ∘ h)
    ( λ n → (triangle-cone-Coseq A c n) ·r h)

universal-property-sequential-limit :
  ( l : Level) {l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2}
  ( c : cone-Coseq A X) → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-sequential-limit l A c =
  (Y : UU l) → is-equiv (cone-map-Coseq A c Y)

--------------------------------------------------------------------------------

{- We introduce the canonical sequential limit. -}

canonical-sequential-limit :
  {l : Level} (A : Coseq-UU l) → UU l
canonical-sequential-limit A =
  Σ ( (n : ℕ) → type-Coseq A n)
    ( λ a → (n : ℕ) → Id (map-Coseq A n (a (succ-ℕ n))) (a n))

point-canonical-sequential-limit :
  {l : Level} (A : Coseq-UU l) (x : canonical-sequential-limit A) (n : ℕ) →
  type-Coseq A n
point-canonical-sequential-limit A x = pr1 x

path-canonical-sequential-limit :
  {l : Level} (A : Coseq-UU l) (x : canonical-sequential-limit A) (n : ℕ) →
  Id ( map-Coseq A n (point-canonical-sequential-limit A x (succ-ℕ n)))
     ( point-canonical-sequential-limit A x n)
path-canonical-sequential-limit A x = pr2 x

{- We introduce a second canonical sequential limit. -}

canonical-sequential-limit' : {l : Level} (A : Coseq-UU l) → UU l
canonical-sequential-limit' A = cone-Coseq A unit

equiv-canonical-sequential-limit :
  {l : Level} (A : Coseq-UU l) →
  canonical-sequential-limit' A ≃ canonical-sequential-limit A
equiv-canonical-sequential-limit A =
  equiv-Σ
    ( λ a → (n : ℕ) → Id (map-Coseq A n (a (succ-ℕ n))) (a n))
    ( equiv-postcomp-Π (λ n → equiv-ev-star' (type-Coseq A n)))
    ( λ a →
      equiv-postcomp-Π
        ( λ n →
          equiv-ev-star (λ x → Id (map-Coseq A n (a (succ-ℕ n) x)) (a n x))))

--------------------------------------------------------------------------------

{- We characterize the identity type of the canonical sequential limit. -}

Eq-canonical-sequential-limit :
  { l1 : Level} (A : Coseq-UU l1) (x y : canonical-sequential-limit A) → UU l1
Eq-canonical-sequential-limit A x y =
  Σ ( ( point-canonical-sequential-limit A x) ~
      ( point-canonical-sequential-limit A y))
    ( λ H → (n : ℕ) →
      Id ( ( ap (map-Coseq A n) (H (succ-ℕ n))) ∙
           ( path-canonical-sequential-limit A y n))
         ( ( path-canonical-sequential-limit A x n) ∙
           ( H n)))

refl-Eq-canonical-sequential-limit :
  { l1 : Level} (A : Coseq-UU l1) (x : canonical-sequential-limit A) →
  Eq-canonical-sequential-limit A x x
refl-Eq-canonical-sequential-limit A x =
  pair refl-htpy (inv-htpy right-unit-htpy)

Eq-canonical-sequential-limit-eq :
  { l1 : Level} (A : Coseq-UU l1) (x y : canonical-sequential-limit A) →
  Id x y → Eq-canonical-sequential-limit A x y
Eq-canonical-sequential-limit-eq A x .x refl =
  refl-Eq-canonical-sequential-limit A x

is-contr-total-Eq-canonical-sequential-limit :
  { l1 : Level} (A : Coseq-UU l1) (x : canonical-sequential-limit A) →
  is-contr
    ( Σ (canonical-sequential-limit A) (Eq-canonical-sequential-limit A x))
is-contr-total-Eq-canonical-sequential-limit A x =
  is-contr-total-Eq-structure
    ( λ y q (H : (n : ℕ) → Id (pr1 x n) (y n)) →
      (n : ℕ) →
        Id ((ap (map-Coseq A n) (H (succ-ℕ n))) ∙ (q n)) ((pr2 x n) ∙ (H n)))
    ( is-contr-total-Eq-Π
      ( λ n yn → Id (pr1 x n) yn)
      ( λ n → is-contr-total-path (pr1 x n))
      ( pr1 x))
    ( pair (pr1 x) refl-htpy)
    ( is-contr-total-Eq-Π
      ( λ n q → Id q ((pr2 x n) ∙ refl))
      ( λ n → is-contr-total-path' ((pr2 x n) ∙ refl))
      ( pr2 x))

is-equiv-Eq-canonical-sequential-limit :
  { l1 : Level} (A : Coseq-UU l1) (x y : canonical-sequential-limit A) →
  is-equiv (Eq-canonical-sequential-limit-eq A x y)
is-equiv-Eq-canonical-sequential-limit A x =
  fundamental-theorem-id x
    ( refl-Eq-canonical-sequential-limit A x)
    ( is-contr-total-Eq-canonical-sequential-limit A x)
    ( Eq-canonical-sequential-limit-eq A x)

eq-Eq-canonical-sequential-limit :
  { l1 : Level} (A : Coseq-UU l1) {x y : canonical-sequential-limit A} →
  Eq-canonical-sequential-limit A x y → Id x y
eq-Eq-canonical-sequential-limit A {x} {y} =
  map-inv-is-equiv (is-equiv-Eq-canonical-sequential-limit A x y)

--------------------------------------------------------------------------------

{- We give a second characterization of the identity type of the canonical
   sequential colimit, expressed as a canonical sequential colimit. -}

type-coseq-Eq-canonical-sequential-limit' :
  {l : Level} (A : Coseq-UU l) (x y : canonical-sequential-limit A) →
  (n : ℕ) → UU l
type-coseq-Eq-canonical-sequential-limit' A x y n =
  Id ( point-canonical-sequential-limit A x n)
     ( point-canonical-sequential-limit A y n)

map-coseq-Eq-canonical-sequential-limit' :
  {l : Level} (A : Coseq-UU l) (x y : canonical-sequential-limit A) (n : ℕ) →
  type-coseq-Eq-canonical-sequential-limit' A x y (succ-ℕ n) →
  type-coseq-Eq-canonical-sequential-limit' A x y n
map-coseq-Eq-canonical-sequential-limit' A x y n p =
  ( inv (path-canonical-sequential-limit A x n)) ∙
  ( ( ap (map-Coseq A n) p) ∙
    ( path-canonical-sequential-limit A y n))

coseq-Eq-canonical-sequential-limit' :
  {l : Level} (A : Coseq-UU l) (x y : canonical-sequential-limit A) → Coseq-UU l
coseq-Eq-canonical-sequential-limit' A x y =
  pair ( type-coseq-Eq-canonical-sequential-limit' A x y)
       ( map-coseq-Eq-canonical-sequential-limit' A x y)

Eq-canonical-sequential-limit' :
  {l : Level} (A : Coseq-UU l) (x y : canonical-sequential-limit A) → UU l
Eq-canonical-sequential-limit' A x y =
  canonical-sequential-limit (coseq-Eq-canonical-sequential-limit' A x y)

refl-Eq-canonical-sequential-limit' :
  {l : Level} (A : Coseq-UU l) (x : canonical-sequential-limit A) →
  Eq-canonical-sequential-limit' A x x
refl-Eq-canonical-sequential-limit' A x =
  pair (λ n → refl) (λ n → left-inv (path-canonical-sequential-limit A x n))

Eq-canonical-sequential-limit-eq' :
  {l : Level} (A : Coseq-UU l) (x y : canonical-sequential-limit A) →
  Id x y → Eq-canonical-sequential-limit' A x y
Eq-canonical-sequential-limit-eq' A x .x refl =
  refl-Eq-canonical-sequential-limit' A x

is-contr-total-Eq-canonical-sequential-limit' :
  {l : Level} (A : Coseq-UU l) (x : canonical-sequential-limit A) →
  is-contr
    ( Σ (canonical-sequential-limit A) (Eq-canonical-sequential-limit' A x))
is-contr-total-Eq-canonical-sequential-limit' A x =
  is-contr-total-Eq-structure
    ( λ a H (p : (n : ℕ) → Id (point-canonical-sequential-limit A x n) (a n)) →
      (n : ℕ) →
      Id ( inv
           ( path-canonical-sequential-limit A x n) ∙
           ( ( ap (map-Coseq A n) (p (succ-ℕ n))) ∙ (H n)))
         ( p n))
    ( is-contr-total-htpy (point-canonical-sequential-limit A x))
    ( pair (point-canonical-sequential-limit A x) refl-htpy)
    ( is-contr-equiv'
      ( Σ ( (n : ℕ) →
            Id ( map-Coseq A n
                 ( point-canonical-sequential-limit A x (succ-ℕ n)))
               ( point-canonical-sequential-limit A x n))
          ( λ p →
            (n : ℕ) → Id (path-canonical-sequential-limit A x n) (p n)))
      ( equiv-tot
        ( λ p →
          equiv-postcomp-Π
            ( λ n →
              ( equiv-inv refl (inv (pr2 x n) ∙ p n)) ∘e
              ( ( equiv-inv-con (pr2 x n) refl (p n)) ∘e
                ( equiv-concat right-unit (p n))))))
      ( is-contr-total-htpy (path-canonical-sequential-limit A x)))

is-equiv-Eq-canonical-sequential-limit-eq' :
  {l : Level} (A : Coseq-UU l) (x y : canonical-sequential-limit A) →
  is-equiv (Eq-canonical-sequential-limit-eq' A x y)
is-equiv-Eq-canonical-sequential-limit-eq' A x =
  fundamental-theorem-id x
    ( refl-Eq-canonical-sequential-limit' A x)
    ( is-contr-total-Eq-canonical-sequential-limit' A x)
    ( Eq-canonical-sequential-limit-eq' A x)

--------------------------------------------------------------------------------

{- We equip the canonical sequential limit with the structure of a cone. -}

cone-canonical-sequential-limit :
  {l1 : Level} (A : Coseq-UU l1) → cone-Coseq A (canonical-sequential-limit A)
cone-canonical-sequential-limit A =
  pair ( λ n a → point-canonical-sequential-limit A a n)
       ( λ n a → path-canonical-sequential-limit A a n)

--------------------------------------------------------------------------------

{- We show that the canonical sequential limit satisfies the universal property
   of sequential limits. -}

inv-cone-map-cone-canonical-sequential-limit :
  { l1 l2 : Level} (A : Coseq-UU l1) (Y : UU l2) →
  cone-Coseq A Y → (Y → canonical-sequential-limit A)
inv-cone-map-cone-canonical-sequential-limit A Y c y =
  pair
    ( λ n → map-cone-Coseq A c n y)
    ( λ n → triangle-cone-Coseq A c n y)

issec-inv-cone-map-cone-canonical-sequential-limit :
  { l1 l2 : Level} (A : Coseq-UU l1) (Y : UU l2) →
  ( ( cone-map-Coseq A (cone-canonical-sequential-limit A) Y) ∘
    ( inv-cone-map-cone-canonical-sequential-limit A Y)) ~ id
issec-inv-cone-map-cone-canonical-sequential-limit A Y c =
  eq-htpy-cone-Coseq A
    ( cone-map-Coseq A
      ( cone-canonical-sequential-limit A)
      ( Y)
      ( inv-cone-map-cone-canonical-sequential-limit A Y c))
    ( c)
    ( refl-htpy-cone-Coseq A c)

isretr-inv-cone-map-cone-canonical-sequential-limit :
  { l1 l2 : Level} (A : Coseq-UU l1) (Y : UU l2) →
  ( ( inv-cone-map-cone-canonical-sequential-limit A Y) ∘
    ( cone-map-Coseq A (cone-canonical-sequential-limit A) Y)) ~ id
isretr-inv-cone-map-cone-canonical-sequential-limit A Y h =
  eq-htpy (λ y →
    eq-Eq-canonical-sequential-limit A
      ( refl-Eq-canonical-sequential-limit A (h y)))

is-equiv-cone-map-cone-canonical-sequential-limit :
  { l1 l2 : Level} (A : Coseq-UU l1) (Y : UU l2) →
  is-equiv (cone-map-Coseq A (cone-canonical-sequential-limit A) Y)
is-equiv-cone-map-cone-canonical-sequential-limit A Y =
  is-equiv-has-inverse
    ( inv-cone-map-cone-canonical-sequential-limit A Y)
    ( issec-inv-cone-map-cone-canonical-sequential-limit A Y)
    ( isretr-inv-cone-map-cone-canonical-sequential-limit A Y)

universal-property-canonical-sequential-limit :
  ( l : Level) {l1 : Level} (A : Coseq-UU l1) →
  universal-property-sequential-limit l A (cone-canonical-sequential-limit A)
universal-property-canonical-sequential-limit l A Y =
  is-equiv-cone-map-cone-canonical-sequential-limit A Y

--------------------------------------------------------------------------------

{- Unique mapping property for sequential limits. -}

unique-mapping-property-sequential-limit' :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( up-X : {l : Level} → universal-property-sequential-limit l A c)
  { Y : UU l3} (c' : cone-Coseq A Y) →
  is-contr (fib (cone-map-Coseq A c Y) c')
unique-mapping-property-sequential-limit' A c up-X {Y} =
  is-contr-map-is-equiv (up-X Y)

map-universal-property-sequential-limit :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( up-X : {l : Level} → universal-property-sequential-limit l A c) →
  { Y : UU l3} (c' : cone-Coseq A Y) → Y → X
map-universal-property-sequential-limit A c up-X c' =
  pr1 (center (unique-mapping-property-sequential-limit' A c up-X c'))

path-universal-property-sequential-limit :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( up-X : {l : Level} → universal-property-sequential-limit l A c) →
  { Y : UU l3} (c' : cone-Coseq A Y) →
  Id ( cone-map-Coseq A c Y
       ( map-universal-property-sequential-limit A c up-X c'))
     ( c')
path-universal-property-sequential-limit A c up-X c' =
  pr2 (center (unique-mapping-property-sequential-limit' A c up-X c'))

unique-mapping-property-sequential-limit :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( up-X : {l : Level} → universal-property-sequential-limit l A c) →
  { Y : UU l3} (c' : cone-Coseq A Y) →
  is-contr
    ( Σ ( Y → X)
        ( λ h → htpy-cone-Coseq A (cone-map-Coseq A c Y h) c'))
unique-mapping-property-sequential-limit {l3 = l3} A c up-X {Y} c' =
  is-contr-equiv'
    ( fib (cone-map-Coseq A c Y) c')
    ( equiv-tot
      ( λ h → equiv-htpy-cone-Coseq-eq A (cone-map-Coseq A c Y h) c'))
    ( unique-mapping-property-sequential-limit' A c up-X c')

htpy-universal-property-sequential-limit :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( up-X : {l : Level} → universal-property-sequential-limit l A c) →
  { Y : UU l3} (c' : cone-Coseq A Y) →
  htpy-cone-Coseq A
    ( cone-map-Coseq A c Y
      ( map-universal-property-sequential-limit A c up-X c'))
    ( c')
htpy-universal-property-sequential-limit A c up-X {Y} c' =
  htpy-cone-Coseq-eq A
    ( cone-map-Coseq A c Y
      ( map-universal-property-sequential-limit A c up-X c'))
    ( c')
    ( path-universal-property-sequential-limit A c up-X c')

uniqueness-map-sequential-limit' :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( up-X : {l : Level} → universal-property-sequential-limit l A c)
  { Y : UU l3} (c' : cone-Coseq A Y) →
  ( h : Y → X) (H : Id (cone-map-Coseq A c Y h) c')
  ( h' : Y → X) (H' : Id (cone-map-Coseq A c Y h') c') →
  h ~ h'
uniqueness-map-sequential-limit' A c up-X c' h H h' H' =
  htpy-eq
    ( ap pr1
      ( eq-is-contr
        ( unique-mapping-property-sequential-limit' A c up-X c')
          ( pair h H)
          ( pair h' H')))

uniqueness-map-sequential-limit :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( up-X : {l : Level} → universal-property-sequential-limit l A c) →
  { Y : UU l3} (c' : cone-Coseq A Y)
  ( h : Y → X) (H : htpy-cone-Coseq A (cone-map-Coseq A c Y h) c')
  ( h' : Y → X) (H' : htpy-cone-Coseq A (cone-map-Coseq A c Y h') c') →
  h ~ h'
uniqueness-map-sequential-limit A c up-X c' h H h' H' =
  htpy-eq
    ( ap pr1
      ( eq-is-contr
        ( unique-mapping-property-sequential-limit A c up-X c')
        ( pair h H)
        ( pair h' H')))

--------------------------------------------------------------------------------
    
{- We show a 3-for-2 property of sequential limits. -}

compose-cone-map-Coseq :
  { l1 l2 l3 l4 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X)
  { Y : UU l3} {Z : UU l4} (h : Y → X) (k : Z → Y) →
  Id ( cone-map-Coseq A (cone-map-Coseq A c Y h) Z k)
     ( cone-map-Coseq A c Z (h ∘ k))
compose-cone-map-Coseq A c h k = refl

module 3-for-2-sequential-limit
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} {Y : UU l3}
  ( c : cone-Coseq A X) (c' : cone-Coseq A Y) (h : Y → X)
  ( e : htpy-cone-Coseq A (cone-map-Coseq A c Y h) c')
  where

  triangle-cone-cone-Coseq :
    {l4 : Level} (Z : UU  l4) →
      ( cone-map-Coseq A c' Z) ~
      ( ( cone-map-Coseq A c Z) ∘ (λ (k : Z → Y) → h ∘ k))
  triangle-cone-cone-Coseq Z k =
    ap (λ t → cone-map-Coseq A t Z k)
      (inv (eq-htpy-cone-Coseq A (cone-map-Coseq A c Y h) c' e))

  is-equiv-universal-property-sequential-limit :
    ({l : Level} → universal-property-sequential-limit l A c) →
    ({l : Level} → universal-property-sequential-limit l A c') →
    is-equiv h
  is-equiv-universal-property-sequential-limit up-X up-Y =
    is-equiv-is-equiv-postcomp h (λ {l} Z →
      is-equiv-right-factor
        ( cone-map-Coseq A c' Z)
        ( cone-map-Coseq A c Z)
        ( λ k → h ∘ k)
        ( triangle-cone-cone-Coseq Z)
        ( up-X Z)
        ( up-Y Z))

  universal-property-sequential-limit-is-equiv' :
    ({l : Level} → universal-property-sequential-limit l A c) →
    is-equiv h →
    ({l : Level} → universal-property-sequential-limit l A c')
  universal-property-sequential-limit-is-equiv' up-X is-equiv-h Z =
    is-equiv-comp
      ( cone-map-Coseq A c' Z)
      ( cone-map-Coseq A c Z)
      ( λ k → h ∘ k)
      ( triangle-cone-cone-Coseq Z)
      ( is-equiv-postcomp-is-equiv h is-equiv-h Z)
      ( up-X Z)

  universal-property-sequential-limit-is-equiv :
    ({l : Level} → universal-property-sequential-limit l A c') →
    is-equiv h →
    ({l : Level} → universal-property-sequential-limit l A c)
  universal-property-sequential-limit-is-equiv up-Y is-equiv-h Z =
    is-equiv-left-factor
      ( cone-map-Coseq A c' Z)
      ( cone-map-Coseq A c Z)
      ( λ k → h ∘ k)
      ( triangle-cone-cone-Coseq Z)
      ( up-Y Z)
      ( is-equiv-postcomp-is-equiv h is-equiv-h Z)

open 3-for-2-sequential-limit public

--------------------------------------------------------------------------------

{- We prove the uniquely uniqueness of sequential limits. -}

uniquely-uniqueness-sequential-limit :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} {Y : UU l3} →
  ( c : cone-Coseq A X) (c' : cone-Coseq A Y) →
  ( {l : Level} → universal-property-sequential-limit l A c) →
  ( {l : Level} → universal-property-sequential-limit l A c') →
  is-contr (Σ (Y ≃ X)
    (λ e → htpy-cone-Coseq A (cone-map-Coseq A c Y (map-equiv e)) c'))
uniquely-uniqueness-sequential-limit A {X} {Y} c c' up-X up-Y =
  is-contr-total-Eq-substructure
    ( unique-mapping-property-sequential-limit A c up-X c')
    ( is-subtype-is-equiv)
    ( map-universal-property-sequential-limit A c up-X c')
    ( htpy-universal-property-sequential-limit A c up-X c')
    ( is-equiv-universal-property-sequential-limit A c c'
      ( map-universal-property-sequential-limit A c up-X c')
      ( htpy-universal-property-sequential-limit A c up-X c')
      ( up-X)
      ( up-Y))

--------------------------------------------------------------------------------

{- We introduce the sequence of function types. -}

mapping-sequence :
  { l1 l2 : Level} (A : Coseq-UU l1) (X : UU l2) → Coseq-UU (l1 ⊔ l2)
mapping-sequence A X =
  pair
    ( λ n → X → type-Coseq A n)
    ( λ n h → (map-Coseq A n) ∘ h)

cone-mapping-sequence :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( Y : UU l3) → cone-Coseq (mapping-sequence A Y) (Y → X)
cone-mapping-sequence A c Y =
  pair
    ( λ n h → (map-cone-Coseq A c n) ∘ h)
    ( λ n h → eq-htpy ((triangle-cone-Coseq A c n) ·r h))

{- -- unfinished
universal-property-sequential-limit-cone-mapping-sequence :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( up-X : {l : Level} → universal-property-sequential-limit l A c) →
  ( Y : UU l3) {l : Level} →
  universal-property-sequential-limit l
    ( mapping-sequence A Y)
    ( cone-mapping-sequence A c Y)
universal-property-sequential-limit-cone-mapping-sequence A c up-X Y Z =
  {!!}
-}
