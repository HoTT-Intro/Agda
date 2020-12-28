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

Naturality-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) →
  (h : (n : ℕ) → type-Coseq A n → type-Coseq B n) → UU (l1 ⊔ l2)
Naturality-hom-Coseq A B h =
  (n : ℕ) → ((map-Coseq B n) ∘ (h (succ-ℕ n))) ~ ((h n) ∘ (map-Coseq A n))

hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) → UU (l1 ⊔ l2)
hom-Coseq A B =
  Σ ((n : ℕ) → type-Coseq A n → type-Coseq B n) (Naturality-hom-Coseq A B)

map-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) →
  hom-Coseq A B → (n : ℕ) → type-Coseq A n → type-Coseq B n
map-hom-Coseq A B h = pr1 h

naturality-map-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (h : hom-Coseq A B) →
  Naturality-hom-Coseq A B (map-hom-Coseq A B h)
naturality-map-hom-Coseq A B h = pr2 h

{- We define composition of morphisms of cosequences -}

map-comp-hom-Coseq :
  {l1 l2 l3 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (C : Coseq-UU l3) →
  (g : hom-Coseq B C) (f : hom-Coseq A B) →
  (n : ℕ) → (type-Coseq A n) → (type-Coseq C n)
map-comp-hom-Coseq A B C g f n =
  ( map-hom-Coseq B C g n) ∘ ( map-hom-Coseq A B f n)

naturality-map-comp-hom-Coseq :
  {l1 l2 l3 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (C : Coseq-UU l3) →
  (g : hom-Coseq B C) (f : hom-Coseq A B) (n : ℕ) → 
  ( ( map-Coseq C n) ∘ (map-comp-hom-Coseq A B C g f (succ-ℕ n))) ~
  ( ( map-comp-hom-Coseq A B C g f n) ∘ (map-Coseq A n))
naturality-map-comp-hom-Coseq A B C g f n =
  ( ( naturality-map-hom-Coseq B C g n) ·r (map-hom-Coseq A B f (succ-ℕ n))) ∙h
  ( ( map-hom-Coseq B C g n) ·l (naturality-map-hom-Coseq A B f n))

comp-hom-Coseq :
  {l1 l2 l3 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (C : Coseq-UU l3) →
  (g : hom-Coseq B C) (f : hom-Coseq A B) → hom-Coseq A C
comp-hom-Coseq A B C g f =
  pair ( map-comp-hom-Coseq A B C g f)
       ( naturality-map-comp-hom-Coseq A B C g f)

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
      ( λ n → is-contr-total-equiv (type-Coseq A n)))
    ( pair (type-Coseq A) (λ n → equiv-id))
    ( is-contr-total-Eq-Π
      ( λ n g → g ~ (map-Coseq A n))
      ( λ n → is-contr-total-htpy' (map-Coseq A n)))

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
      ( λ n → is-contr-total-htpy (map-hom-Coseq A B f n)))
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
          ( is-contr-total-htpy' (naturality-map-hom-Coseq A B f n))))

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

universal-property-limit-Coseq :
  ( l : Level) {l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2}
  ( c : cone-Coseq A X) → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-limit-Coseq l A c =
  (Y : UU l) → is-equiv (cone-map-Coseq A c Y)

--------------------------------------------------------------------------------

{- We introduce the canonical sequential limit. -}

limit-Coseq :
  {l : Level} (A : Coseq-UU l) → UU l
limit-Coseq A =
  Σ ( (n : ℕ) → type-Coseq A n)
    ( λ a → (n : ℕ) → Id (map-Coseq A n (a (succ-ℕ n))) (a n))

point-limit-Coseq :
  {l : Level} (A : Coseq-UU l) (x : limit-Coseq A) (n : ℕ) →
  type-Coseq A n
point-limit-Coseq A x = pr1 x

path-limit-Coseq :
  {l : Level} (A : Coseq-UU l) (x : limit-Coseq A) (n : ℕ) →
  Id ( map-Coseq A n (point-limit-Coseq A x (succ-ℕ n)))
     ( point-limit-Coseq A x n)
path-limit-Coseq A x = pr2 x

{- We introduce a second canonical sequential limit. -}

limit-Coseq' : {l : Level} (A : Coseq-UU l) → UU l
limit-Coseq' A = cone-Coseq A unit

equiv-limit-Coseq :
  {l : Level} (A : Coseq-UU l) →
  limit-Coseq' A ≃ limit-Coseq A
equiv-limit-Coseq A =
  equiv-Σ
    ( λ a → (n : ℕ) → Id (map-Coseq A n (a (succ-ℕ n))) (a n))
    ( equiv-postcomp-Π (λ n → equiv-ev-star' (type-Coseq A n)))
    ( λ a →
      equiv-postcomp-Π
        ( λ n →
          equiv-ev-star (λ x → Id (map-Coseq A n (a (succ-ℕ n) x)) (a n x))))

--------------------------------------------------------------------------------

{- We characterize the identity type of the canonical sequential limit. -}

Eq-limit-Coseq :
  { l1 : Level} (A : Coseq-UU l1) (x y : limit-Coseq A) → UU l1
Eq-limit-Coseq A x y =
  Σ ( ( point-limit-Coseq A x) ~
      ( point-limit-Coseq A y))
    ( λ H → (n : ℕ) →
      Id ( ( ap (map-Coseq A n) (H (succ-ℕ n))) ∙
           ( path-limit-Coseq A y n))
         ( ( path-limit-Coseq A x n) ∙
           ( H n)))

refl-Eq-limit-Coseq :
  { l1 : Level} (A : Coseq-UU l1) (x : limit-Coseq A) →
  Eq-limit-Coseq A x x
refl-Eq-limit-Coseq A x =
  pair refl-htpy (inv-htpy right-unit-htpy)

Eq-limit-Coseq-eq :
  { l1 : Level} (A : Coseq-UU l1) (x y : limit-Coseq A) →
  Id x y → Eq-limit-Coseq A x y
Eq-limit-Coseq-eq A x .x refl =
  refl-Eq-limit-Coseq A x

is-contr-total-Eq-limit-Coseq :
  { l1 : Level} (A : Coseq-UU l1) (x : limit-Coseq A) →
  is-contr
    ( Σ (limit-Coseq A) (Eq-limit-Coseq A x))
is-contr-total-Eq-limit-Coseq A x =
  is-contr-total-Eq-structure
    ( λ y q (H : (n : ℕ) → Id (pr1 x n) (y n)) →
      (n : ℕ) →
        Id ((ap (map-Coseq A n) (H (succ-ℕ n))) ∙ (q n)) ((pr2 x n) ∙ (H n)))
    ( is-contr-total-Eq-Π
      ( λ n yn → Id (pr1 x n) yn)
      ( λ n → is-contr-total-path (pr1 x n)))
    ( pair (pr1 x) refl-htpy)
    ( is-contr-total-Eq-Π
      ( λ n q → Id q ((pr2 x n) ∙ refl))
      ( λ n → is-contr-total-path' ((pr2 x n) ∙ refl)))

is-equiv-Eq-limit-Coseq :
  { l1 : Level} (A : Coseq-UU l1) (x y : limit-Coseq A) →
  is-equiv (Eq-limit-Coseq-eq A x y)
is-equiv-Eq-limit-Coseq A x =
  fundamental-theorem-id x
    ( refl-Eq-limit-Coseq A x)
    ( is-contr-total-Eq-limit-Coseq A x)
    ( Eq-limit-Coseq-eq A x)

eq-Eq-limit-Coseq :
  { l1 : Level} (A : Coseq-UU l1) {x y : limit-Coseq A} →
  Eq-limit-Coseq A x y → Id x y
eq-Eq-limit-Coseq A {x} {y} =
  map-inv-is-equiv (is-equiv-Eq-limit-Coseq A x y)

--------------------------------------------------------------------------------

{- We give a second characterization of the identity type of the canonical
   sequential colimit, expressed as a canonical sequential colimit. -}

type-coseq-Eq-limit-Coseq' :
  {l : Level} (A : Coseq-UU l) (x y : limit-Coseq A) →
  (n : ℕ) → UU l
type-coseq-Eq-limit-Coseq' A x y n =
  Id ( point-limit-Coseq A x n)
     ( point-limit-Coseq A y n)

map-coseq-Eq-limit-Coseq' :
  {l : Level} (A : Coseq-UU l) (x y : limit-Coseq A) (n : ℕ) →
  type-coseq-Eq-limit-Coseq' A x y (succ-ℕ n) →
  type-coseq-Eq-limit-Coseq' A x y n
map-coseq-Eq-limit-Coseq' A x y n p =
  ( inv (path-limit-Coseq A x n)) ∙
  ( ( ap (map-Coseq A n) p) ∙
    ( path-limit-Coseq A y n))

coseq-Eq-limit-Coseq' :
  {l : Level} (A : Coseq-UU l) (x y : limit-Coseq A) → Coseq-UU l
coseq-Eq-limit-Coseq' A x y =
  pair ( type-coseq-Eq-limit-Coseq' A x y)
       ( map-coseq-Eq-limit-Coseq' A x y)

Eq-limit-Coseq' :
  {l : Level} (A : Coseq-UU l) (x y : limit-Coseq A) → UU l
Eq-limit-Coseq' A x y =
  limit-Coseq (coseq-Eq-limit-Coseq' A x y)

refl-Eq-limit-Coseq' :
  {l : Level} (A : Coseq-UU l) (x : limit-Coseq A) →
  Eq-limit-Coseq' A x x
refl-Eq-limit-Coseq' A x =
  pair (λ n → refl) (λ n → left-inv (path-limit-Coseq A x n))

Eq-limit-Coseq-eq' :
  {l : Level} (A : Coseq-UU l) (x y : limit-Coseq A) →
  Id x y → Eq-limit-Coseq' A x y
Eq-limit-Coseq-eq' A x .x refl =
  refl-Eq-limit-Coseq' A x

is-contr-total-Eq-limit-Coseq' :
  {l : Level} (A : Coseq-UU l) (x : limit-Coseq A) →
  is-contr
    ( Σ (limit-Coseq A) (Eq-limit-Coseq' A x))
is-contr-total-Eq-limit-Coseq' A x =
  is-contr-total-Eq-structure
    ( λ a H (p : (n : ℕ) → Id (point-limit-Coseq A x n) (a n)) →
      (n : ℕ) →
      Id ( inv
           ( path-limit-Coseq A x n) ∙
           ( ( ap (map-Coseq A n) (p (succ-ℕ n))) ∙ (H n)))
         ( p n))
    ( is-contr-total-htpy (point-limit-Coseq A x))
    ( pair (point-limit-Coseq A x) refl-htpy)
    ( is-contr-equiv'
      ( Σ ( (n : ℕ) →
            Id ( map-Coseq A n
                 ( point-limit-Coseq A x (succ-ℕ n)))
               ( point-limit-Coseq A x n))
          ( λ p →
            (n : ℕ) → Id (path-limit-Coseq A x n) (p n)))
      ( equiv-tot
        ( λ p →
          equiv-postcomp-Π
            ( λ n →
              ( equiv-inv refl (inv (pr2 x n) ∙ p n)) ∘e
              ( ( equiv-inv-con (pr2 x n) refl (p n)) ∘e
                ( equiv-concat right-unit (p n))))))
      ( is-contr-total-htpy (path-limit-Coseq A x)))

is-equiv-Eq-limit-Coseq-eq' :
  {l : Level} (A : Coseq-UU l) (x y : limit-Coseq A) →
  is-equiv (Eq-limit-Coseq-eq' A x y)
is-equiv-Eq-limit-Coseq-eq' A x =
  fundamental-theorem-id x
    ( refl-Eq-limit-Coseq' A x)
    ( is-contr-total-Eq-limit-Coseq' A x)
    ( Eq-limit-Coseq-eq' A x)

--------------------------------------------------------------------------------

{- We equip the canonical sequential limit with the structure of a cone. -}

cone-limit-Coseq :
  {l1 : Level} (A : Coseq-UU l1) → cone-Coseq A (limit-Coseq A)
cone-limit-Coseq A =
  pair ( λ n a → point-limit-Coseq A a n)
       ( λ n a → path-limit-Coseq A a n)

--------------------------------------------------------------------------------

{- We show that the canonical sequential limit satisfies the universal property
   of sequential limits. -}

gap-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) {Y : UU l2} → cone-Coseq A Y →
  Y → limit-Coseq A
gap-Coseq A c y =
  pair ( λ n → map-cone-Coseq A c n y)
       ( λ n → triangle-cone-Coseq A c n y)

issec-gap-Coseq' :
  { l1 l2 : Level} (A : Coseq-UU l1) {Y : UU l2} (c : cone-Coseq A Y) →
  htpy-cone-Coseq A
    ( cone-map-Coseq A (cone-limit-Coseq A) Y (gap-Coseq A c))
    ( c)
issec-gap-Coseq' A c = refl-htpy-cone-Coseq A c

issec-gap-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) (Y : UU l2) →
  ((cone-map-Coseq A (cone-limit-Coseq A) Y) ∘ (gap-Coseq A {Y})) ~ id
issec-gap-Coseq A Y c =
  eq-htpy-cone-Coseq A
    ( cone-map-Coseq A
      ( cone-limit-Coseq A)
      ( Y)
      ( gap-Coseq A c))
    ( c)
    ( issec-gap-Coseq' A c)

isretr-gap-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) (Y : UU l2) →
  ((gap-Coseq A {Y}) ∘ (cone-map-Coseq A (cone-limit-Coseq A) Y)) ~ id
isretr-gap-Coseq A Y h =
  eq-htpy (λ y →
    eq-Eq-limit-Coseq A
      ( refl-Eq-limit-Coseq A (h y)))

is-equiv-cone-map-cone-limit-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) (Y : UU l2) →
  is-equiv (cone-map-Coseq A (cone-limit-Coseq A) Y)
is-equiv-cone-map-cone-limit-Coseq A Y =
  is-equiv-has-inverse
    ( gap-Coseq A)
    ( issec-gap-Coseq A Y)
    ( isretr-gap-Coseq A Y)

universal-property-limit-limit-Coseq :
  ( l : Level) {l1 : Level} (A : Coseq-UU l1) →
  universal-property-limit-Coseq l A (cone-limit-Coseq A)
universal-property-limit-limit-Coseq l A Y =
  is-equiv-cone-map-cone-limit-Coseq A Y

--------------------------------------------------------------------------------

{- Unique mapping property for sequential limits. -}

unique-mapping-property-sequential-limit' :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( up-X : {l : Level} → universal-property-limit-Coseq l A c)
  { Y : UU l3} (c' : cone-Coseq A Y) →
  is-contr (fib (cone-map-Coseq A c Y) c')
unique-mapping-property-sequential-limit' A c up-X {Y} =
  is-contr-map-is-equiv (up-X Y)

map-universal-property-limit-Coseq :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( up-X : {l : Level} → universal-property-limit-Coseq l A c) →
  { Y : UU l3} (c' : cone-Coseq A Y) → Y → X
map-universal-property-limit-Coseq A c up-X c' =
  pr1 (center (unique-mapping-property-sequential-limit' A c up-X c'))

path-universal-property-limit-Coseq :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( up-X : {l : Level} → universal-property-limit-Coseq l A c) →
  { Y : UU l3} (c' : cone-Coseq A Y) →
  Id ( cone-map-Coseq A c Y
       ( map-universal-property-limit-Coseq A c up-X c'))
     ( c')
path-universal-property-limit-Coseq A c up-X c' =
  pr2 (center (unique-mapping-property-sequential-limit' A c up-X c'))

unique-mapping-property-sequential-limit :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( up-X : {l : Level} → universal-property-limit-Coseq l A c) →
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

htpy-universal-property-limit-Coseq :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( up-X : {l : Level} → universal-property-limit-Coseq l A c) →
  { Y : UU l3} (c' : cone-Coseq A Y) →
  htpy-cone-Coseq A
    ( cone-map-Coseq A c Y
      ( map-universal-property-limit-Coseq A c up-X c'))
    ( c')
htpy-universal-property-limit-Coseq A c up-X {Y} c' =
  htpy-cone-Coseq-eq A
    ( cone-map-Coseq A c Y
      ( map-universal-property-limit-Coseq A c up-X c'))
    ( c')
    ( path-universal-property-limit-Coseq A c up-X c')

uniqueness-map-sequential-limit' :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( up-X : {l : Level} → universal-property-limit-Coseq l A c)
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
  ( up-X : {l : Level} → universal-property-limit-Coseq l A c) →
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

  is-equiv-universal-property-limit-Coseq :
    ({l : Level} → universal-property-limit-Coseq l A c) →
    ({l : Level} → universal-property-limit-Coseq l A c') →
    is-equiv h
  is-equiv-universal-property-limit-Coseq up-X up-Y =
    is-equiv-is-equiv-postcomp h (λ {l} Z →
      is-equiv-right-factor
        ( cone-map-Coseq A c' Z)
        ( cone-map-Coseq A c Z)
        ( λ k → h ∘ k)
        ( triangle-cone-cone-Coseq Z)
        ( up-X Z)
        ( up-Y Z))

  universal-property-limit-is-equiv-Coseq' :
    ({l : Level} → universal-property-limit-Coseq l A c) →
    is-equiv h →
    ({l : Level} → universal-property-limit-Coseq l A c')
  universal-property-limit-is-equiv-Coseq' up-X is-equiv-h Z =
    is-equiv-comp
      ( cone-map-Coseq A c' Z)
      ( cone-map-Coseq A c Z)
      ( λ k → h ∘ k)
      ( triangle-cone-cone-Coseq Z)
      ( is-equiv-postcomp-is-equiv h is-equiv-h Z)
      ( up-X Z)

  universal-property-limit-is-equiv-Coseq :
    ({l : Level} → universal-property-limit-Coseq l A c') →
    is-equiv h →
    ({l : Level} → universal-property-limit-Coseq l A c)
  universal-property-limit-is-equiv-Coseq up-Y is-equiv-h Z =
    is-equiv-left-factor
      ( cone-map-Coseq A c' Z)
      ( cone-map-Coseq A c Z)
      ( λ k → h ∘ k)
      ( triangle-cone-cone-Coseq Z)
      ( up-Y Z)
      ( is-equiv-postcomp-is-equiv h is-equiv-h Z)

open 3-for-2-sequential-limit public

--------------------------------------------------------------------------------

{- We simplify the proof that something is a limit of a cosequence. -}

is-limit-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  UU (l1 ⊔ l2)
is-limit-Coseq A {X} c = is-equiv (gap-Coseq A c)

universal-property-limit-is-limit-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  is-limit-Coseq A c → {l : Level} → universal-property-limit-Coseq l A c
universal-property-limit-is-limit-Coseq A {X} c H =
  universal-property-limit-is-equiv-Coseq' A
    ( cone-limit-Coseq A)
    ( c)
    ( gap-Coseq A c)
    ( issec-gap-Coseq' A c)
    ( λ {l'} → universal-property-limit-limit-Coseq l' A)
    ( H)

is-limit-universal-property-limit-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ({l : Level} → universal-property-limit-Coseq l A c) → is-limit-Coseq A c
is-limit-universal-property-limit-Coseq A {X} c up-c =
  is-equiv-universal-property-limit-Coseq A
    ( cone-limit-Coseq A)
    ( c)
    ( gap-Coseq A c)
    ( issec-gap-Coseq' A c)
    ( λ {l'} → universal-property-limit-limit-Coseq l' A)
    ( up-c)

--------------------------------------------------------------------------------

{- We define the functorial action of limits -}

point-map-limit-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  ((n : ℕ) → type-Coseq A n) → ((n : ℕ) → type-Coseq B n)
point-map-limit-Coseq A B f x n =
  map-hom-Coseq A B f n (x n)

path-map-limit-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  (x : (n : ℕ) → type-Coseq A n)
  (p : (n : ℕ) → Id (map-Coseq A n (x (succ-ℕ n))) (x n))
  (n : ℕ) →
  Id ( map-Coseq B n (point-map-limit-Coseq A B f x (succ-ℕ n)))
     ( point-map-limit-Coseq A B f x n)
path-map-limit-Coseq A B f x p n =
  ( naturality-map-hom-Coseq A B f n (x (succ-ℕ n))) ∙
  ( ap (map-hom-Coseq A B f n) (p n))

map-limit-Coseq' :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  limit-Coseq A → limit-Coseq B
map-limit-Coseq' A B f =
  map-Σ
    ( λ y → (n : ℕ) → Id (map-Coseq B n (y (succ-ℕ n))) (y n))
    ( point-map-limit-Coseq A B f)
    ( path-map-limit-Coseq A B f)

map-limit-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  limit-Coseq A → limit-Coseq B
map-limit-Coseq A B f =
  gap-Coseq B
    ( comp-hom-Coseq (constant-Coseq (limit-Coseq A))
    ( A)
    ( B)
    ( f)
    ( cone-limit-Coseq A))

htpy-map-limit-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  map-limit-Coseq' A B f ~ map-limit-Coseq A B f
htpy-map-limit-Coseq A B f x =
  eq-Eq-limit-Coseq B
    ( refl-Eq-limit-Coseq B (map-limit-Coseq A B f x))

--------------------------------------------------------------------------------

{- We introduce the notion of diagonal fillers for morphisms of cosequences -}

has-filler-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D) (H : (k ∘ g) ~ (h ∘ f)) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
has-filler-square {A = A} {B} {C} {D} f g h k H =
  Σ ( C → B)
    ( λ j →
       Σ ( (j ∘ g) ~ f)
         ( λ T →
           Σ ( k ~ (h ∘ j))
             ( λ S → ((S ·r g) ∙h ( h ·l T)) ~ H)))

map-has-filler-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D) (H : (k ∘ g) ~ (h ∘ f)) →
  has-filler-square f g h k H → C → B
map-has-filler-square f g h k H J = pr1 J

upper-triangle-has-filler-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D) (H : (k ∘ g) ~ (h ∘ f)) →
  (J : has-filler-square f g h k H) →
  ((map-has-filler-square f g h k H J) ∘ g) ~ f
upper-triangle-has-filler-square f g h k H J = pr1 (pr2 J)

lower-triangle-has-filler-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D) (H : (k ∘ g) ~ (h ∘ f)) →
  (J : has-filler-square f g h k H) →
  k ~ (h ∘ (map-has-filler-square f g h k H J))
lower-triangle-has-filler-square f g h k H J = pr1 (pr2 (pr2 J))

coherence-has-filler-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D) (H : (k ∘ g) ~ (h ∘ f)) →
  (J : has-filler-square f g  h k H) →
  ( ( (lower-triangle-has-filler-square f g h k H J) ·r g) ∙h
    ( h ·l (upper-triangle-has-filler-square f g h k H J))) ~ H
coherence-has-filler-square f g h k H J = pr2 (pr2 (pr2 J))

has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  UU (l1 ⊔ l2)
has-filler-hom-Coseq A B f =
  (n : ℕ) →
  has-filler-square
    ( map-Coseq A n)
    ( map-hom-Coseq A B f (succ-ℕ n))
    ( map-hom-Coseq A B f n)
    ( map-Coseq B n)
    ( naturality-map-hom-Coseq A B f n)

map-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  has-filler-hom-Coseq A B f →
  (n : ℕ) → type-Coseq B (succ-ℕ n) → type-Coseq A n
map-has-filler-hom-Coseq A B f J n = pr1 (J n)

upper-triangle-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  (J : has-filler-hom-Coseq A B f) (n : ℕ) →
  ( ( map-has-filler-hom-Coseq A B f J n) ∘
    ( map-hom-Coseq A B f (succ-ℕ n))) ~ (map-Coseq A n)
upper-triangle-has-filler-hom-Coseq A B f J n = pr1 (pr2 (J n))

lower-triangle-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  (J : has-filler-hom-Coseq A B f) (n : ℕ) →
  (map-Coseq B n) ~
  ((map-hom-Coseq A B f n) ∘ (map-has-filler-hom-Coseq A B f J n))
lower-triangle-has-filler-hom-Coseq A B f J n = pr1 (pr2 (pr2 (J n)))

coherence-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  (J : has-filler-hom-Coseq A B f) (n : ℕ) →
  ( ( ( lower-triangle-has-filler-hom-Coseq A B f J n) ·r
      ( map-hom-Coseq A B f (succ-ℕ n))) ∙h
    ( ( map-hom-Coseq A B f n) ·l
      ( upper-triangle-has-filler-hom-Coseq A B f J n))) ~
  ( naturality-map-hom-Coseq A B f n)
coherence-has-filler-hom-Coseq A B f J n = pr2 (pr2 (pr2 (J n)))

--------------------------------------------------------------------------------

{- We show that any morphism of cosequences that has a diagonal filler induces
   an equivalence on limits -}

point-map-inv-limit-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  has-filler-hom-Coseq A B f →
  ((n : ℕ) → type-Coseq B n) → ((n : ℕ) → type-Coseq A n)
point-map-inv-limit-has-filler-hom-Coseq A B f J y n =
  map-has-filler-hom-Coseq A B f J n (y (succ-ℕ n))

path-map-inv-limit-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  (J : has-filler-hom-Coseq A B f) (y : (n : ℕ) → type-Coseq B n)
  (z : (n : ℕ) → Id (map-Coseq B n (y (succ-ℕ n))) (y n)) → (n : ℕ) →
  Id ( map-Coseq A n
       ( point-map-inv-limit-has-filler-hom-Coseq
         A B f J y (succ-ℕ n)))
     ( point-map-inv-limit-has-filler-hom-Coseq A B f J y n)
path-map-inv-limit-has-filler-hom-Coseq A B f J y z n =
  ( inv ( H (j' (y (succ-ℕ (succ-ℕ n)))))) ∙
  ( ( ap j (inv (K (y (succ-ℕ (succ-ℕ n)))))) ∙
    ( ap j (z (succ-ℕ n))))
  where
  j = map-has-filler-hom-Coseq A B f J n
  j' = map-has-filler-hom-Coseq A B f J (succ-ℕ n)
  H = upper-triangle-has-filler-hom-Coseq A B f J n
  K = lower-triangle-has-filler-hom-Coseq A B f J (succ-ℕ n)

map-inv-limit-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  has-filler-hom-Coseq A B f → limit-Coseq B → limit-Coseq A
map-inv-limit-has-filler-hom-Coseq A B f J =
  map-Σ
    ( λ x → (n : ℕ) → Id (map-Coseq A n (x (succ-ℕ n))) (x n))
    ( point-map-inv-limit-has-filler-hom-Coseq A B f J)
    ( path-map-inv-limit-has-filler-hom-Coseq A B f J)

{-
issec-map-inv-limit-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  (J : has-filler-hom-Coseq A B f) →
  ( ( map-limit-Coseq' A B f) ∘
    ( map-inv-limit-has-filler-hom-Coseq A B f J)) ~ id
issec-map-inv-limit-has-filler-hom-Coseq A B f J (pair y q) =
  eq-Eq-limit-Coseq B
    ( pair
      ( λ n → (inv (K n (y (succ-ℕ n)))) ∙ (q n))
      ( λ n →
         ( ap
           ( concat'
             ( map-Coseq B n
               ( map-hom-Coseq A B f (succ-ℕ n)
                 ( j (succ-ℕ n) (y (succ-ℕ (succ-ℕ n)))))) (q n))
           {!!}) ∙
         ( assoc
           ( ( naturality-map-hom-Coseq A B f n
               ( j (succ-ℕ n) (y (succ-ℕ (succ-ℕ n))))) ∙
             ( ap ( map-hom-Coseq A B f n)
                  ( ( inv (H n (j (succ-ℕ n) (y (succ-ℕ (succ-ℕ n)))))) ∙
                    ( ( ap (j n) (inv (K (succ-ℕ n) (y (succ-ℕ (succ-ℕ n)))))) ∙
                      ( ap (j n) (q (succ-ℕ n)))))))
           ( inv (K n (y (succ-ℕ n))))
           ( q n))))
  where
  j = map-has-filler-hom-Coseq A B f J
  H = upper-triangle-has-filler-hom-Coseq A B f J
  K = lower-triangle-has-filler-hom-Coseq A B f J
  M = coherence-has-filler-hom-Coseq A B f J
-}

{-
is-equiv-map-limit-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  has-filler-hom-Coseq A B f → is-equiv (map-limit-Coseq A B f)
is-equiv-map-limit-has-filler-hom-Coseq A B f J = {!!}

universal-property-limit-has-filler-Coeq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B)
  (X : UU l2) (c : cone-Coseq A X) → has-filler-hom-Coseq A B f →
  universal-property-limit-Coseq l4 A c →
  universal-property-limit-Coseq l4 B
    ( comp-hom-Coseq (constant-Coseq X) A B f c)
universal-property-limit-has-filler-Coeq A B f X c J up-A Y = {!!}
-}
--------------------------------------------------------------------------------

{- We prove the uniquely uniqueness of sequential limits. -}

uniquely-uniqueness-sequential-limit :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} {Y : UU l3} →
  ( c : cone-Coseq A X) (c' : cone-Coseq A Y) →
  ( {l : Level} → universal-property-limit-Coseq l A c) →
  ( {l : Level} → universal-property-limit-Coseq l A c') →
  is-contr (Σ (Y ≃ X)
    (λ e → htpy-cone-Coseq A (cone-map-Coseq A c Y (map-equiv e)) c'))
uniquely-uniqueness-sequential-limit A {X} {Y} c c' up-X up-Y =
  is-contr-total-Eq-substructure
    ( unique-mapping-property-sequential-limit A c up-X c')
    ( is-subtype-is-equiv)
    ( map-universal-property-limit-Coseq A c up-X c')
    ( htpy-universal-property-limit-Coseq A c up-X c')
    ( is-equiv-universal-property-limit-Coseq A c c'
      ( map-universal-property-limit-Coseq A c up-X c')
      ( htpy-universal-property-limit-Coseq A c up-X c')
      ( up-X)
      ( up-Y))

--------------------------------------------------------------------------------

{- We show that the shifted cosequence as an equivalent limit -}

type-shift-Coseq : {l : Level} → Coseq-UU l → ℕ → UU l
type-shift-Coseq A n = type-Coseq A (succ-ℕ n)

map-shift-Coseq :
  {l : Level} (A : Coseq-UU l) (n : ℕ) →
  type-shift-Coseq A (succ-ℕ n) → type-shift-Coseq A n
map-shift-Coseq A n = map-Coseq A (succ-ℕ n)

shift-Coseq : {l : Level} → Coseq-UU l → Coseq-UU l
shift-Coseq A = pair (type-shift-Coseq A) (map-shift-Coseq A)

limit-shift-Coseq :
  {l : Level} → Coseq-UU l → UU l
limit-shift-Coseq A = limit-Coseq (shift-Coseq A)

map-hom-shift-Coseq :
  {l : Level} (A : Coseq-UU l) (n : ℕ) →
  type-Coseq A (succ-ℕ n) → type-Coseq A n
map-hom-shift-Coseq = map-Coseq

naturality-map-hom-shift-Coseq :
  {l : Level} (A : Coseq-UU l) →
  Naturality-hom-Coseq (shift-Coseq A) A (map-hom-shift-Coseq A)
naturality-map-hom-shift-Coseq A n = refl-htpy

hom-shift-Coseq : {l : Level} (A : Coseq-UU l) → hom-Coseq (shift-Coseq A) A
hom-shift-Coseq A =
  pair (map-hom-shift-Coseq A) (naturality-map-hom-shift-Coseq A)

cone-limit-shift-Coseq :
  {l : Level} (A : Coseq-UU l) → cone-Coseq A (limit-shift-Coseq A)
cone-limit-shift-Coseq A =
  comp-hom-Coseq
    ( constant-Coseq (limit-Coseq (shift-Coseq A)))
    ( shift-Coseq A)
    ( A)
    ( hom-shift-Coseq A)
    ( cone-limit-Coseq (shift-Coseq A))

map-limit-shift-Coseq' :
  {l : Level} (A : Coseq-UU l) → limit-shift-Coseq A → limit-Coseq A
map-limit-shift-Coseq' A =
  gap-Coseq A (cone-limit-shift-Coseq A)

map-limit-shift-Coseq :
  {l : Level} (A : Coseq-UU l) →
  limit-Coseq (shift-Coseq A) → limit-Coseq A
map-limit-shift-Coseq A =
  map-limit-Coseq (shift-Coseq A) A (hom-shift-Coseq A)

htpy-map-limit-shift-Coseq :
  {l : Level} (A : Coseq-UU l) →
  map-limit-shift-Coseq' A ~ map-limit-shift-Coseq A
htpy-map-limit-shift-Coseq A = refl-htpy

map-inv-limit-shift-Coseq :
  {l : Level} (A : Coseq-UU l) →
  limit-Coseq A → limit-Coseq (shift-Coseq A)
map-inv-limit-shift-Coseq A =
  map-Σ
    ( λ x → (n : ℕ) → Id (map-Coseq A (succ-ℕ n) (x (succ-ℕ n))) (x n))
    ( λ x n → x (succ-ℕ n))
    ( λ x p n → p (succ-ℕ n))

issec-map-inv-limit-shift-Coseq :
  {l : Level} (A : Coseq-UU l) →
  ( ( map-limit-shift-Coseq A) ∘ ( map-inv-limit-shift-Coseq A)) ~ id
issec-map-inv-limit-shift-Coseq A x =
  eq-Eq-limit-Coseq A (pair (pr2 x) (λ n → refl))

isretr-map-inv-limit-shift-Coseq :
  {l : Level} (A : Coseq-UU l) →
  ( ( map-inv-limit-shift-Coseq A) ∘ (map-limit-shift-Coseq A)) ~ id
isretr-map-inv-limit-shift-Coseq A x =
  eq-Eq-limit-Coseq (shift-Coseq A) (pair (pr2 x) (λ n → refl))

is-limit-cone-limit-shift-Coseq :
  {l : Level} (A : Coseq-UU l) →
  is-limit-Coseq A (cone-limit-shift-Coseq A)
is-limit-cone-limit-shift-Coseq A =
  is-equiv-has-inverse
    ( map-inv-limit-shift-Coseq A)
    ( issec-map-inv-limit-shift-Coseq A)
    ( isretr-map-inv-limit-shift-Coseq A)

equiv-limit-shift-Coseq :
  {l : Level} (A : Coseq-UU l) → (limit-shift-Coseq A) ≃ (limit-Coseq A)
equiv-limit-shift-Coseq A =
  pair (map-limit-shift-Coseq A) (is-limit-cone-limit-shift-Coseq A)

--------------------------------------------------------------------------------

map-hom-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  (J : has-filler-hom-Coseq A B f) (n : ℕ) →
  type-Coseq B (succ-ℕ n) → type-Coseq A n
map-hom-has-filler-hom-Coseq = map-has-filler-hom-Coseq

naturality-map-hom-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  (J : has-filler-hom-Coseq A B f) →
  Naturality-hom-Coseq (shift-Coseq B) A (map-hom-has-filler-hom-Coseq A B f J)
naturality-map-hom-has-filler-hom-Coseq A B f J n b =
  ( inv
    ( upper-triangle-has-filler-hom-Coseq A B f J n
      ( map-hom-has-filler-hom-Coseq A B f J (succ-ℕ n) b))) ∙
  ( inv
    ( ap (map-hom-has-filler-hom-Coseq A B f J n)
      ( lower-triangle-has-filler-hom-Coseq A B f J (succ-ℕ n) b)))

hom-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  (J : has-filler-hom-Coseq A B f) → hom-Coseq (shift-Coseq B) A
hom-has-filler-hom-Coseq A B f J =
  pair ( map-hom-has-filler-hom-Coseq A B f J)
       ( naturality-map-hom-has-filler-hom-Coseq A B f J)

htpy-triangle-hom-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  (J : has-filler-hom-Coseq A B f) (n : ℕ) →
  ( map-hom-Coseq A B f n ∘ map-hom-has-filler-hom-Coseq A B f J n) ~
  ( map-hom-shift-Coseq B n)
htpy-triangle-hom-has-filler-hom-Coseq A B f J n =
  inv-htpy (lower-triangle-has-filler-hom-Coseq A B f J n)

interchange-whisker-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f g : A → B}
  {h k : B → C} (G : f ~ g) (H : h ~ k) →
  ((H ·r f) ∙h (k ·l G)) ~ ((h ·l G) ∙h (H ·r g))
interchange-whisker-htpy G H a = htpy-nat H (G a)

naturality-triangle-hom-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  (J : has-filler-hom-Coseq A B f) →
  naturality-htpy-hom-Coseq (shift-Coseq B) B
    ( comp-hom-Coseq (shift-Coseq B) A B f
      ( hom-has-filler-hom-Coseq A B f J))
    ( hom-shift-Coseq B)
    ( htpy-triangle-hom-has-filler-hom-Coseq A B f J)
naturality-triangle-hom-has-filler-hom-Coseq A B f J n b =
  ( right-unit ∙ ( ap-inv (pr2 B n) (K (succ-ℕ n) b))) ∙
  ( inv
    ( ( ap
        ( concat'
          ( map-Coseq B n (pr1 f (succ-ℕ n) (j (succ-ℕ n) b)))
          ( inv (K n (pr2 B (succ-ℕ n) b))))
        ( ( ap
            ( concat
              ( pr2 f n (j (succ-ℕ n) b))
              ( pr1 f n (j n (pr2 B (succ-ℕ n) b))))
            ( ap-concat
              ( pr1 f n)
              ( inv (H n (j (succ-ℕ n) b)))
              ( inv (ap (j n) (K (succ-ℕ n) b))))) ∙
          ( inv
            ( assoc
              ( pr2 f n (j (succ-ℕ n) b))
              ( ap (pr1 f n) (inv (H n (j (succ-ℕ n) b))))
              ( ap (pr1 f n) (inv (ap (j n) (K (succ-ℕ n) b)))))))) ∙
      ( ( assoc
          ( ( pr2 f n (j (succ-ℕ n) b)) ∙
            ( ap (pr1 f n) (inv (H n (j (succ-ℕ n) b)))))
          ( ap (pr1 f n) (inv (ap (j n) (K (succ-ℕ n) b))))
          ( inv (K n (pr2 B (succ-ℕ n) b)))) ∙
        ( ( ap
            ( concat
              ( ( pr2 f n (j (succ-ℕ n) b)) ∙
                ( ap (pr1 f n) (inv (H n (j (succ-ℕ n) b)))))
              ( map-Coseq B n (map-Coseq B (succ-ℕ n) b)))
            ( ( ap
                ( concat'
                  ( pr1 f n (j n (pr1 f (succ-ℕ n) (j (succ-ℕ n) b))))
                  ( inv (K n (pr2 B (succ-ℕ n) b))))
                ( ( ap-inv (pr1 f n) (ap (j n) (K (succ-ℕ n) b))) ∙
                  ( ap
                    ( inv)
                    ( inv (ap-comp (pr1 f n) (j n) (K (succ-ℕ n) b)))))) ∙
              ( ( inv
                  ( distributive-inv-concat
                    ( K n (pr2 B (succ-ℕ n) b))
                    ( ap ((pr1 f n) ∘ (j n)) (K (succ-ℕ n) b)))) ∙
                ( ( ap
                    ( inv)
                    ( interchange-whisker-htpy (K (succ-ℕ n)) (K n) b)) ∙
                  ( distributive-inv-concat
                    ( ap (pr2 B n) (K (succ-ℕ n) b))
                    ( K n (pr1 f (succ-ℕ n) (j (succ-ℕ n) b)))))))) ∙
          ( ( inv
              ( assoc
                ( ( pr2 f n (j (succ-ℕ n) b)) ∙
                  ( ap (pr1 f n) (inv (H n (j (succ-ℕ n) b)))))
                ( inv (K n (pr1 f (succ-ℕ n) (j (succ-ℕ n) b))))
                ( inv (ap (pr2 B n) (K (succ-ℕ n) b))))) ∙
            ( ap
              ( concat'
                ( pr2 B n (pr1 f (succ-ℕ n) (j (succ-ℕ n) b)))
                ( inv (ap (pr2 B n) (K (succ-ℕ n) b))))
              ( inv
                ( con-inv
                  ( refl)
                  ( K n (pr1 f (succ-ℕ n) (j (succ-ℕ n) b)))
                  ( ( pr2 f n (j (succ-ℕ n) b)) ∙ 
                    ( ap (pr1 f n) (inv (H n (j (succ-ℕ n) b)))))
                  ( ( con-inv
                      ( K n (pr1 f (succ-ℕ n) (j (succ-ℕ n) b)))
                      ( ap (pr1 f n) (H n (j (succ-ℕ n) b)))
                      ( pr2 f n (j (succ-ℕ n) b))
                      ( M n (j (succ-ℕ n) b))) ∙
                    ( ap
                      ( concat
                        ( pr2 f n (j (succ-ℕ n) b))
                        ( pr1 f n (j n (pr1 f (succ-ℕ n) (j (succ-ℕ n) b)))))
                      ( inv
                        ( ap-inv (pr1 f n) (H n (j (succ-ℕ n) b))))))))))))))
  where
  j = map-has-filler-hom-Coseq A B f J
  H = upper-triangle-has-filler-hom-Coseq A B f J
  K = lower-triangle-has-filler-hom-Coseq A B f J
  M = coherence-has-filler-hom-Coseq A B f J

--------------------------------------------------------------------------------

{- We show that exponents preserve sequential limits -}

exponent-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) (X : UU l2) → Coseq-UU (l1 ⊔ l2)
exponent-Coseq A X =
  pair
    ( λ n → X → type-Coseq A n)
    ( λ n h → (map-Coseq A n) ∘ h)

limit-Coseq-exponent-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) (X : UU l2) → UU (l1 ⊔ l2)
limit-Coseq-exponent-Coseq A X =
  X → limit-Coseq A

cone-limit-Coseq-exponent-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (X : UU l2) →
  cone-Coseq
    ( exponent-Coseq A X)
    ( limit-Coseq-exponent-Coseq A X)
cone-limit-Coseq-exponent-Coseq A X =
  pair
    ( λ n h →
      ( map-cone-Coseq A (cone-limit-Coseq A) n) ∘ h)
    ( λ n h →
      eq-htpy
        ( (triangle-cone-Coseq A (cone-limit-Coseq A) n) ·r h))

cone-exponent-Coseq :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( Y : UU l3) → cone-Coseq (exponent-Coseq A Y) (Y → X)
cone-exponent-Coseq A c Y =
  pair
    ( λ n h → (map-cone-Coseq A c n) ∘ h)
    ( λ n h → eq-htpy ((triangle-cone-Coseq A c n) ·r h))

{-
universal-property-limit-cone-exponent-Coseq :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( up-X : {l : Level} → universal-property-limit-Coseq l A c) →
  ( Y : UU l3) {l : Level} →
  universal-property-limit-Coseq l
    ( exponent-Coseq A Y)
    ( cone-exponent-Coseq A c Y)
universal-property-limit-cone-exponent-Coseq A c up-X Y Z =
  {!!}
-}

--------------------------------------------------------------------------------

{- We show that coproducts preserve sequential limits -}

type-coprod-Coseq :
  {l1 l2 : Level} → Coseq-UU l1 → Coseq-UU l2 → ℕ → UU (l1 ⊔ l2)
type-coprod-Coseq A B n = coprod (type-Coseq A n) (type-Coseq B n)

map-coprod-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (n : ℕ) →
  type-coprod-Coseq A B (succ-ℕ n) → type-coprod-Coseq A B n
map-coprod-Coseq A B n =
  map-coprod (map-Coseq A n) (map-Coseq B n)

coprod-Coseq :
  {l1 l2 : Level} → Coseq-UU l1 → Coseq-UU l2 → Coseq-UU (l1 ⊔ l2)
coprod-Coseq A B =
  pair (type-coprod-Coseq A B) (map-coprod-Coseq A B)

{- We introduce dependent sequences -}

dependent-Coseq-UU :
  (l : Level) {l1 : Level} (A : Coseq-UU l1) → UU (lsuc l ⊔ l1)
dependent-Coseq-UU l A =
  Σ ( (n : ℕ) → type-Coseq A n → UU l)
    ( λ B →
      (n : ℕ) (a : type-Coseq A (succ-ℕ n)) →
      B (succ-ℕ n) a → B n (map-Coseq A n a))

type-dependent-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A) →
  (n : ℕ) → type-Coseq A n → UU l2
type-dependent-Coseq A = pr1

map-dependent-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A) →
  (n : ℕ) (a : type-Coseq A (succ-ℕ n)) →
  type-dependent-Coseq A B (succ-ℕ n) a →
  type-dependent-Coseq A B n (map-Coseq A n a)
map-dependent-Coseq A = pr2

{- We introduce dependent morphisms for dependent cosequences -}

Map-hom-dependent-Coseq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C)
  (f : hom-Coseq A C) → UU (l1 ⊔ l2 ⊔ l4)
Map-hom-dependent-Coseq A B C D f =
  (n : ℕ) (a : type-Coseq A n) → type-dependent-Coseq A B n a →
  type-dependent-Coseq C D n (map-hom-Coseq A C f n a)

Naturality-hom-dependent-Coseq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C)
  (f : hom-Coseq A C) (g : Map-hom-dependent-Coseq A B C D f) →
  UU (l1 ⊔ l2 ⊔ l4)
Naturality-hom-dependent-Coseq A B C D f g =
  (n : ℕ) (a : type-Coseq A (succ-ℕ n))
  (b : type-dependent-Coseq A B (succ-ℕ n) a) →
  Id ( tr ( type-dependent-Coseq C D n)
          ( naturality-map-hom-Coseq A C f n a)
          ( map-dependent-Coseq C D n
            ( map-hom-Coseq A C f (succ-ℕ n) a)
            ( g (succ-ℕ n) a b)))
     ( g n (map-Coseq A n a) (map-dependent-Coseq A B n a b))

hom-dependent-Coseq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C)
  (f : hom-Coseq A C) → UU (l1 ⊔ l2 ⊔ l4)
hom-dependent-Coseq A B C D f =
  Σ ( Map-hom-dependent-Coseq A B C D f)
    ( Naturality-hom-dependent-Coseq A B C D f)

map-hom-dependent-Coseq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C) (f : hom-Coseq A C) →
  hom-dependent-Coseq A B C D f → Map-hom-dependent-Coseq A B C D f
map-hom-dependent-Coseq A B C D f g = pr1 g

naturality-hom-dependent-Coseq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C) (f : hom-Coseq A C) →
  (g : hom-dependent-Coseq A B C D f) →
  Naturality-hom-dependent-Coseq A B C D f (map-hom-dependent-Coseq A B C D f g)
naturality-hom-dependent-Coseq A B C D f g = pr2 g

{- We characterize the identity type of hom-dependent-Coseq -}

Htpy-htpy-hom-dependent-Coseq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C) (f : hom-Coseq A C)
  (g h : hom-dependent-Coseq A B C D f) → UU (l1 ⊔ l2 ⊔ l4)
Htpy-htpy-hom-dependent-Coseq A B C D f g h =
  (n : ℕ) (a : type-Coseq A n) →
  map-hom-dependent-Coseq A B C D f g n a ~
  map-hom-dependent-Coseq A B C D f h n a

Naturality-htpy-hom-dependent-Coseq' :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C) (f : hom-Coseq A C)
  (g h : hom-dependent-Coseq A B C D f)
  (H : Htpy-htpy-hom-dependent-Coseq A B C D f g h) (n : ℕ)
  (a : type-Coseq A (succ-ℕ n)) (b : type-dependent-Coseq A B (succ-ℕ n) a) →
  UU l4
Naturality-htpy-hom-dependent-Coseq' A B C D f g h H n a b =
  Id ( ( ap ( tr ( type-dependent-Coseq C D n)
                 ( naturality-map-hom-Coseq A C f n a))
            ( ap ( map-dependent-Coseq C D n (map-hom-Coseq A C f (succ-ℕ n) a))
                 ( H (succ-ℕ n) a b))) ∙
       ( naturality-hom-dependent-Coseq A B C D f h n a b))
     ( ( naturality-hom-dependent-Coseq A B C D f g n a b) ∙
       ( H n (map-Coseq A n a) (map-dependent-Coseq A B n a b)))

Naturality-htpy-hom-dependent-Coseq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C) (f : hom-Coseq A C)
  (g h : hom-dependent-Coseq A B C D f)
  (H : Htpy-htpy-hom-dependent-Coseq A B C D f g h) → UU (l1 ⊔ l2 ⊔ l4)
Naturality-htpy-hom-dependent-Coseq A B C D f g h H =
  (n : ℕ) (a : type-Coseq A (succ-ℕ n))
  (b : type-dependent-Coseq A B (succ-ℕ n) a) →
  Naturality-htpy-hom-dependent-Coseq' A B C D f g h H n a b

htpy-hom-dependent-Coseq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C) (f : hom-Coseq A C) →
  (g h : hom-dependent-Coseq A B C D f) → UU (l1 ⊔ l2 ⊔ l4)
htpy-hom-dependent-Coseq A B C D f g h =
  Σ ( Htpy-htpy-hom-dependent-Coseq A B C D f g h)
    ( Naturality-htpy-hom-dependent-Coseq A B C D f g h)

refl-htpy-hom-dependent-Coseq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C) (f : hom-Coseq A C) →
  (g : hom-dependent-Coseq A B C D f) →
  htpy-hom-dependent-Coseq A B C D f g g
refl-htpy-hom-dependent-Coseq A B C D f g =
  pair (λ n a → refl-htpy) (λ n a b → inv right-unit)

htpy-hom-dependent-Coseq-eq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C) (f : hom-Coseq A C) →
  (g h : hom-dependent-Coseq A B C D f) → Id g h →
  htpy-hom-dependent-Coseq A B C D f g h
htpy-hom-dependent-Coseq-eq A B C D f g .g refl =
  refl-htpy-hom-dependent-Coseq A B C D f g

is-contr-total-htpy-hom-dependent-Coseq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C) (f : hom-Coseq A C)
  (g : hom-dependent-Coseq A B C D f) →
  is-contr
    ( Σ ( hom-dependent-Coseq A B C D f)
        ( htpy-hom-dependent-Coseq A B C D f g))
is-contr-total-htpy-hom-dependent-Coseq A B C D f g =
  is-contr-total-Eq-structure
    ( λ h H → Naturality-htpy-hom-dependent-Coseq A B C D f g (pair h H))
    ( is-contr-total-Eq-Π
      ( λ n h →
        ( a : type-Coseq A n) → map-hom-dependent-Coseq A B C D f g n a ~ h a)
      ( λ n →
        is-contr-total-Eq-Π
          ( λ a h → map-hom-dependent-Coseq A B C D f g n a ~ h)
          ( λ a →
            is-contr-total-htpy (map-hom-dependent-Coseq A B C D f g n a))))
    ( pair (map-hom-dependent-Coseq A B C D f g) (λ n a → refl-htpy))
    ( is-contr-total-Eq-Π
      ( λ n H →
        ( a : type-Coseq A (succ-ℕ n)) →
        ( b : type-dependent-Coseq A B (succ-ℕ n) a) →
        Id ( H a b)
           ( ( naturality-hom-dependent-Coseq A B C D f g n a b) ∙ refl))
      ( λ n →
        ( is-contr-total-Eq-Π
          ( λ a H →
            ( b : type-dependent-Coseq A B (succ-ℕ n) a) →
            Id ( H b)
               ( ( naturality-hom-dependent-Coseq A B C D f g n a b) ∙ refl))
          ( λ a →
            is-contr-total-htpy'
              ( λ b →
                ( naturality-hom-dependent-Coseq A B C D f g n a b) ∙ refl)))))

is-equiv-htpy-hom-dependent-Coseq-eq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C) (f : hom-Coseq A C)
  (g h : hom-dependent-Coseq A B C D f) →
  is-equiv (htpy-hom-dependent-Coseq-eq A B C D f g h)
is-equiv-htpy-hom-dependent-Coseq-eq A B C D f g =
  fundamental-theorem-id g
    ( refl-htpy-hom-dependent-Coseq A B C D f g)
    ( is-contr-total-htpy-hom-dependent-Coseq A B C D f g)
    ( htpy-hom-dependent-Coseq-eq A B C D f g)

{- We introduce dependent cones for dependent cosequences -}

constant-dependent-Coseq :
  {l1 l2 : Level} (X : UU l1) (Y : X → UU l2) →
  dependent-Coseq-UU l2 (constant-Coseq X)
constant-dependent-Coseq X Y =
  pair (λ n → Y) (λ n x → id)

cone-dependent-Coseq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (X : UU l2)
  (B : dependent-Coseq-UU l2 A) (Y : X → UU l4) →
  cone-Coseq A X → UU (l2 ⊔ l4)
cone-dependent-Coseq A X B Y c =
  hom-dependent-Coseq (constant-Coseq X) (constant-dependent-Coseq X Y) A B c

{- We introduce limiting cones of dependent cosequences -}

{- We define the canonical limit of a dependent cosequence -}

type-limit-dependent-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A) →
  limit-Coseq A → UU l2
type-limit-dependent-Coseq A B x =
  Σ ( ( n : ℕ) → type-dependent-Coseq A B n (point-limit-Coseq A x n))
    ( λ y →
      ( n : ℕ) → Id ( tr
                      ( type-dependent-Coseq A B n)
                      ( path-limit-Coseq A x n)
                      ( map-dependent-Coseq A B n
                        ( point-limit-Coseq A x (succ-ℕ n))
                        ( y (succ-ℕ n))))
                    ( y n) )

{- We introduce the total cosequence of a dependent cosequence -}

type-total-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A) →
  ℕ → UU (l1 ⊔ l2)
type-total-Coseq A B n =
  Σ (type-Coseq A n) (type-dependent-Coseq A B n)

map-total-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A) (n : ℕ) →
  type-total-Coseq A B (succ-ℕ n) → type-total-Coseq A B n
map-total-Coseq A B n =
  map-Σ
    ( type-dependent-Coseq A B n)
    ( map-Coseq A n)
    ( map-dependent-Coseq A B n)

total-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A) →
  Coseq-UU (l1 ⊔ l2)
total-Coseq A B =
  pair (type-total-Coseq A B) (map-total-Coseq A B)

{- We show that Σ preserves sequential limits -}
