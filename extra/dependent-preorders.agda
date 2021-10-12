{-# OPTIONS --without-K --exact-split #-}

module extra.dependent-preorders where

open import book public

--------------------------------------------------------------------------------

{- We define the type of preorders -}

PreOrd : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
PreOrd l1 l2 =
  Σ ( UU l1)
    ( λ A →
      Σ ( A → (A → UU-Prop l2))
        ( λ leq-A →
          ( {x : A} → type-Prop (leq-A x x)) ×
          ( {x y z : A} → type-Prop (leq-A y z) → type-Prop (leq-A x y) →
                          type-Prop (leq-A x z))))

construct-PreOrd :
  {l1 l2 : Level} (A : UU l1)
  (leq-A : A → A → UU-Prop l2)
  (r : {x : A} → type-Prop (leq-A x x))
  (t : {x y z : A} → type-Prop (leq-A y z) → type-Prop (leq-A x y) →
       type-Prop (leq-A x z)) →
  PreOrd l1 l2
construct-PreOrd A leq-A r t = pair A (pair leq-A (pair r t))

type-PreOrd :
  {l1 l2 : Level} → PreOrd l1 l2 → UU l1
type-PreOrd A = pr1 A

leq-PreOrd-Prop :
  {l1 l2 : Level} (A : PreOrd l1 l2) (x y : type-PreOrd A) → UU-Prop l2
leq-PreOrd-Prop A = pr1 (pr2 A)

leq-PreOrd :
  {l1 l2 : Level} (A : PreOrd l1 l2) (x y : type-PreOrd A) → UU l2
leq-PreOrd A x y = type-Prop (leq-PreOrd-Prop A x y)

is-prop-leq-PreOrd :
  {l1 l2 : Level} (A : PreOrd l1 l2) (x y : type-PreOrd A) →
  is-prop (leq-PreOrd A x y)
is-prop-leq-PreOrd A x y = is-prop-type-Prop (leq-PreOrd-Prop A x y)

refl-leq-PreOrd :
  {l1 l2 : Level} (A : PreOrd l1 l2) {x : type-PreOrd A} → leq-PreOrd A x x
refl-leq-PreOrd A = pr1 (pr2 (pr2 A))

transitive-leq-PreOrd :
  {l1 l2 : Level} (A : PreOrd l1 l2) {x y z : type-PreOrd A} →
  leq-PreOrd A y z → leq-PreOrd A x y → leq-PreOrd A x z
transitive-leq-PreOrd A = pr2 (pr2 (pr2 A))

--------------------------------------------------------------------------------

{- We define the type of dependent preorders -}

dependent-PreOrd :
  {l1 l2 : Level} (l3 l4 : Level) (A : PreOrd l1 l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
dependent-PreOrd l3 l4 A =
  Σ ( type-PreOrd A → UU l3)
    ( λ B →
      Σ ( {x y : type-PreOrd A} → leq-PreOrd A x y → B x → B y → UU-Prop l4)
        ( λ leq-B →
          ( { x : type-PreOrd A} {u : B x} →
            type-Prop (leq-B (refl-leq-PreOrd A) u u)) ×
          ( { x y z : type-PreOrd A} (q : leq-PreOrd A y z)
            ( p : leq-PreOrd A x y) {u : B x} {v : B y} {w : B z} →
            type-Prop (leq-B q v w) → type-Prop (leq-B p u v) →
            type-Prop (leq-B (transitive-leq-PreOrd A q p) u w ))))

type-dependent-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) → dependent-PreOrd l3 l4 A →
  type-PreOrd A → UU l3
type-dependent-PreOrd A B = pr1 B

leq-dependent-PreOrd-Prop :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A) →
  {x y : type-PreOrd A} → leq-PreOrd A x y → type-dependent-PreOrd A B x →
  type-dependent-PreOrd A B y → UU-Prop l4
leq-dependent-PreOrd-Prop A B = pr1 (pr2 B)

leq-dependent-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A) →
  {x y : type-PreOrd A} → leq-PreOrd A x y → type-dependent-PreOrd A B x →
  type-dependent-PreOrd A B y → UU l4
leq-dependent-PreOrd A B p u v = type-Prop (leq-dependent-PreOrd-Prop A B p u v)

is-prop-leq-dependent-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A) →
  {x y : type-PreOrd A} (p : leq-PreOrd A x y)
  (u : type-dependent-PreOrd A B x) (v : type-dependent-PreOrd A B y) →
  is-prop (leq-dependent-PreOrd A B p u v)
is-prop-leq-dependent-PreOrd A B p u v =
  is-prop-type-Prop (leq-dependent-PreOrd-Prop A B p u v)

refl-leq-dependent-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A) →
  {x : type-PreOrd A} {u : type-dependent-PreOrd A B x} →
  leq-dependent-PreOrd A B (refl-leq-PreOrd A) u u
refl-leq-dependent-PreOrd A B = pr1 (pr2 (pr2 B))

transitive-leq-dependent-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A) →
  {x y z : type-PreOrd A} (q : leq-PreOrd A y z) (p : leq-PreOrd A x y) →
  {u : type-dependent-PreOrd A B x} {v : type-dependent-PreOrd A B y}
  {w : type-dependent-PreOrd A B z} (β : leq-dependent-PreOrd A B q v w)
  (α : leq-dependent-PreOrd A B p u v) →
  leq-dependent-PreOrd A B (transitive-leq-PreOrd A q p) u w
transitive-leq-dependent-PreOrd A B = pr2 (pr2 (pr2 B))

--------------------------------------------------------------------------------

{- We define the fibers of dependent preorders -}

type-fiber-dependent-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A) →
  (a : type-PreOrd A) → UU l3
type-fiber-dependent-PreOrd A B a = type-dependent-PreOrd A B a

leq-fiber-dependent-PreOrd-Prop :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A) →
  {a : type-PreOrd A} →
  (u v : type-fiber-dependent-PreOrd A B a) → UU-Prop l4
leq-fiber-dependent-PreOrd-Prop A B {a} =
  leq-dependent-PreOrd-Prop A B (refl-leq-PreOrd A)

leq-fiber-dependent-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A) →
  {a : type-PreOrd A} → (u v : type-fiber-dependent-PreOrd A B a) → UU l4
leq-fiber-dependent-PreOrd A B u v =
  type-Prop (leq-fiber-dependent-PreOrd-Prop A B u v)

is-prop-leq-fiber-dependent-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A) →
  {a : type-PreOrd A} → (u v : type-fiber-dependent-PreOrd A B a) →
  is-prop (leq-fiber-dependent-PreOrd A B u v)
is-prop-leq-fiber-dependent-PreOrd A B u v =
  is-prop-type-Prop (leq-fiber-dependent-PreOrd-Prop A B u v)

refl-leq-fiber-dependent-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A) →
  {a : type-PreOrd A} {u : type-fiber-dependent-PreOrd A B a} →
  leq-fiber-dependent-PreOrd A B u u
refl-leq-fiber-dependent-PreOrd A B = refl-leq-dependent-PreOrd A B

transitive-leq-fiber-dependent-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A)
  {a : type-PreOrd A} {u v w : type-fiber-dependent-PreOrd A B a} →
  leq-fiber-dependent-PreOrd A B v w → leq-fiber-dependent-PreOrd A B u v →
  leq-fiber-dependent-PreOrd A B u w
transitive-leq-fiber-dependent-PreOrd A B {a} {u} {v} {w} β α =
  tr ( λ t → leq-dependent-PreOrd A B t u w)
     ( eq-is-prop (is-prop-leq-PreOrd A a a))
     ( transitive-leq-dependent-PreOrd A B
       ( refl-leq-PreOrd A)
       ( refl-leq-PreOrd A)
       ( β)
       ( α))

fiber-dependent-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A) →
  (a : type-PreOrd A) → PreOrd l3 l4
fiber-dependent-PreOrd A B a =
  construct-PreOrd
    ( type-fiber-dependent-PreOrd A B a)
    ( leq-fiber-dependent-PreOrd-Prop A B {a})
    ( refl-leq-fiber-dependent-PreOrd A B {a})
    ( transitive-leq-fiber-dependent-PreOrd A B {a})
  

--------------------------------------------------------------------------------

{- We define sections of dependent preorders -}

type-section-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
type-section-PreOrd A B =
  Σ ( (x : type-PreOrd A) → type-dependent-PreOrd A B x)
    ( λ f →
      {x y : type-PreOrd A} (p : leq-PreOrd A x y)→
      leq-dependent-PreOrd A B p (f x) (f y))

function-section-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A) →
  type-section-PreOrd A B → (x : type-PreOrd A) → type-dependent-PreOrd A B x
function-section-PreOrd A B f = pr1 f

is-order-preserving-function-section-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A) →
  (f : type-section-PreOrd A B) {x y : type-PreOrd A} (p : leq-PreOrd A x y) →
  leq-dependent-PreOrd A B p
    ( function-section-PreOrd A B f x)
    ( function-section-PreOrd A B f y)
is-order-preserving-function-section-PreOrd A B f = pr2 f

leq-section-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A) →
  (f g : type-section-PreOrd A B) → UU (l1 ⊔ l4)
leq-section-PreOrd A B f g =
  (x : type-PreOrd A) →
  leq-fiber-dependent-PreOrd A B
    ( function-section-PreOrd A B f x)
    ( function-section-PreOrd A B g x)

is-prop-leq-section-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A) →
  (f g : type-section-PreOrd A B) → is-prop (leq-section-PreOrd A B f g)
is-prop-leq-section-PreOrd A B f g =
  is-prop-Π
    ( λ x →
      is-prop-leq-fiber-dependent-PreOrd A B
      ( function-section-PreOrd A B f x)
      ( function-section-PreOrd A B g x))

leq-section-PreOrd-Prop :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A) →
  (f g : type-section-PreOrd A B) → UU-Prop (l1 ⊔ l4)
leq-section-PreOrd-Prop A B f g =
  pair (leq-section-PreOrd A B f g) (is-prop-leq-section-PreOrd A B f g)

refl-leq-section-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A) →
  {f : type-section-PreOrd A B} → leq-section-PreOrd A B f f
refl-leq-section-PreOrd A B x = refl-leq-fiber-dependent-PreOrd A B

transitive-leq-section-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A) →
  {f g h : type-section-PreOrd A B} → leq-section-PreOrd A B g h →
  leq-section-PreOrd A B f g → leq-section-PreOrd A B f h
transitive-leq-section-PreOrd A B q p x =
  transitive-leq-fiber-dependent-PreOrd A B (q x) (p x)

section-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A) →
  PreOrd (l1 ⊔ l2 ⊔ l3 ⊔ l4) (l1 ⊔ l4)
section-PreOrd A B =
  construct-PreOrd
    ( type-section-PreOrd A B)
    ( leq-section-PreOrd-Prop A B)
    ( λ {f} → refl-leq-section-PreOrd A B {f})
    ( λ {f} {g} {h} → transitive-leq-section-PreOrd A B {f} {g} {h})

--------------------------------------------------------------------------------

{- We characterize the identity type of section-PreOrd -}

htpy-section-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A) →
  (f g : type-section-PreOrd A B) → UU (l1 ⊔ l3)
htpy-section-PreOrd A B f g =
  function-section-PreOrd A B f ~ function-section-PreOrd A B g

refl-htpy-section-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A) →
  (f : type-section-PreOrd A B) → htpy-section-PreOrd A B f f
refl-htpy-section-PreOrd A B f = refl-htpy

htpy-eq-section-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A) →
  {f g : type-section-PreOrd A B} → Id f g → htpy-section-PreOrd A B f g
htpy-eq-section-PreOrd A B {f} refl = refl-htpy-section-PreOrd A B f

is-contr-total-htpy-section-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A) →
  (f : type-section-PreOrd A B) →
  is-contr (Σ (type-section-PreOrd A B) (htpy-section-PreOrd A B f))
is-contr-total-htpy-section-PreOrd A B f =
  is-contr-total-Eq-substructure
    ( is-contr-total-htpy (function-section-PreOrd A B f))
    ( λ g →
      is-prop-Π'
      ( λ x →
        is-prop-Π'
        ( λ y →
          is-prop-Π
          ( λ p → is-prop-leq-dependent-PreOrd A B p (g x) (g y)))))
    ( function-section-PreOrd A B f)
    ( refl-htpy)
    ( λ {x} {y} p → is-order-preserving-function-section-PreOrd A B f p)

is-equiv-htpy-eq-section-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A) →
  (f g : type-section-PreOrd A B) →
  is-equiv (htpy-eq-section-PreOrd A B {f} {g})
is-equiv-htpy-eq-section-PreOrd A B f =
  fundamental-theorem-id f
    ( refl-htpy-section-PreOrd A B f)
    ( is-contr-total-htpy-section-PreOrd A B f)
    ( λ g → htpy-eq-section-PreOrd A B {f} {g})

eq-htpy-section-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : dependent-PreOrd l3 l4 A) →
  {f g : type-section-PreOrd A B} → htpy-section-PreOrd A B f g → Id f g
eq-htpy-section-PreOrd A B {f} {g} =
  map-inv-is-equiv (is-equiv-htpy-eq-section-PreOrd A B f g)

--------------------------------------------------------------------------------

{- We define the category of preorders -}

construct-dependent-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) →
  ( B : (x : type-PreOrd A) → UU l3)
  ( leq-B :
    { x y : type-PreOrd A} (p : leq-PreOrd A x y) → B x → B y → UU-Prop l4)
  ( r :
    { x : type-PreOrd A} {u : B x} → type-Prop (leq-B (refl-leq-PreOrd A) u u))
  ( t :
    { x y z : type-PreOrd A} (q : leq-PreOrd A y z) (p : leq-PreOrd A x y) →
    { u : B x} {v : B y} {w : B z} →
    type-Prop (leq-B q v w) → type-Prop (leq-B p u v) →
    type-Prop (leq-B (transitive-leq-PreOrd A q p) u w)) →
  dependent-PreOrd l3 l4 A
construct-dependent-PreOrd A B leq-B r t =
  pair B (pair leq-B (pair r t))
  
weakening-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : PreOrd l3 l4) →
  dependent-PreOrd l3 l4 A
weakening-PreOrd A B =
  construct-dependent-PreOrd A
    ( λ x → type-PreOrd B)
    ( λ {x} {y} p → leq-PreOrd-Prop B)
    ( λ {x} → refl-leq-PreOrd B)
    ( λ {x} {y} {z} q p → transitive-leq-PreOrd B)

type-hom-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : PreOrd l3 l4) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
type-hom-PreOrd A B = type-section-PreOrd A (weakening-PreOrd A B)

map-hom-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : PreOrd l3 l4) →
  type-hom-PreOrd A B → type-PreOrd A → type-PreOrd B
map-hom-PreOrd A B f = function-section-PreOrd A (weakening-PreOrd A B) f

is-order-preserving-map-hom-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : PreOrd l3 l4)
  (f : type-hom-PreOrd A B) →
  {x y : type-PreOrd A} → leq-PreOrd A x y →
  leq-PreOrd B (map-hom-PreOrd A B f x) (map-hom-PreOrd A B f y)
is-order-preserving-map-hom-PreOrd A B f =
  is-order-preserving-function-section-PreOrd A (weakening-PreOrd A B) f

hom-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : PreOrd l3 l4) →
  PreOrd (l1 ⊔ l2 ⊔ l3 ⊔ l4) (l1 ⊔ l4)
hom-PreOrd A B = section-PreOrd A (weakening-PreOrd A B)

--------------------------------------------------------------------------------

{- We define substitutions of dependent preorders -}

type-subst-dependent-PreOrd :
  {l1 l2 l3 l4 l5 l6 : Level} (A : PreOrd l1 l2) (B : PreOrd l3 l4) →
  type-hom-PreOrd A B → dependent-PreOrd l5 l6 B →
  (x : type-PreOrd A) → UU l5
type-subst-dependent-PreOrd A B f C x =
  type-dependent-PreOrd B C (map-hom-PreOrd A B f x)

leq-subst-dependent-PreOrd-Prop :
  {l1 l2 l3 l4 l5 l6 : Level} (A : PreOrd l1 l2) (B : PreOrd l3 l4) →
  (f : type-hom-PreOrd A B) (C : dependent-PreOrd l5 l6 B) →
  {x y : type-PreOrd A} (p : leq-PreOrd A x y)
  (u : type-subst-dependent-PreOrd A B f C x)
  (v : type-subst-dependent-PreOrd A B f C y) → UU-Prop l6
leq-subst-dependent-PreOrd-Prop A B f C p =
  leq-dependent-PreOrd-Prop B C (is-order-preserving-map-hom-PreOrd A B f p)

leq-subst-dependent-PreOrd :
  {l1 l2 l3 l4 l5 l6 : Level} (A : PreOrd l1 l2) (B : PreOrd l3 l4) →
  (f : type-hom-PreOrd A B) (C : dependent-PreOrd l5 l6 B) →
  {x y : type-PreOrd A} (p : leq-PreOrd A x y)
  (u : type-subst-dependent-PreOrd A B f C x)
  (v : type-subst-dependent-PreOrd A B f C y) → UU l6
leq-subst-dependent-PreOrd A B f C p u v =
  type-Prop (leq-subst-dependent-PreOrd-Prop A B f C p u v)

abstract 
  refl-leq-subst-dependent-PreOrd :
    {l1 l2 l3 l4 l5 l6 : Level} (A : PreOrd l1 l2) (B : PreOrd l3 l4) →
    (f : type-hom-PreOrd A B) (C : dependent-PreOrd l5 l6 B) →
    {x : type-PreOrd A} {u : type-subst-dependent-PreOrd A B f C x} →
    leq-subst-dependent-PreOrd A B f C (refl-leq-PreOrd A) u u
  refl-leq-subst-dependent-PreOrd A B f C {x} {u} =
    tr ( λ t → leq-dependent-PreOrd B C t u u)
       ( eq-is-prop
         ( is-prop-leq-PreOrd B
           ( map-hom-PreOrd A B f x)
           ( map-hom-PreOrd A B f x)))
       ( refl-leq-dependent-PreOrd B C)

abstract
  transitive-leq-subst-dependent-PreOrd :
    {l1 l2 l3 l4 l5 l6 : Level} (A : PreOrd l1 l2) (B : PreOrd l3 l4) →
    (f : type-hom-PreOrd A B) (C : dependent-PreOrd l5 l6 B) →
    {x y z : type-PreOrd A} (q : leq-PreOrd A y z) (p : leq-PreOrd A x y)
    {u : type-subst-dependent-PreOrd A B f C x}
    {v : type-subst-dependent-PreOrd A B f C y}
    {w : type-subst-dependent-PreOrd A B f C z} →
    leq-subst-dependent-PreOrd A B f C q v w →
    leq-subst-dependent-PreOrd A B f C p u v →
    leq-subst-dependent-PreOrd A B f C
      (transitive-leq-PreOrd A q p) u w
  transitive-leq-subst-dependent-PreOrd
    A B f C {x} {y} {z} q p {u} {v} {w} β α =
    tr ( λ t → leq-dependent-PreOrd B C t u w)
       ( eq-is-prop
         ( is-prop-leq-PreOrd B
           ( map-hom-PreOrd A B f x)
           ( map-hom-PreOrd A B f z)))
       ( transitive-leq-dependent-PreOrd B C
         ( is-order-preserving-map-hom-PreOrd A B f q)
         ( is-order-preserving-map-hom-PreOrd A B f p)
         ( β)
         ( α))

subst-dependent-PreOrd :
  {l1 l2 l3 l4 l5 l6 : Level} (A : PreOrd l1 l2) (B : PreOrd l3 l4) →
  type-hom-PreOrd A B → dependent-PreOrd l5 l6 B → dependent-PreOrd l5 l6 A
subst-dependent-PreOrd A B f C =
  construct-dependent-PreOrd A
    ( type-subst-dependent-PreOrd A B f C)
    ( leq-subst-dependent-PreOrd-Prop A B f C)
    ( refl-leq-subst-dependent-PreOrd A B f C)
    ( transitive-leq-subst-dependent-PreOrd A B f C)

--------------------------------------------------------------------------------

function-precomp-section-PreOrd :
  {l1 l2 l3 l4 l5 l6 : Level} (A : PreOrd l1 l2) (B : PreOrd l3 l4) →
  (f : type-hom-PreOrd A B) (C : dependent-PreOrd l5 l6 B) →
  type-section-PreOrd B C →
  (x : type-PreOrd A) → type-subst-dependent-PreOrd A B f C x
function-precomp-section-PreOrd A B f C g x =
  function-section-PreOrd B C g (map-hom-PreOrd A B f x)

is-order-preserving-function-precomp-section-PreOrd :
  {l1 l2 l3 l4 l5 l6 : Level} (A : PreOrd l1 l2) (B : PreOrd l3 l4) →
  (f : type-hom-PreOrd A B) (C : dependent-PreOrd l5 l6 B) →
  (g : type-section-PreOrd B C) →
  {x y : type-PreOrd A} (p : leq-PreOrd A x y) →
  leq-subst-dependent-PreOrd A B f C p
    ( function-precomp-section-PreOrd A B f C g x)
    ( function-precomp-section-PreOrd A B f C g y)
is-order-preserving-function-precomp-section-PreOrd A B f C g p =
  is-order-preserving-function-section-PreOrd B C g
    ( is-order-preserving-map-hom-PreOrd A B f p)

precomp-section-PreOrd :
  {l1 l2 l3 l4 l5 l6 : Level} (A : PreOrd l1 l2) (B : PreOrd l3 l4) →
  (f : type-hom-PreOrd A B) (C : dependent-PreOrd l5 l6 B) →
  type-section-PreOrd B C →
  type-section-PreOrd A (subst-dependent-PreOrd A B f C)
precomp-section-PreOrd A B f C g =
  pair
    ( function-precomp-section-PreOrd A B f C g)
    ( is-order-preserving-function-precomp-section-PreOrd A B f C g)

--------------------------------------------------------------------------------

is-poset-PreOrd :
  {l1 l2 : Level} → PreOrd l1 l2 → UU (l1 ⊔ l2)
is-poset-PreOrd A =
  {x y : type-PreOrd A} → leq-PreOrd A x y → leq-PreOrd A y x → Id x y

is-poset-dependent-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) →
  dependent-PreOrd l3 l4 A → UU (l1 ⊔ l3 ⊔ l4)
is-poset-dependent-PreOrd A B =
  {x : type-PreOrd A} → is-poset-PreOrd (fiber-dependent-PreOrd A B x)

--------------------------------------------------------------------------------

type-op-PreOrd : {l1 l2 : Level} (A : PreOrd l1 l2) → UU l1
type-op-PreOrd A = type-PreOrd A

leq-op-PreOrd-Prop :
  {l1 l2 : Level} (A : PreOrd l1 l2) (x y : type-op-PreOrd A) → UU-Prop l2
leq-op-PreOrd-Prop A x y = leq-PreOrd-Prop A y x

leq-op-PreOrd :
  {l1 l2 : Level} (A : PreOrd l1 l2) (x y : type-op-PreOrd A) → UU l2
leq-op-PreOrd A x y = type-Prop (leq-op-PreOrd-Prop A x y)

refl-leq-op-PreOrd :
  {l1 l2 : Level} (A : PreOrd l1 l2) {x : type-op-PreOrd A} →
  leq-op-PreOrd A x x
refl-leq-op-PreOrd A = refl-leq-PreOrd A

transitive-leq-op-PreOrd :
  {l1 l2 : Level} (A : PreOrd l1 l2) {x y z : type-op-PreOrd A} →
  leq-op-PreOrd A y z → leq-op-PreOrd A x y → leq-op-PreOrd A x z
transitive-leq-op-PreOrd A q p = transitive-leq-PreOrd A p q

op-PreOrd :
  {l1 l2 : Level} → PreOrd l1 l2 → PreOrd l1 l2
op-PreOrd A =
  construct-PreOrd
    ( type-op-PreOrd A)
    ( leq-op-PreOrd-Prop A)
    ( refl-leq-op-PreOrd A)
    ( transitive-leq-op-PreOrd A)

--------------------------------------------------------------------------------

Prop-PreOrd : (l : Level) → PreOrd (lsuc l) l
Prop-PreOrd l =
  construct-PreOrd
    ( UU-Prop l)
    ( hom-Prop)
    ( λ {P} → id)
    ( λ {P} {Q} {R} g f → g ∘ f)

--------------------------------------------------------------------------------

map-yoneda-PreOrd :
  {l1 l2 : Level} (A : PreOrd l1 l2) →
  type-PreOrd A → type-hom-PreOrd (op-PreOrd A) (Prop-PreOrd l2)
map-yoneda-PreOrd A a =
  pair ( λ x → leq-PreOrd-Prop A x a)
       ( λ {x} {y} p q → transitive-leq-PreOrd A q p)

yoneda-PreOrd :
  {l1 l2 : Level} (A : PreOrd l1 l2) →
  type-hom-PreOrd A (hom-PreOrd (op-PreOrd A) (Prop-PreOrd l2))
yoneda-PreOrd A =
  pair
    ( map-yoneda-PreOrd A)
    ( λ {a} {b} p x q → transitive-leq-PreOrd A p q)

type-poset-reflection-PreOrd :
  {l1 l2 : Level} (A : PreOrd l1 l2) → UU (l1 ⊔ lsuc l2)
type-poset-reflection-PreOrd A = im (map-yoneda-PreOrd A)

--------------------------------------------------------------------------------

{- We construct the image of an order preserving map as a preorder -}

type-im-hom-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : PreOrd l3 l4)
  (f : type-hom-PreOrd A B) → UU (l1 ⊔ l3)
type-im-hom-PreOrd A B f = im (map-hom-PreOrd A B f)

leq-im-hom-PreOrd-Prop :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : PreOrd l3 l4)
  (f : type-hom-PreOrd A B) →
  (x y : type-im-hom-PreOrd A B f) → UU-Prop l4
leq-im-hom-PreOrd-Prop A B f x y =
  leq-PreOrd-Prop B ( inclusion-im (map-hom-PreOrd A B f) x)
                    ( inclusion-im (map-hom-PreOrd A B f) y)

leq-im-hom-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : PreOrd l3 l4)
  (f : type-hom-PreOrd A B) →
  (x y : type-im-hom-PreOrd A B f) → UU l4
leq-im-hom-PreOrd A B f x y = type-Prop (leq-im-hom-PreOrd-Prop A B f x y)

is-prop-leq-im-hom-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : PreOrd l3 l4)
  (f : type-hom-PreOrd A B) (x y : type-im-hom-PreOrd A B f) →
  is-prop (leq-im-hom-PreOrd A B f x y)
is-prop-leq-im-hom-PreOrd A B f x y =
  is-prop-type-Prop (leq-im-hom-PreOrd-Prop A B f x y)

refl-leq-im-hom-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : PreOrd l3 l4)
  (f : type-hom-PreOrd A B) {x : type-im-hom-PreOrd A B f} →
  leq-im-hom-PreOrd A B f x x
refl-leq-im-hom-PreOrd A B f = refl-leq-PreOrd B

transitive-leq-im-hom-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : PreOrd l3 l4)
  (f : type-hom-PreOrd A B) {x y z : type-im-hom-PreOrd A B f} →
  leq-im-hom-PreOrd A B f y z → leq-im-hom-PreOrd A B f x y →
  leq-im-hom-PreOrd A B f x z
transitive-leq-im-hom-PreOrd A B f q p = transitive-leq-PreOrd B q p

im-hom-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : PreOrd l3 l4)
  (f : type-hom-PreOrd A B) → PreOrd (l1 ⊔ l3) l4
im-hom-PreOrd A B f =
  construct-PreOrd
    ( type-im-hom-PreOrd A B f)
    ( leq-im-hom-PreOrd-Prop A B f)
    ( λ {x} → refl-leq-im-hom-PreOrd A B f {x})
    ( λ {x} {y} {z} → transitive-leq-im-hom-PreOrd A B f {x} {y} {z})

map-inclusion-im-hom-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : PreOrd l3 l4)
  (f : type-hom-PreOrd A B) → type-im-hom-PreOrd A B f → type-PreOrd B
map-inclusion-im-hom-PreOrd A B f = inclusion-im (map-hom-PreOrd A B f)

is-order-preserving-map-inclusion-im-hom-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : PreOrd l3 l4)
  (f : type-hom-PreOrd A B)
  {x y : type-im-hom-PreOrd A B f} (p : leq-im-hom-PreOrd A B f x y) →
  leq-PreOrd B ( map-inclusion-im-hom-PreOrd A B f x)
               ( map-inclusion-im-hom-PreOrd A B f y)
is-order-preserving-map-inclusion-im-hom-PreOrd A B f p = p

inclusion-im-hom-PreOrd :
  {l1 l2 l3 l4 : Level} (A : PreOrd l1 l2) (B : PreOrd l3 l4)
  (f : type-hom-PreOrd A B) → type-hom-PreOrd (im-hom-PreOrd A B f) B
inclusion-im-hom-PreOrd A B f =
  pair ( map-inclusion-im-hom-PreOrd A B f)
       ( λ {x} {y} →
         is-order-preserving-map-inclusion-im-hom-PreOrd A B f {x} {y})
