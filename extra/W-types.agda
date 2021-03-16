{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module extra.W-types where

import book
open book public

--------------------------------------------------------------------------------

-- Appendix B W-types

--------------------------------------------------------------------------------

-- Section B.1 W-types

data 𝕎 {l1 l2 : Level} (A : UU l1) (B : A → UU l2) : UU (l1 ⊔ l2) where
  collect-𝕎 : (x : A) (α : B x → 𝕎 A B) → 𝕎 A B

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where
  
  arity-𝕎 : 𝕎 A B → A
  arity-𝕎 (collect-𝕎 x α) = x
  
  component-𝕎 : (x : 𝕎 A B) → B (arity-𝕎 x) → 𝕎 A B
  component-𝕎 (collect-𝕎 x α) = α

  η-𝕎 : (x : 𝕎 A B) → Id (collect-𝕎 (arity-𝕎 x) (component-𝕎 x)) x
  η-𝕎 (collect-𝕎 x α) = refl

-- Example B.1.3

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  constant-𝕎 : (x : A) → is-empty (B x) → 𝕎 A B
  constant-𝕎 x h = collect-𝕎 x (ex-falso ∘ h)

  is-constant-𝕎 : 𝕎 A B → UU l2
  is-constant-𝕎 x = is-empty (B (arity-𝕎 x))

-- Proposition B.1.4

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-empty-𝕎 : ((x : A) → type-trunc-Prop (B x)) → is-empty (𝕎 A B)
  is-empty-𝕎 H (collect-𝕎 x α) =
    apply-universal-property-trunc-Prop
      ( H x)
      ( empty-Prop)
      ( λ y → is-empty-𝕎 H (α y))

-- Example B.1.5

Nat-𝕎 : UU lzero
Nat-𝕎 = 𝕎 bool (Eq-𝟚 true)

zero-Nat-𝕎 : Nat-𝕎
zero-Nat-𝕎 = constant-𝕎 false id

succ-Nat-𝕎 : Nat-𝕎 → Nat-𝕎
succ-Nat-𝕎 x = collect-𝕎 true (λ y → x)

Nat-𝕎-ℕ : ℕ → Nat-𝕎
Nat-𝕎-ℕ zero-ℕ = zero-Nat-𝕎
Nat-𝕎-ℕ (succ-ℕ x) = succ-Nat-𝕎 (Nat-𝕎-ℕ x)

ℕ-Nat-𝕎 : Nat-𝕎 → ℕ
ℕ-Nat-𝕎 (collect-𝕎 true α) = succ-ℕ (ℕ-Nat-𝕎 (α star))
ℕ-Nat-𝕎 (collect-𝕎 false α) = zero-ℕ

issec-ℕ-Nat-𝕎 : (Nat-𝕎-ℕ ∘ ℕ-Nat-𝕎) ~ id
issec-ℕ-Nat-𝕎 (collect-𝕎 true α) =
  ap ( collect-𝕎 true)
     ( eq-htpy H)
  where
  H : (z : unit) → Id (Nat-𝕎-ℕ (ℕ-Nat-𝕎 (α star))) (α z)
  H star = issec-ℕ-Nat-𝕎 (α star)
issec-ℕ-Nat-𝕎 (collect-𝕎 false α) =
  ap (collect-𝕎 false) (eq-is-contr (universal-property-empty' Nat-𝕎))

isretr-ℕ-Nat-𝕎 : (ℕ-Nat-𝕎 ∘ Nat-𝕎-ℕ) ~ id
isretr-ℕ-Nat-𝕎 zero-ℕ = refl
isretr-ℕ-Nat-𝕎 (succ-ℕ x) = ap succ-ℕ (isretr-ℕ-Nat-𝕎 x)

is-equiv-Nat-𝕎-ℕ : is-equiv Nat-𝕎-ℕ
is-equiv-Nat-𝕎-ℕ =
  is-equiv-has-inverse
    ℕ-Nat-𝕎
    issec-ℕ-Nat-𝕎
    isretr-ℕ-Nat-𝕎

equiv-Nat-𝕎-ℕ : ℕ ≃ Nat-𝕎
equiv-Nat-𝕎-ℕ = pair Nat-𝕎-ℕ is-equiv-Nat-𝕎-ℕ

is-equiv-ℕ-Nat-𝕎 : is-equiv ℕ-Nat-𝕎
is-equiv-ℕ-Nat-𝕎 =
  is-equiv-has-inverse
    Nat-𝕎-ℕ
    isretr-ℕ-Nat-𝕎
    issec-ℕ-Nat-𝕎

equiv-ℕ-Nat-𝕎 : Nat-𝕎 ≃ ℕ
equiv-ℕ-Nat-𝕎 = pair ℕ-Nat-𝕎 is-equiv-ℕ-Nat-𝕎

-- Example B.1.6

data Planar-Bin-Tree : UU lzero where
  root-PBT : Planar-Bin-Tree
  join-PBT : (x y : Planar-Bin-Tree) → Planar-Bin-Tree

PBT-𝕎 : UU lzero
PBT-𝕎 = 𝕎 bool P
  where
  P : bool → UU lzero
  P true = bool
  P false = empty

root-PBT-𝕎 : PBT-𝕎
root-PBT-𝕎 = constant-𝕎 false id

join-PBT-𝕎 : (x y : PBT-𝕎) → PBT-𝕎
join-PBT-𝕎 x y = collect-𝕎 true α
  where
  α : bool → PBT-𝕎
  α true = x
  α false = y

{-
Planar-Bin-Tree-PBT-𝕎 : PBT-𝕎 → Planar-Bin-Tree
Planar-Bin-Tree-PBT-𝕎 (collect-𝕎 true α) =
  join-PBT
    ( Planar-Bin-Tree-PBT-𝕎 (α true))
    ( Planar-Bin-Tree-PBT-𝕎 (α false))
Planar-Bin-Tree-PBT-𝕎 (collect-𝕎 false α) = {!!}
-}

--------------------------------------------------------------------------------

-- Section B.2 Observational equality of W-types

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where
  
  Eq-𝕎 : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  Eq-𝕎 (collect-𝕎 x α) (collect-𝕎 y β) =
    Σ (Id x y) (λ p → (z : B x) → Eq-𝕎 (α z) (β (tr B p z))) 

  refl-Eq-𝕎 : (w : 𝕎 A B) → Eq-𝕎 w w
  refl-Eq-𝕎 (collect-𝕎 x α) = pair refl (λ z → refl-Eq-𝕎 (α z))

  center-total-Eq-𝕎 : (w : 𝕎 A B) → Σ (𝕎 A B) (Eq-𝕎 w)
  center-total-Eq-𝕎 w = pair w (refl-Eq-𝕎 w)

  aux-total-Eq-𝕎 :
    (x : A) (α : B x → 𝕎 A B) →
    Σ (B x → 𝕎 A B) (λ β → (y : B x) → Eq-𝕎 (α y) (β y)) →
    Σ (𝕎 A B) (Eq-𝕎 (collect-𝕎 x α))
  aux-total-Eq-𝕎 x α (pair β e) = pair (collect-𝕎 x β) (pair refl e)

  contraction-total-Eq-𝕎 :
    (w : 𝕎 A B) (t : Σ (𝕎 A B) (Eq-𝕎 w)) → Id (center-total-Eq-𝕎 w) t
  contraction-total-Eq-𝕎
    ( collect-𝕎 x α) (pair (collect-𝕎 .x β) (pair refl e)) =
    ap ( ( aux-total-Eq-𝕎 x α) ∘
         ( choice-∞ {A = B x} {B = λ y → 𝕎 A B} {C = λ y → Eq-𝕎 (α y)}))
       { x = λ y → pair (α y) (refl-Eq-𝕎 (α y))}
       { y = λ y → pair (β y) (e y)}
       ( eq-htpy (λ y → contraction-total-Eq-𝕎 (α y) (pair (β y) (e y))))

  is-contr-total-Eq-𝕎 : (w : 𝕎 A B) → is-contr (Σ (𝕎 A B) (Eq-𝕎 w))
  is-contr-total-Eq-𝕎 w =
    pair (center-total-Eq-𝕎 w) (contraction-total-Eq-𝕎 w)

  Eq-𝕎-eq : (v w : 𝕎 A B) → Id v w → Eq-𝕎 v w
  Eq-𝕎-eq v .v refl = refl-Eq-𝕎 v

  is-equiv-Eq-𝕎-eq : (v w : 𝕎 A B) → is-equiv (Eq-𝕎-eq v w)
  is-equiv-Eq-𝕎-eq v =
    fundamental-theorem-id v
      ( refl-Eq-𝕎 v)
      ( is-contr-total-Eq-𝕎 v)
      ( Eq-𝕎-eq v)

  equiv-Eq-𝕎-eq : (v w : 𝕎 A B) → Id v w ≃ Eq-𝕎 v w
  equiv-Eq-𝕎-eq v w = pair (Eq-𝕎-eq v w) (is-equiv-Eq-𝕎-eq v w)
  
  is-trunc-𝕎 : (k : 𝕋) → is-trunc (succ-𝕋 k) A → is-trunc (succ-𝕋 k) (𝕎 A B)
  is-trunc-𝕎 k is-trunc-A (collect-𝕎 x α) (collect-𝕎 y β) =
    is-trunc-is-equiv k
      ( Eq-𝕎 (collect-𝕎 x α) (collect-𝕎 y β))
      ( Eq-𝕎-eq (collect-𝕎 x α) (collect-𝕎 y β))
      ( is-equiv-Eq-𝕎-eq (collect-𝕎 x α) (collect-𝕎 y β))
      ( is-trunc-Σ k
        ( is-trunc-A x y)
        ( λ p → is-trunc-Π k
          ( λ z →
            is-trunc-is-equiv' k
            ( Id (α z) (β (tr B p z)))
            ( Eq-𝕎-eq (α z) (β (tr B p z)))
            ( is-equiv-Eq-𝕎-eq (α z) (β (tr B p z)))
            ( is-trunc-𝕎 k is-trunc-A (α z) (β (tr B p z))))))
  
--------------------------------------------------------------------------------
  
-- Section B.3 W-types as initial algebras

-- The polynomial endofunctor associated to a container
                                              
type-polynomial-endofunctor :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (X : UU l3) →
  UU (l1 ⊔ l2 ⊔ l3)
type-polynomial-endofunctor A B X = Σ A (λ x → B x → X)

-- We characterize the identity type of type-polynomial-endofunctor

Eq-type-polynomial-endofunctor :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {X : UU l3} →
  (x y : type-polynomial-endofunctor A B X) → UU (l1 ⊔ l2 ⊔ l3)
Eq-type-polynomial-endofunctor {B = B} x y =
  Σ (Id (pr1 x) (pr1 y)) (λ p → (pr2 x) ~ ((pr2 y) ∘ (tr B p)))

refl-Eq-type-polynomial-endofunctor :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {X : UU l3} →
  (x : type-polynomial-endofunctor A B X) →
  Eq-type-polynomial-endofunctor x x
refl-Eq-type-polynomial-endofunctor (pair x α) = pair refl refl-htpy

is-contr-total-Eq-type-polynomial-endofunctor :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {X : UU l3} →
  (x : type-polynomial-endofunctor A B X) →
  is-contr
    ( Σ ( type-polynomial-endofunctor A B X)
        ( Eq-type-polynomial-endofunctor x))
is-contr-total-Eq-type-polynomial-endofunctor {A = A} {B} {X} (pair x α) =
  is-contr-total-Eq-structure
    ( ( λ (y : A) (β : B y → X) (p : Id x y) → α ~ (β ∘ tr B p)))
    ( is-contr-total-path x)
    ( pair x refl)
    ( is-contr-total-htpy α)

Eq-type-polynomial-endofunctor-eq :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {X : UU l3} →
  (x y : type-polynomial-endofunctor A B X) →
  Id x y → Eq-type-polynomial-endofunctor x y
Eq-type-polynomial-endofunctor-eq x .x refl =
  refl-Eq-type-polynomial-endofunctor x

is-equiv-Eq-type-polynomial-endofunctor-eq :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {X : UU l3} →
  (x y : type-polynomial-endofunctor A B X) →
  is-equiv (Eq-type-polynomial-endofunctor-eq x y)
is-equiv-Eq-type-polynomial-endofunctor-eq x =
  fundamental-theorem-id x
    ( refl-Eq-type-polynomial-endofunctor x)
    ( is-contr-total-Eq-type-polynomial-endofunctor x)
    ( Eq-type-polynomial-endofunctor-eq x)

eq-Eq-type-polynomial-endofunctor :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {X : UU l3} →
  (x y : type-polynomial-endofunctor A B X) →
  Eq-type-polynomial-endofunctor x y → Id x y
eq-Eq-type-polynomial-endofunctor x y =
  map-inv-is-equiv (is-equiv-Eq-type-polynomial-endofunctor-eq x y)

isretr-eq-Eq-type-polynomial-endofunctor :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {X : UU l3} →
  (x y : type-polynomial-endofunctor A B X) →
  ( ( eq-Eq-type-polynomial-endofunctor x y) ∘
    ( Eq-type-polynomial-endofunctor-eq x y)) ~ id
isretr-eq-Eq-type-polynomial-endofunctor x y =
  isretr-map-inv-is-equiv (is-equiv-Eq-type-polynomial-endofunctor-eq x y)

coh-refl-eq-Eq-type-polynomial-endofunctor :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {X : UU l3} →
  (x : type-polynomial-endofunctor A B X) →
  Id ( eq-Eq-type-polynomial-endofunctor x x
       ( refl-Eq-type-polynomial-endofunctor x)) refl
coh-refl-eq-Eq-type-polynomial-endofunctor x =
  isretr-eq-Eq-type-polynomial-endofunctor x x refl
  
--------------------------------------------------------------------------------

-- The action on morphisms of the polynomial endofunctor

map-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2) {X : UU l3} {Y : UU l4}
  (f : X → Y) →
  type-polynomial-endofunctor A B X → type-polynomial-endofunctor A B Y
map-polynomial-endofunctor A B f = tot (λ x α → f ∘ α)

-- The action on homotopies of the polynomial endofunctor

htpy-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2) {X : UU l3} {Y : UU l4}
  {f g : X → Y} →
  f ~ g → map-polynomial-endofunctor A B f ~ map-polynomial-endofunctor A B g
htpy-polynomial-endofunctor A B {X = X} {Y} {f} {g} H (pair x α) =
  eq-Eq-type-polynomial-endofunctor
    ( map-polynomial-endofunctor A B f (pair x α))
    ( map-polynomial-endofunctor A B g (pair x α))
    ( pair refl (H ·r α))

coh-refl-htpy-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2) {X : UU l3} {Y : UU l4}
  (f : X → Y) →
  htpy-polynomial-endofunctor A B (refl-htpy {f = f}) ~ refl-htpy
coh-refl-htpy-polynomial-endofunctor A B {X = X} {Y} f (pair x α) =
  coh-refl-eq-Eq-type-polynomial-endofunctor
    ( map-polynomial-endofunctor A B f (pair x α)) 
                                           
-- algebras for the polynomial endofunctors

algebra-polynomial-endofunctor-UU :
  (l : Level) {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  UU (lsuc l ⊔ l1 ⊔ l2)
algebra-polynomial-endofunctor-UU l A B =
  Σ (UU l) (λ X → type-polynomial-endofunctor A B X → X)
                                                  
type-algebra-polynomial-endofunctor :
  {l l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  algebra-polynomial-endofunctor-UU l A B → UU l
type-algebra-polynomial-endofunctor X = pr1 X
                                            
structure-algebra-polynomial-endofunctor :
  {l l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l A B) →
  type-polynomial-endofunctor A B (type-algebra-polynomial-endofunctor X) →
  type-algebra-polynomial-endofunctor X
structure-algebra-polynomial-endofunctor X = pr2 X

-- W-types are algebras for polynomial endofunctors

structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  type-polynomial-endofunctor A B (𝕎 A B) → 𝕎 A B
structure-𝕎-Alg (pair x α) = collect-𝕎 x α

𝕎-Alg :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  algebra-polynomial-endofunctor-UU (l1 ⊔ l2) A B
𝕎-Alg A B = pair (𝕎 A B) structure-𝕎-Alg

map-inv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  𝕎 A B → type-polynomial-endofunctor A B (𝕎 A B)
map-inv-structure-𝕎-Alg (collect-𝕎 x α) = pair x α

issec-map-inv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (structure-𝕎-Alg {B = B} ∘ map-inv-structure-𝕎-Alg {B = B}) ~ id
issec-map-inv-structure-𝕎-Alg (collect-𝕎 x α) = refl

isretr-map-inv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (map-inv-structure-𝕎-Alg {B = B} ∘ structure-𝕎-Alg {B = B}) ~ id
isretr-map-inv-structure-𝕎-Alg (pair x α) = refl

is-equiv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-equiv (structure-𝕎-Alg {B = B})
is-equiv-structure-𝕎-Alg =
  is-equiv-has-inverse
    map-inv-structure-𝕎-Alg
    issec-map-inv-structure-𝕎-Alg
    isretr-map-inv-structure-𝕎-Alg

equiv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  type-polynomial-endofunctor A B (𝕎 A B) ≃ 𝕎 A B
equiv-structure-𝕎-Alg =
  pair structure-𝕎-Alg is-equiv-structure-𝕎-Alg

is-equiv-map-inv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-equiv (map-inv-structure-𝕎-Alg {B = B})
is-equiv-map-inv-structure-𝕎-Alg =
  is-equiv-has-inverse
    structure-𝕎-Alg
    isretr-map-inv-structure-𝕎-Alg
    issec-map-inv-structure-𝕎-Alg

inv-equiv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  𝕎 A B ≃ type-polynomial-endofunctor A B (𝕎 A B)
inv-equiv-structure-𝕎-Alg =
  pair map-inv-structure-𝕎-Alg is-equiv-map-inv-structure-𝕎-Alg

-- Morphisms of algebras for polynomial endofunctors
  
hom-algebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B) →
  (Y : algebra-polynomial-endofunctor-UU l4 A B) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
hom-algebra-polynomial-endofunctor {A = A} {B} X Y =
  Σ ( type-algebra-polynomial-endofunctor X →
      type-algebra-polynomial-endofunctor Y)
    ( λ f →
      ( f ∘ (structure-algebra-polynomial-endofunctor X)) ~
      ( ( structure-algebra-polynomial-endofunctor Y) ∘
        ( map-polynomial-endofunctor A B f)))

map-hom-algebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B) →
  (Y : algebra-polynomial-endofunctor-UU l4 A B) →
  hom-algebra-polynomial-endofunctor X Y →
  type-algebra-polynomial-endofunctor X →
  type-algebra-polynomial-endofunctor Y
map-hom-algebra-polynomial-endofunctor X Y f = pr1 f

structure-hom-algebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B) →
  (Y : algebra-polynomial-endofunctor-UU l4 A B) →
  (f : hom-algebra-polynomial-endofunctor X Y) →
  ( ( map-hom-algebra-polynomial-endofunctor X Y f) ∘
    ( structure-algebra-polynomial-endofunctor X)) ~
  ( ( structure-algebra-polynomial-endofunctor Y) ∘
    ( map-polynomial-endofunctor A B
      ( map-hom-algebra-polynomial-endofunctor X Y f)))
structure-hom-algebra-polynomial-endofunctor X Y f = pr2 f

--------------------------------------------------------------------------------

-- We characterize the identity type of the type of morphisms of algebras
                                                                 
htpy-hom-algebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B)
  (Y : algebra-polynomial-endofunctor-UU l4 A B)
  (f : hom-algebra-polynomial-endofunctor X Y)
  (g : hom-algebra-polynomial-endofunctor X Y) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
htpy-hom-algebra-polynomial-endofunctor {A = A} {B} X Y f g =
  Σ ( map-hom-algebra-polynomial-endofunctor X Y f ~
      map-hom-algebra-polynomial-endofunctor X Y g)
    ( λ H →
      ( ( structure-hom-algebra-polynomial-endofunctor X Y f) ∙h
        ( ( structure-algebra-polynomial-endofunctor Y) ·l
          ( htpy-polynomial-endofunctor A B H))) ~
      ( ( H ·r structure-algebra-polynomial-endofunctor X) ∙h
        ( structure-hom-algebra-polynomial-endofunctor X Y g)))

refl-htpy-hom-algebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B)
  (Y : algebra-polynomial-endofunctor-UU l4 A B)
  (f : hom-algebra-polynomial-endofunctor X Y) →
  htpy-hom-algebra-polynomial-endofunctor X Y f f
refl-htpy-hom-algebra-polynomial-endofunctor {A = A} {B} X Y f =
  pair refl-htpy
    ( λ z →
      ( ap ( λ t →
             concat
               ( structure-hom-algebra-polynomial-endofunctor X Y f z)
               ( structure-algebra-polynomial-endofunctor Y
                 ( map-polynomial-endofunctor A B
                   ( map-hom-algebra-polynomial-endofunctor X Y f) z) )
               ( ap (structure-algebra-polynomial-endofunctor Y ) t))
           ( coh-refl-htpy-polynomial-endofunctor A B
             ( map-hom-algebra-polynomial-endofunctor X Y f) z)) ∙
      ( right-unit))
  
htpy-hom-algebra-polynomial-endofunctor-eq :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B)
  (Y : algebra-polynomial-endofunctor-UU l4 A B)
  (f : hom-algebra-polynomial-endofunctor X Y) →
  (g : hom-algebra-polynomial-endofunctor X Y) →
  Id f g → htpy-hom-algebra-polynomial-endofunctor X Y f g
htpy-hom-algebra-polynomial-endofunctor-eq X Y f .f refl =
  refl-htpy-hom-algebra-polynomial-endofunctor X Y f

is-contr-total-htpy-hom-algebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B)
  (Y : algebra-polynomial-endofunctor-UU l4 A B)
  (f : hom-algebra-polynomial-endofunctor X Y) →
  is-contr
    ( Σ ( hom-algebra-polynomial-endofunctor X Y)
        ( htpy-hom-algebra-polynomial-endofunctor X Y f))
is-contr-total-htpy-hom-algebra-polynomial-endofunctor {A = A} {B} X Y f =
  is-contr-total-Eq-structure
    ( λ ( g : pr1 X → pr1 Y)
        ( G : (g ∘ pr2 X) ~ ((pr2 Y) ∘ (map-polynomial-endofunctor A B g)))
        ( H : map-hom-algebra-polynomial-endofunctor X Y f ~ g) →
        ( ( structure-hom-algebra-polynomial-endofunctor X Y f) ∙h
          ( ( structure-algebra-polynomial-endofunctor Y) ·l
            ( htpy-polynomial-endofunctor A B H))) ~
        ( ( H ·r structure-algebra-polynomial-endofunctor X) ∙h G))
    ( is-contr-total-htpy (map-hom-algebra-polynomial-endofunctor X Y f))
    ( pair (map-hom-algebra-polynomial-endofunctor X Y f) refl-htpy)
    ( is-contr-equiv'
      ( Σ ( ( (pr1 f) ∘ pr2 X) ~
            ( pr2 Y ∘ map-polynomial-endofunctor A B (pr1 f)))
          ( λ H → (pr2 f) ~ H))
      ( equiv-tot
        ( λ H →
          ( equiv-concat-htpy
            ( λ x →
              ap ( concat
                   ( pr2 f x)
                   ( structure-algebra-polynomial-endofunctor Y
                     ( map-polynomial-endofunctor A B (pr1 f) x)))
                 ( ap ( ap (pr2 Y))
                      ( coh-refl-htpy-polynomial-endofunctor A B (pr1 f) x)))
            ( H)) ∘e
          ( equiv-concat-htpy right-unit-htpy H)))
      ( is-contr-total-htpy (pr2 f)))

is-equiv-htpy-hom-algebra-polynomial-endofunctor-eq :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B)
  (Y : algebra-polynomial-endofunctor-UU l4 A B)
  (f : hom-algebra-polynomial-endofunctor X Y) →
  (g : hom-algebra-polynomial-endofunctor X Y) →
  is-equiv (htpy-hom-algebra-polynomial-endofunctor-eq X Y f g)
is-equiv-htpy-hom-algebra-polynomial-endofunctor-eq X Y f =
  fundamental-theorem-id f
    ( refl-htpy-hom-algebra-polynomial-endofunctor X Y f)
    ( is-contr-total-htpy-hom-algebra-polynomial-endofunctor X Y f)
    ( htpy-hom-algebra-polynomial-endofunctor-eq X Y f)
        
eq-htpy-hom-algebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B)
  (Y : algebra-polynomial-endofunctor-UU l4 A B)
  (f : hom-algebra-polynomial-endofunctor X Y) →
  (g : hom-algebra-polynomial-endofunctor X Y) →
  htpy-hom-algebra-polynomial-endofunctor X Y f g → Id f g
eq-htpy-hom-algebra-polynomial-endofunctor X Y f g =
  map-inv-is-equiv (is-equiv-htpy-hom-algebra-polynomial-endofunctor-eq X Y f g)
                                                                          
--------------------------------------------------------------------------------

-- We show that 𝕎 A B is an initial algebra
  
map-hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B) →
  𝕎 A B → type-algebra-polynomial-endofunctor X
map-hom-𝕎-Alg X (collect-𝕎 x α) =
  structure-algebra-polynomial-endofunctor X (pair x (map-hom-𝕎-Alg X ∘ α))

structure-hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B) →
  ( (map-hom-𝕎-Alg X) ∘ structure-𝕎-Alg) ~
  ( ( structure-algebra-polynomial-endofunctor X) ∘
    ( map-polynomial-endofunctor A B (map-hom-𝕎-Alg X)))
structure-hom-𝕎-Alg X (pair x α) = refl

hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B) →
  hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X
hom-𝕎-Alg X = pair (map-hom-𝕎-Alg X) (structure-hom-𝕎-Alg X)

htpy-htpy-hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B) →
  (f : hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X) →
  map-hom-𝕎-Alg X ~
  map-hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X f
htpy-htpy-hom-𝕎-Alg {A = A} {B} X f (collect-𝕎 x α) =
  ( ap ( λ t → structure-algebra-polynomial-endofunctor X (pair x t))
       ( eq-htpy (λ z → htpy-htpy-hom-𝕎-Alg X f (α z)))) ∙
  ( inv
    ( structure-hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X f
      ( pair x α)))
                 
compute-structure-htpy-hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B) (x : A) (α : B x → 𝕎 A B)
  {f : 𝕎 A B → type-algebra-polynomial-endofunctor X} →
  (H : map-hom-𝕎-Alg X ~ f) →
  Id ( ap ( structure-algebra-polynomial-endofunctor X)
          ( htpy-polynomial-endofunctor A B H (pair x α)))
     ( ap ( λ t → structure-algebra-polynomial-endofunctor X (pair x t))
          ( eq-htpy (H ·r α)))
compute-structure-htpy-hom-𝕎-Alg {A = A} {B} X x α = 
  ind-htpy
    ( map-hom-𝕎-Alg X)
    ( λ f H →
      Id ( ap ( structure-algebra-polynomial-endofunctor X)
              ( htpy-polynomial-endofunctor A B H (pair x α)))
         ( ap ( λ t → structure-algebra-polynomial-endofunctor X (pair x t))
              ( eq-htpy (H ·r α))))
    ( ap ( ap (pr2 X))
         ( coh-refl-htpy-polynomial-endofunctor A B
           ( map-hom-𝕎-Alg X)
           ( pair x α)) ∙
    ( inv
      ( ap ( ap (λ t → pr2 X (pair x t)))
           ( eq-htpy-refl-htpy (map-hom-𝕎-Alg X ∘ α)))))

structure-htpy-hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B) →
  (f : hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X) →
  ( structure-hom-𝕎-Alg X ∙h
    ( ( structure-algebra-polynomial-endofunctor X) ·l
      ( htpy-polynomial-endofunctor A B (htpy-htpy-hom-𝕎-Alg X f)))) ~
  ( ( (htpy-htpy-hom-𝕎-Alg X f) ·r structure-𝕎-Alg {B = B}) ∙h
    ( structure-hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X f))
structure-htpy-hom-𝕎-Alg {A = A} {B} X (pair f μ-f) (pair x α) =
  ( ( ( compute-structure-htpy-hom-𝕎-Alg X x α
        ( htpy-htpy-hom-𝕎-Alg X (pair f μ-f)))  ∙
      ( inv right-unit)) ∙
    ( ap ( concat
           ( ap
             ( λ t → pr2 X (pair x t))
             ( eq-htpy (htpy-htpy-hom-𝕎-Alg X (pair f μ-f) ·r α)))
         ( pr2 X (map-polynomial-endofunctor A B f (pair x α))))
         ( inv (left-inv ( μ-f (pair x α)))))) ∙
  ( inv
    ( assoc
      ( ap ( λ t → pr2 X (pair x t))
           ( eq-htpy (htpy-htpy-hom-𝕎-Alg X (pair f μ-f) ·r α)))
      ( inv (μ-f (pair x α)))
      ( μ-f (pair x α))))

htpy-hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B) →
  (f : hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X) →
  htpy-hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X (hom-𝕎-Alg X) f
htpy-hom-𝕎-Alg X f =
  pair (htpy-htpy-hom-𝕎-Alg X f) (structure-htpy-hom-𝕎-Alg X f)

is-initial-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B) →
  is-contr (hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X)
is-initial-𝕎-Alg {A = A} {B} X =
  pair
    ( hom-𝕎-Alg X)
    ( λ f →
      eq-htpy-hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X (hom-𝕎-Alg X) f
        ( htpy-hom-𝕎-Alg X f))

--------------------------------------------------------------------------------

-- Section B.4 Functoriality of 𝕎

map-𝕎' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A → C) (g : (x : A) → D (f x) → B x) →
  𝕎 A B → 𝕎 C D
map-𝕎' D f g (collect-𝕎 a α) = collect-𝕎 (f a) (map-𝕎' D f g ∘ (α ∘ g a))

map-𝕎 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A → C) (e : (x : A) → B x ≃ D (f x)) →
  𝕎 A B → 𝕎 C D
map-𝕎 D f e = map-𝕎' D f (λ x → map-inv-equiv (e x))

fib-map-𝕎 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A → C) (e : (x : A) → B x ≃ D (f x)) →
  𝕎 C D → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
fib-map-𝕎 D f e (collect-𝕎 c γ) =
  (fib f c) × ((d : D c) → fib (map-𝕎 D f e) (γ d))

abstract
  equiv-fib-map-𝕎 :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3}
    (D : C → UU l4) (f : A → C) (e : (x : A) → B x ≃ D (f x)) →
    (y : 𝕎 C D) → fib (map-𝕎 D f e) y ≃ fib-map-𝕎 D f e y
  equiv-fib-map-𝕎 {A = A} {B} {C} D f e (collect-𝕎 c γ) =
    ( ( ( inv-equiv
          ( assoc-Σ A
            ( λ a → Id (f a) c)
            ( λ t → (d : D c) → fib (map-𝕎 D f e) (γ d)))) ∘e
        ( equiv-tot
          ( λ a →
            ( ( equiv-tot
                ( λ p →
                  ( ( equiv-Π
                      ( λ (d : D c) → fib (map-𝕎 D f e) (γ d))
                      ( (equiv-tr D p) ∘e (e a))
                      ( λ b → equiv-id)) ∘e
                    ( equiv-inv-choice-∞
                      ( λ b w →
                        Id ( map-𝕎 D f e w)
                           ( γ (tr D p (map-equiv (e a) b)))))) ∘e 
                  ( equiv-tot
                    ( λ α →
                      equiv-Π
                        ( λ (b : B a) →
                          Id ( map-𝕎 D f e (α b))
                             ( γ (tr D p (map-equiv (e a) b))))
                        ( inv-equiv (e a))
                        ( λ d →
                          ( equiv-concat'
                            ( map-𝕎 D f e
                              ( α (map-inv-equiv (e a) d)))
                            ( ap ( γ ∘ (tr D p))
                                 ( inv (issec-map-inv-equiv (e a) d)))) ∘e
                          ( inv-equiv
                            ( equiv-Eq-𝕎-eq
                              ( map-𝕎 D f e
                                ( α (map-inv-equiv (e a) d)))
                              ( γ (tr D p d))))))))) ∘e
              ( equiv-Σ-swap
                ( B a → 𝕎 A B)
                ( Id (f a) c)
                ( λ α p →
                  ( x : D (f a)) →
                  Eq-𝕎
                    ( map-𝕎 D f e (α (map-inv-equiv (e a) x)))
                    ( γ (tr D p x))))) ∘e
            ( equiv-tot
              ( λ α →
                equiv-Eq-𝕎-eq
                  ( collect-𝕎
                    ( f a)
                    ( ( map-𝕎 D f e) ∘
                      ( α ∘ map-inv-equiv (e a)))) (collect-𝕎 c γ)))))) ∘e
      ( assoc-Σ A
        ( λ a → B a → 𝕎 A B)
        ( λ t →
          Id (map-𝕎 D f e (structure-𝕎-Alg t)) (collect-𝕎 c γ)))) ∘e
    ( equiv-Σ
      ( λ t → Id (map-𝕎 D f e (structure-𝕎-Alg t)) (collect-𝕎 c γ))
      ( inv-equiv-structure-𝕎-Alg)
      ( λ x →
        equiv-concat
          ( ap (map-𝕎 D f e) (issec-map-inv-structure-𝕎-Alg x))
          ( collect-𝕎 c γ)))

is-trunc-map-map-𝕎 :
  {l1 l2 l3 l4 : Level} (k : 𝕋)
  {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A → C) (e : (x : A) → B x ≃ D (f x)) →
  is-trunc-map k f → is-trunc-map k (map-𝕎 D f e)
is-trunc-map-map-𝕎 k D f e H (collect-𝕎 c γ) =
  is-trunc-equiv k
    ( fib-map-𝕎 D f e (collect-𝕎 c γ))
    ( equiv-fib-map-𝕎 D f e (collect-𝕎 c γ))
    ( is-trunc-Σ k
      ( H c)
      ( λ t → is-trunc-Π k (λ d → is-trunc-map-map-𝕎 k D f e H (γ d))))

is-equiv-map-𝕎 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A → C) (e : (x : A) → B x ≃ D (f x)) →
  is-equiv f → is-equiv (map-𝕎 D f e)
is-equiv-map-𝕎 D f e H =
  is-equiv-is-contr-map
    ( is-trunc-map-map-𝕎 neg-two-𝕋 D f e (is-contr-map-is-equiv H))

equiv-𝕎 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A ≃ C) (e : (x : A) → B x ≃ D (map-equiv f x)) →
  𝕎 A B ≃ 𝕎 C D
equiv-𝕎 D f e =
  pair
    ( map-𝕎 D (map-equiv f) e)
    ( is-equiv-map-𝕎 D (map-equiv f) e (is-equiv-map-equiv f))

is-emb-map-𝕎 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A → C) (e : (x : A) → B x ≃ D (f x)) →
  is-emb f → is-emb (map-𝕎 D f e)
is-emb-map-𝕎 D f e H =
  is-emb-is-prop-map
    (is-trunc-map-map-𝕎 neg-one-𝕋 D f e (is-prop-map-is-emb H))

emb-𝕎 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A ↪ C) (e : (x : A) → B x ≃ D (map-emb f x)) → 𝕎 A B ↪ 𝕎 C D
emb-𝕎 D f e =
  pair
    ( map-𝕎 D (map-emb f) e)
    ( is-emb-map-𝕎 D (map-emb f) e (is-emb-map-emb f))

--------------------------------------------------------------------------------

-- Section B.5 Indexed W-types

data i𝕎 {l1 l2 l3 : Level} (I : UU l1) (A : I → UU l2) (B : (i : I) → A i → UU l3) (f : (i : I) (x : A i) → B i x → I) (i : I) : UU (l2 ⊔ l3) where
  sup-i𝕎 : (x : A i) (α : (y : B i x) → i𝕎 I A B f (f i x y)) → i𝕎 I A B f i

--------------------------------------------------------------------------------

-- Section B.6 Russel's paradox in type theory

-- Definition B.6.1

_∈-𝕎_ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
x ∈-𝕎 y = fib (component-𝕎 y) x

extensional-Eq-eq-𝕎 : 
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {x y : 𝕎 A B} →
  Id x y → (z : 𝕎 A B) → (z ∈-𝕎 y) ≃ (z ∈-𝕎 y)
extensional-Eq-eq-𝕎 refl z = equiv-id

is-extensional-𝕎 :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) → UU (l1 ⊔ l2)
is-extensional-𝕎 A B =
  (x y : 𝕎 A B) → is-equiv (extensional-Eq-eq-𝕎 {x = x} {y})

-- Theorem B.6.2

is-univalent :
  {l1 l2 : Level} {A : UU l1} → (A → UU l2) → UU (l1 ⊔ l2)
is-univalent {A = A} B = (x y : A) → is-equiv (λ (p : Id x y) → equiv-tr B p)

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

{-
  is-extensional-is-univalent-𝕎 :
    is-univalent B → is-extensional-𝕎 A B
  is-extensional-is-univalent-𝕎 H x =
    fundamental-theorem-id x
      ( λ z → equiv-id)
      ( is-contr-equiv
        ( Σ ( type-polynomial-endofunctor A B (𝕎 A B))
            ( λ t → {!!}))
        {!!}
        {!!})
      ( λ y → extensional-Eq-eq-𝕎)
-}

𝕎-UU : (l : Level) → UU (lsuc l)
𝕎-UU l = 𝕎 (UU l) (λ X → X)

raise-𝕎-UU : (l : Level) {l1 : Level} → 𝕎-UU l1 → 𝕎-UU (l1 ⊔ l)
raise-𝕎-UU l = map-𝕎 id (raise l) (equiv-raise l)

is-small-𝕎-UU :
  (l : Level) {l1 : Level} → 𝕎-UU l1 → UU (l1 ⊔ lsuc l)
is-small-𝕎-UU l (collect-𝕎 A α) =
  is-small l A × ((x : A) → is-small-𝕎-UU l (α x))

arity-resize-𝕎-UU :
  {l l1 : Level} (X : 𝕎-UU l1) → is-small-𝕎-UU l X → UU l
arity-resize-𝕎-UU (collect-𝕎 A α) (pair (pair A' e) H) = A'

equiv-arity-resize-𝕎-UU :
  {l l1 : Level} (X : 𝕎-UU l1) (H : is-small-𝕎-UU l X) →
  arity-𝕎 X ≃ arity-resize-𝕎-UU X H
equiv-arity-resize-𝕎-UU (collect-𝕎 A α) (pair (pair A' e) H) = e

resize-𝕎-UU :
  {l1 l2 : Level} (X : 𝕎-UU l1) → is-small-𝕎-UU l2 X → 𝕎-UU l2
resize-𝕎-UU (collect-𝕎 A α) (pair (pair A' e) H2) =
  collect-𝕎 A'
    ( λ x' → resize-𝕎-UU (α (map-inv-equiv e x')) (H2 (map-inv-equiv e x')))

-- The componenthood relation on 𝕎-UU l is valued in 𝕎-UU (lsuc l)

_∈-𝕎-UU_ : {l : Level} → 𝕎-UU l → 𝕎-UU l → UU (lsuc l)
_∈-𝕎-UU_ {l} X (collect-𝕎 A α) = fib α X

-- The condition that an component of 𝕎-UU l is empty

is-empty-𝕎-UU : {l : Level} (X : 𝕎-UU l) → UU l
is-empty-𝕎-UU (collect-𝕎 A α) = is-empty A

-- The condition that an component of 𝕎-UU l has no components

_∉-𝕎-UU_ : {l : Level} → 𝕎-UU l → 𝕎-UU l → UU (lsuc l)
X ∉-𝕎-UU Y = is-empty (X ∈-𝕎-UU Y)

has-no-components-𝕎-UU :
  {l : Level} (X : 𝕎-UU l) → UU (lsuc l)
has-no-components-𝕎-UU {l} X = (Y : 𝕎-UU l) → (Y ∉-𝕎-UU X)

-- An object X of 𝕎-UU l is empty if and only if it has no components

is-empty-has-no-components-𝕎-UU :
  {l : Level} (X : 𝕎-UU l) → has-no-components-𝕎-UU X → is-empty-𝕎-UU X
is-empty-has-no-components-𝕎-UU (collect-𝕎 A α) H a =
  H (α a) (pair a refl)

has-no-components-is-empty-𝕎-UU :
  {l : Level} (X : 𝕎-UU l) → is-empty-𝕎-UU X → has-no-components-𝕎-UU X
has-no-components-is-empty-𝕎-UU (collect-𝕎 A α) H (collect-𝕎 B β) t = H (pr1 t)

fam-𝕎-UU :
  (l : Level) {l1 : Level} (X : 𝕎-UU l1) → UU (l1 ⊔ lsuc l)
fam-𝕎-UU l (collect-𝕎 A α) = A → 𝕎-UU l

flatten-𝕎-UU : {l : Level} → 𝕎-UU l → 𝕎-UU l
flatten-𝕎-UU {l} (collect-𝕎 A α) =
  collect-𝕎
    ( Σ A (λ x → arity-𝕎 (α x)))
    ( ind-Σ (λ x → component-𝕎 (α x)))

subtree-𝕎-UU :
  {l : Level} (X : 𝕎-UU l) → (P : arity-𝕎 X → UU-Prop l) → 𝕎-UU l
subtree-𝕎-UU X P =
  collect-𝕎 (Σ (arity-𝕎 X) (λ x → type-Prop (P x))) ((component-𝕎 X) ∘ pr1)

tree-of-trees-𝕎-UU :
  (l : Level) → 𝕎-UU (lsuc l)
tree-of-trees-𝕎-UU l = collect-𝕎 (𝕎-UU l) (raise-𝕎-UU (lsuc l))

Russell : (l : Level) → 𝕎-UU (lsuc l)
Russell l =
  subtree-𝕎-UU
    ( tree-of-trees-𝕎-UU l)
    ( λ X → neg-Prop' (X ∈-𝕎-UU X))

is-small-universe :
  (l l1 : Level) → UU (lsuc l1 ⊔ lsuc l)
is-small-universe l l1 = is-small l (UU l1) × ((X : UU l1) → is-small l X)

is-small-tree-of-trees-𝕎-UU :
  (l : Level) {l1 : Level} →
  is-small-universe l l1 → is-small-𝕎-UU l (tree-of-trees-𝕎-UU l1)
is-small-tree-of-trees-𝕎-UU l (pair (pair U e) H) =
  pair
    ( pair
      ( 𝕎 U (λ x → pr1 (H (map-inv-equiv e x))))
      {! equiv-𝕎!})
    {!!}

paradox-Russell : {l : Level} → ¬ (is-small l (UU l))
paradox-Russell (pair A e) = {!!}

--------------------------------------------------------------------------------

-- Exercises

_∉-𝕎_ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
x ∉-𝕎 y = is-empty (x ∈-𝕎 y)

irreflexive-∈-𝕎 :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (x : 𝕎 A B) → x ∉-𝕎 x
irreflexive-∈-𝕎 {A = A} {B = B} (collect-𝕎 x α) (pair y p) =
  irreflexive-∈-𝕎 (α y) (tr (λ z → (α y) ∈-𝕎 z) (inv p) (pair y refl))

-- Exercise B.7

-- Exercise B.7 (a)

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  -- We define the strict ordering on 𝕎 A B
  
  data _le-𝕎_ (x : 𝕎 A B) : 𝕎 A B → UU (l1 ⊔ l2) where
    le-∈-𝕎 : {y : 𝕎 A B} → x ∈-𝕎 y → x le-𝕎 y
    propagate-le-𝕎 : {y z : 𝕎 A B} → y ∈-𝕎 z → x le-𝕎 y → x le-𝕎 z

  -- The strict ordering is transitive, irreflexive, and asymmetric
  
  transitive-le-𝕎 : {x y z : 𝕎 A B} → y le-𝕎 z → x le-𝕎 y → x le-𝕎 z
  transitive-le-𝕎 {x = x} {y} {z} (le-∈-𝕎 H) K =
    propagate-le-𝕎 H K
  transitive-le-𝕎 {x = x} {y} {z} (propagate-le-𝕎 L H) K =
    propagate-le-𝕎 L (transitive-le-𝕎 H K)

  irreflexive-le-𝕎 :
    {x : 𝕎 A B} → ¬ (x le-𝕎 x)
  irreflexive-le-𝕎 {x = x} (le-∈-𝕎 H) = irreflexive-∈-𝕎 x H
  irreflexive-le-𝕎 {x = collect-𝕎 x α} (propagate-le-𝕎 (pair b refl) H) =
    irreflexive-le-𝕎 {x = α b} (transitive-le-𝕎 H (le-∈-𝕎 (pair b refl)))

  asymmetric-le-𝕎 :
    {x y : 𝕎 A B} → x le-𝕎 y → y le-𝕎 x → empty
  asymmetric-le-𝕎 H K = irreflexive-le-𝕎 (transitive-le-𝕎 H K)

-- Exercise B.7 (b)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  where
  
  -- We define an operation □-𝕎 that acts on families over 𝕎 A B.

  □-𝕎 : (𝕎 A B → UU l3) → 𝕎 A B → UU (l1 ⊔ l2 ⊔ l3)
  □-𝕎 P x = (y : 𝕎 A B) → (y le-𝕎 x) → P y

  variable
    P : 𝕎 A B → UU l3

  -- The unit of □-𝕎 takes sections of P to sections of □-𝕎 P

  unit-□-𝕎 :
    ((x : 𝕎 A B) → P x) → ((x : 𝕎 A B) → □-𝕎 P x)
  unit-□-𝕎 f x y p = f y

  -- The reflector (counit) of □-𝕎 is dual, with an extra hypothesis

  reflect-□-𝕎 :
    ((x : 𝕎 A B) → □-𝕎 P x → P x) →
    ((x : 𝕎 A B) → □-𝕎 P x) → ((x : 𝕎 A B) → P x)
  reflect-□-𝕎 h f x = h x (f x)

  {- We first prove an intermediate induction principle with computation rule,
     where we obtain sections of □-𝕎 P. -}

  □-strong-ind-𝕎 :
    ((x : 𝕎 A B) → □-𝕎 P x → P x) → (x : 𝕎 A B) → □-𝕎 P x
  □-strong-ind-𝕎 h (collect-𝕎 x α) .(α b) (le-∈-𝕎 (pair b refl)) =
    h (α b) (□-strong-ind-𝕎 h (α b))
  □-strong-ind-𝕎 h (collect-𝕎 x α) y (propagate-le-𝕎 (pair b refl) K) =
    □-strong-ind-𝕎 h (α b) y K

  □-strong-comp-𝕎 :
    (h : (x : 𝕎 A B) → □-𝕎 P x → P x)
    (x : 𝕎 A B) (y : 𝕎 A B) (p : y le-𝕎 x) →
    Id (□-strong-ind-𝕎 h x y p) (h y (□-strong-ind-𝕎 h y))
  □-strong-comp-𝕎 h (collect-𝕎 x α) .(α b) (le-∈-𝕎 (pair b refl)) =
    refl
  □-strong-comp-𝕎 h (collect-𝕎 x α) y (propagate-le-𝕎 (pair b refl) K) =
    □-strong-comp-𝕎 h (α b) y K

{- Now we prove the actual induction principle with computation rule, where we
   obtain sections of P. -}

strong-ind-𝕎 :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (P : 𝕎 A B → UU l3) → 
  ((x : 𝕎 A B) → □-𝕎 P x → P x) → (x : 𝕎 A B) → P x
strong-ind-𝕎 P h = reflect-□-𝕎 h (□-strong-ind-𝕎 h)
                                               
strong-comp-𝕎 :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (P : 𝕎 A B → UU l3) →
  (h : (x : 𝕎 A B) → □-𝕎 P x → P x) (x : 𝕎 A B) →
  Id (strong-ind-𝕎 P h x) (h x (unit-□-𝕎 (strong-ind-𝕎 P h) x))
strong-comp-𝕎 P h x =
  ap (h x) (eq-htpy (λ y → eq-htpy (λ p → □-strong-comp-𝕎 h x y p)))

-- Exercise B.7 (c)

no-infinite-descent-𝕎 :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (f : ℕ → 𝕎 A B) → ¬ ((n : ℕ) → (f (succ-ℕ n) le-𝕎 (f n)))
no-infinite-descent-𝕎 {A = A} {B} f =
  strong-ind-𝕎
    ( λ x → (f : ℕ → 𝕎 A B) (p : Id (f zero-ℕ) x) →
            ¬ ((n : ℕ) → (f (succ-ℕ n)) le-𝕎 (f n)))
    ( λ x IH f p H →
      IH ( f one-ℕ)
         ( tr (λ t → (f one-ℕ) le-𝕎 t) p (H zero-ℕ))
         ( f ∘ succ-ℕ)
         ( refl)
         ( λ n → H (succ-ℕ n)))
    ( f zero-ℕ)
    ( f)
    ( refl)

-- Exercise B.8

-- Exercise B.9

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  _≲-𝕎-Prop_ : 𝕎 A B → 𝕎 A B → UU-Prop (l1 ⊔ l2)
  (collect-𝕎 x α) ≲-𝕎-Prop (collect-𝕎 y β) =
    Π-Prop (B x) (λ b → exists-Prop (λ c → (α b) ≲-𝕎-Prop (β c)))

  _≲-𝕎_ : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  x ≲-𝕎 y = type-Prop (x ≲-𝕎-Prop y)

  refl-≲-𝕎 : (x : 𝕎 A B) → x ≲-𝕎 x
  refl-≲-𝕎 (collect-𝕎 x α) b = unit-trunc-Prop (pair b (refl-≲-𝕎 (α b)))

  transitive-≲-𝕎 : {x y z : 𝕎 A B} → (x ≲-𝕎 y) → (y ≲-𝕎 z) → (x ≲-𝕎 z)
  transitive-≲-𝕎 {collect-𝕎 x α} {collect-𝕎 y β} {collect-𝕎 z γ} H K a =
    apply-universal-property-trunc-Prop
      ( H a)
      ( exists-Prop (λ c → (α a) ≲-𝕎-Prop (γ c)))
      ( λ t →
        apply-universal-property-trunc-Prop
          ( K (pr1 t))
          ( exists-Prop (λ c → (α a) ≲-𝕎-Prop (γ c)))
          ( λ s →
            unit-trunc-Prop
              ( pair
                ( pr1 s)
                ( transitive-≲-𝕎
                  { α a}
                  { β (pr1 t)}
                  { γ (pr1 s)}
                  ( pr2 t)
                  ( pr2 s)))))

  is-least-constant-≲-𝕎 :
    {x : A} (h : is-empty (B x)) (w : 𝕎 A B) → constant-𝕎 x h ≲-𝕎 w
  is-least-constant-≲-𝕎 h (collect-𝕎 y β) x = ex-falso (h x)

  not-has-lower-rank-is-element-𝕎 :
    {x y : 𝕎 A B} → x ∈-𝕎 y → ¬ (y ≲-𝕎 x)
  not-has-lower-rank-is-element-𝕎 {.(α x)} {collect-𝕎 y α} (pair x refl) K  =
    {!!}
    where
    K' = tr (λ t → collect-𝕎 y α ≲-𝕎 t) (inv (η-𝕎 (α x))) K

  _≈-𝕎-Prop_ : 𝕎 A B → 𝕎 A B → UU-Prop (l1 ⊔ l2)
  x ≈-𝕎-Prop y = prod-Prop (x ≲-𝕎-Prop y) (y ≲-𝕎-Prop x)

  _≈-𝕎_ : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  x ≈-𝕎 y = type-Prop (x ≈-𝕎-Prop y)

--------------------------------------------------------------------------------

data _leq-𝕎_ {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (x : 𝕎 A B) :
  𝕎 A B → UU (l1 ⊔ l2) where
  refl-leq-𝕎 : x leq-𝕎 x
  propagate-leq-𝕎 : {y z : 𝕎 A B} → y ∈-𝕎 z → x leq-𝕎 y → x leq-𝕎 z
